use thin_vec::ThinVec;

use crate::ast::{Ident, Mutability};
use crate::hir::{self, PrimTy, QPath, UnOp};
use crate::hir::{BinOp, HirId};
use crate::resolve::Res;
use crate::span::Span;
use crate::thir::scope::{Scope, ScopeKind, ScopeTree};
use crate::thir::*;
use crate::typeck::{Adjustment, Ty, TyVarId, TypeckOutputs};

use fxhash::FxHashMap;

pub fn lower_body(
    body: &hir::Body,
    inputs: &ThinVec<hir::Ty>,
    typeck: &TypeckOutputs,
    scope_tree: Option<&ScopeTree>,
) -> ThirBody {
    let mut lowerer = ThirLowerer::new(typeck, scope_tree);
    for (param, input) in body.params.iter().zip(inputs.iter()) {
        let local_var = LocalVarId(lowerer.locals.len() as u32);
        lowerer.locals.insert(param.hir_id, local_var);
        lowerer.params.push(Param {
            name: param.name,
            ty: hir_ty_to_ty(input, &typeck.hir_id_to_ty_var),
            hir_id: param.hir_id,
            local_var,
        });
    }
    let body_expr = lowerer.lower_expr(&body.value);
    ThirBody {
        exprs: lowerer.exprs,
        stmts: lowerer.stmts,
        blocks: lowerer.blocks,
        params: lowerer.params,
        locals: lowerer.locals,
        body_expr,
    }
}

struct ThirLowerer<'a> {
    typeck: &'a TypeckOutputs,
    scope_tree: Option<&'a ScopeTree>,
    exprs: Vec<Expr>,
    stmts: Vec<Stmt>,
    blocks: Vec<Block>,
    params: Vec<Param>,
    locals: FxHashMap<HirId, LocalVarId>,
}

impl<'a> ThirLowerer<'a> {
    fn new(typeck: &'a TypeckOutputs, scope_tree: Option<&'a ScopeTree>) -> Self {
        Self {
            typeck,
            scope_tree,
            exprs: Vec::new(),
            stmts: Vec::new(),
            blocks: Vec::new(),
            params: Vec::new(),
            locals: FxHashMap::default(),
        }
    }

    fn alloc_expr(&mut self, kind: ExprKind, ty: Ty, span: Span, hir_id: HirId) -> ExprId {
        let id = ExprId(self.exprs.len() as u32);
        self.exprs.push(Expr {
            kind,
            ty,
            span,
            hir_id,
            temp_scope: None,
        });
        id
    }

    fn alloc_stmt(&mut self, kind: StmtKind, span: Span, hir_id: HirId) -> StmtId {
        let id = StmtId(self.stmts.len() as u32);
        self.stmts.push(Stmt { kind, span, hir_id });
        id
    }

    fn alloc_block(&mut self, block: Block) -> BlockId {
        let id = BlockId(self.blocks.len() as u32);
        self.blocks.push(block);
        id
    }

    fn lookup_ty(&self, hir_id: HirId) -> Ty {
        self.typeck
            .node_types
            .get(&hir_id)
            .expect("type exists")
            .clone()
    }

    fn lower_expr(&mut self, expr: &hir::Expr) -> ExprId {
        let hir_id = expr.hir_id;
        let span = expr.span;
        let ty = self.lookup_ty(hir_id);
        let inner = self.lower_expr_kind(&expr.kind, hir_id, span, &ty);
        let adjusted = self.apply_adjustments(inner, hir_id, span);
        let region_scope = Scope::new(hir_id.local_id, ScopeKind::Node);
        self.alloc_expr(
            ExprKind::Scope {
                region_scope,
                value: adjusted,
            },
            ty,
            span,
            hir_id,
        )
    }

    fn apply_adjustments(&mut self, mut inner: ExprId, hir_id: HirId, span: Span) -> ExprId {
        let Some(adjustments) = self.typeck.adjustments.get(&hir_id) else {
            return inner;
        };
        let mut current_ty = self.lookup_ty(hir_id);
        for adjustment in adjustments.iter().rev() {
            current_ty = match current_ty {
                Ty::Error => Ty::Error,
                ty => match adjustment {
                    Adjustment::AutoRef(m) => Ty::Ptr(Box::new(ty), *m),
                    Adjustment::AutoDeref => match ty {
                        Ty::Ptr(inner_ty, _) => *inner_ty,
                        _ => Ty::Error,
                    },
                },
            };
            inner = match adjustment {
                Adjustment::AutoRef(m) => self.alloc_expr(
                    ExprKind::Borrow {
                        kind: *m,
                        arg: inner,
                    },
                    current_ty.clone(),
                    span,
                    hir_id,
                ),
                Adjustment::AutoDeref => self.alloc_expr(
                    ExprKind::Deref { arg: inner },
                    current_ty.clone(),
                    span,
                    hir_id,
                ),
            };
        }
        inner
    }

    fn lower_expr_kind(
        &mut self,
        kind: &hir::ExprKind,
        hir_id: HirId,
        span: Span,
        ty: &Ty,
    ) -> ExprId {
        match kind {
            hir::ExprKind::Literal(lit) => {
                self.alloc_expr(ExprKind::Literal(*lit), ty.clone(), span, hir_id)
            }
            hir::ExprKind::Path(qpath) => self.lower_path(qpath, ty, span, hir_id),
            hir::ExprKind::Binary { left, op, right } => {
                self.lower_binary(left, *op, right, ty, span, hir_id)
            }
            hir::ExprKind::Assign { target, value } => {
                self.lower_assign(target, value, ty, span, hir_id)
            }
            hir::ExprKind::Unary { op, right } => self.lower_prefix(*op, right, ty, span, hir_id),
            hir::ExprKind::Dereference { expr } => self.lower_dereference(expr, ty, span, hir_id),
            hir::ExprKind::Reference { expr, mutability } => {
                self.lower_reference(expr, *mutability, ty, span, hir_id)
            }
            hir::ExprKind::Call { callee, args } => self.lower_call(callee, args, ty, span, hir_id),
            hir::ExprKind::MethodCall {
                receiver,
                args,
                def_id,
                ..
            } => self.lower_method_call(receiver, args, *def_id, ty, span, hir_id),
            hir::ExprKind::Field { base, index, .. } => {
                self.lower_field(base, *index, ty, span, hir_id)
            }
            hir::ExprKind::Index { base, index } => self.lower_index(base, index, ty, span, hir_id),
            hir::ExprKind::StructInit { def, fields, .. } => {
                self.lower_struct_init(fields, *def, ty, span, hir_id)
            }
            hir::ExprKind::ArrayInit { contents, .. } => {
                self.lower_array_init(contents, ty, span, hir_id)
            }
            hir::ExprKind::TupleInit(contents) => self.lower_tuple_init(contents, ty, span, hir_id),
            hir::ExprKind::Block(block) => self.lower_block_expr(block),
            hir::ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => self.lower_if(cond, then_branch, else_branch.as_deref(), ty, span, hir_id),
            hir::ExprKind::Loop(block) => self.lower_loop(block, ty, span, hir_id),
            hir::ExprKind::Break(value) => self.lower_break(value.as_deref(), ty, span, hir_id),
            hir::ExprKind::Return(value) => self.lower_return(value.as_deref(), ty, span, hir_id),
            hir::ExprKind::As { expr, ty } => self.lower_cast(expr, ty, span, hir_id),
            hir::ExprKind::MemberAccess { .. } | hir::ExprKind::Error => unreachable!(),
        }
    }

    fn lower_cast(
        &mut self,
        expr: &hir::Expr,
        target: &hir::Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let source = self.lower_expr(expr);
        let target_ty = hir_ty_to_ty(target, &self.typeck.hir_id_to_ty_var);
        self.alloc_expr(
            ExprKind::Cast {
                source,
                target_ty: target_ty.clone(),
            },
            target_ty,
            span,
            hir_id,
        )
    }

    fn lower_return(
        &mut self,
        value: Option<&hir::Expr>,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let value = value.map(|expr| self.lower_expr(expr));
        self.alloc_expr(ExprKind::Return { value }, ty.clone(), span, hir_id)
    }

    fn lower_break(
        &mut self,
        value: Option<&hir::Expr>,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let value = value.map(|expr| self.lower_expr(expr));
        self.alloc_expr(ExprKind::Break { value }, ty.clone(), span, hir_id)
    }

    fn lower_loop(&mut self, block: &hir::Block, ty: &Ty, span: Span, hir_id: HirId) -> ExprId {
        let body = self.lower_block_expr(block);
        self.alloc_expr(ExprKind::Loop { body }, ty.clone(), span, hir_id)
    }

    fn lower_if(
        &mut self,
        cond: &hir::Expr,
        then_branch: &hir::Block,
        else_branch: Option<&hir::Expr>,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let cond_id = self.lower_expr(cond);
        let then_id = self.lower_block_expr(then_branch);
        let else_id = else_branch.map(|expr| {
            assert!(matches!(
                expr.kind,
                hir::ExprKind::Block(_) | hir::ExprKind::If { .. }
            ));
            self.lower_expr(expr)
        });
        self.alloc_expr(
            ExprKind::If {
                cond: cond_id,
                then: then_id,
                else_opt: else_id,
            },
            ty.clone(),
            span,
            hir_id,
        )
    }

    fn lower_block_expr(&mut self, block: &hir::Block) -> ExprId {
        let block_id = self.lower_block(block);
        let ty = block
            .tail
            .as_ref()
            .map(|tail| self.lookup_ty(tail.hir_id))
            .unwrap_or_else(|| Ty::Prim(PrimTy::Void));
        self.alloc_expr(ExprKind::Block(block_id), ty, block.span, block.hir_id)
    }

    fn lower_block(&mut self, block: &hir::Block) -> BlockId {
        let mut stmt_ids = ThinVec::with_capacity(block.stmts.len());

        for stmt in block.stmts.iter() {
            match &stmt.kind {
                hir::StmtKind::Expr(expr) => {
                    let expr_id = self.lower_expr(expr);
                    let stmt_id =
                        self.alloc_stmt(StmtKind::Expr { expr: expr_id }, stmt.span, stmt.hir_id);
                    stmt_ids.push(stmt_id);
                }
                hir::StmtKind::Let {
                    name,
                    ty,
                    init,
                    local,
                    ..
                } => {
                    let init_id = init.as_ref().map(|expr| self.lower_expr(expr));
                    let local_var = LocalVarId(self.locals.len() as u32);
                    self.locals.insert(*local, local_var);
                    let ty = if matches!(ty.kind, hir::TyKind::Infer) {
                        init.as_ref()
                            .and_then(|expr| self.typeck.node_types.get(&expr.hir_id))
                            .cloned()
                            .unwrap_or(Ty::Error)
                    } else {
                        hir_ty_to_ty(ty, &self.typeck.hir_id_to_ty_var)
                    };
                    let remainder_scope = self
                        .scope_tree
                        .expect("has scope tree")
                        .var_scope(local.local_id);
                    let stmt_id = self.alloc_stmt(
                        StmtKind::Let {
                            ty,
                            local_var,
                            remainder_scope,
                            name: *name,
                            init: init_id,
                            init_scope: None,
                        },
                        stmt.span,
                        stmt.hir_id,
                    );
                    stmt_ids.push(stmt_id);
                }
            }
        }

        let tail = block.tail.as_ref().map(|tail| self.lower_expr(tail));

        let region_scope = Scope::new(block.hir_id.local_id, ScopeKind::Node);
        self.alloc_block(Block {
            region_scope,
            stmts: stmt_ids,
            tail,
        })
    }

    fn lower_tuple_init(
        &mut self,
        contents: &ThinVec<hir::Expr>,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let elements: ThinVec<ExprId> = contents.iter().map(|expr| self.lower_expr(expr)).collect();
        self.alloc_expr(ExprKind::TupleInit(elements), ty.clone(), span, hir_id)
    }

    fn lower_array_init(
        &mut self,
        contents: &ThinVec<hir::Expr>,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let elements: ThinVec<ExprId> = contents.iter().map(|expr| self.lower_expr(expr)).collect();
        self.alloc_expr(ExprKind::ArrayInit { elements }, ty.clone(), span, hir_id)
    }

    fn lower_struct_init(
        &mut self,
        fields: &ThinVec<(Ident, hir::Expr)>,
        def_id: DefId,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let struct_field_info = self
            .typeck
            .coherence
            .struct_fields
            .get(&def_id)
            .expect("struct exists");

        let mut ordered = vec![None; struct_field_info.len()];

        for (ident, expr) in fields {
            let &(_, idx) = struct_field_info.get(&ident.value).expect("field exists");
            ordered[idx] = Some((ident.value, self.lower_expr(expr)));
        }

        let fields = ordered.into_iter().flatten().collect();

        self.alloc_expr(
            ExprKind::StructInit { def_id, fields },
            ty.clone(),
            span,
            hir_id,
        )
    }

    fn lower_field(
        &mut self,
        base: &hir::Expr,
        index: usize,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let base_id = self.lower_expr(base);
        self.alloc_expr(
            ExprKind::Field {
                base: base_id,
                index,
            },
            ty.clone(),
            span,
            hir_id,
        )
    }

    fn lower_index(
        &mut self,
        base: &hir::Expr,
        index: &hir::Expr,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let base_id = self.lower_expr(base);
        let index_id = self.lower_expr(index);
        self.alloc_expr(
            ExprKind::Index {
                base: base_id,
                index: index_id,
            },
            ty.clone(),
            span,
            hir_id,
        )
    }

    fn lower_method_call(
        &mut self,
        receiver: &hir::Expr,
        args: &ThinVec<hir::Expr>,
        def_id: DefId,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let recv_id = self.lower_expr(receiver);
        let mut new_args = ThinVec::with_capacity(1 + args.len());
        new_args.push(recv_id);
        new_args.extend(args.iter().map(|arg| self.lower_expr(arg)));
        let path_id = self.alloc_expr(ExprKind::Path { def_id }, Ty::MethodCallee, span, hir_id);
        self.alloc_expr(
            ExprKind::Call {
                callee: path_id,
                args: new_args,
            },
            ty.clone(),
            span,
            hir_id,
        )
    }

    fn lower_call(
        &mut self,
        callee: &hir::Expr,
        args: &ThinVec<hir::Expr>,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let callee = self.lower_expr(callee);
        let args: ThinVec<ExprId> = args.iter().map(|arg| self.lower_expr(arg)).collect();
        self.alloc_expr(ExprKind::Call { callee, args }, ty.clone(), span, hir_id)
    }

    fn lower_dereference(
        &mut self,
        expr: &hir::Expr,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let arg = self.lower_expr(expr);
        self.alloc_expr(ExprKind::Deref { arg }, ty.clone(), span, hir_id)
    }

    fn lower_reference(
        &mut self,
        expr: &hir::Expr,
        mutability: Mutability,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let arg = self.lower_expr(expr);
        self.alloc_expr(
            ExprKind::Borrow {
                arg,
                kind: mutability,
            },
            ty.clone(),
            span,
            hir_id,
        )
    }

    fn lower_prefix(
        &mut self,
        op: UnOp,
        right: &hir::Expr,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let arg = self.lower_expr(right);
        self.alloc_expr(ExprKind::Unary { op, arg }, ty.clone(), span, hir_id)
    }

    fn lower_assign(
        &mut self,
        target: &hir::Expr,
        value: &hir::Expr,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let target = self.lower_expr(target);
        let value = self.lower_expr(value);
        self.alloc_expr(ExprKind::Assign { target, value }, ty.clone(), span, hir_id)
    }

    fn lower_binary(
        &mut self,
        left: &hir::Expr,
        op: BinOp,
        right: &hir::Expr,
        ty: &Ty,
        span: Span,
        hir_id: HirId,
    ) -> ExprId {
        let lhs = self.lower_expr(left);
        let rhs = self.lower_expr(right);
        match op {
            BinOp::And => self.alloc_expr(
                ExprKind::LogicalOp {
                    op: LogOp::And,
                    lhs,
                    rhs,
                },
                ty.clone(),
                span,
                hir_id,
            ),
            BinOp::Or => self.alloc_expr(
                ExprKind::LogicalOp {
                    op: LogOp::Or,
                    lhs,
                    rhs,
                },
                ty.clone(),
                span,
                hir_id,
            ),
            _ => self.alloc_expr(ExprKind::Binary { op, lhs, rhs }, ty.clone(), span, hir_id),
        }
    }

    fn lower_path(&mut self, qpath: &QPath, ty: &Ty, span: Span, hir_id: HirId) -> ExprId {
        let QPath::Resolved(path) = qpath else {
            unreachable!();
        };
        match &path.res {
            Res::Local(local) => {
                let local_var = self
                    .locals
                    .get(local)
                    .expect("variable declared before reference");
                self.alloc_expr(ExprKind::VarRef(*local_var), ty.clone(), span, hir_id)
            }
            Res::Def(def_id) => {
                self.alloc_expr(ExprKind::Path { def_id: *def_id }, ty.clone(), span, hir_id)
            }
            _ => unreachable!(),
        }
    }
}

fn hir_ty_to_ty(hir_ty: &hir::Ty, hir_id_to_ty_var: &FxHashMap<HirId, TyVarId>) -> Ty {
    let ty = match &hir_ty.kind {
        hir::TyKind::Error | hir::TyKind::Infer => Ty::Error,
        hir::TyKind::Never => Ty::Never,
        hir::TyKind::PrimTy(prim) => Ty::Prim(*prim),
        hir::TyKind::Ptr(inner, m) => Ty::Ptr(hir_ty_to_ty(inner, hir_id_to_ty_var).into_box(), *m),
        hir::TyKind::Slice(inner) => Ty::Slice(hir_ty_to_ty(inner, hir_id_to_ty_var).into_box()),
        hir::TyKind::Array(inner, size) => {
            Ty::Array(hir_ty_to_ty(inner, hir_id_to_ty_var).into_box(), *size)
        }
        hir::TyKind::Fn { params, ret } => Ty::Fn {
            params: params
                .iter()
                .map(|p| hir_ty_to_ty(p, hir_id_to_ty_var))
                .collect(),
            ret: hir_ty_to_ty(ret, hir_id_to_ty_var).into_box(),
        },
        hir::TyKind::Tuple(elements) => Ty::Tuple(
            elements
                .iter()
                .map(|e| hir_ty_to_ty(e, hir_id_to_ty_var))
                .collect(),
        ),
        hir::TyKind::Path(qpath) => match qpath {
            QPath::Resolved(path) => match &path.res {
                Res::Def(def_id) | Res::SelfTyAlias { alias_to: def_id } => {
                    let generics = path
                        .segments
                        .last()
                        .and_then(|seg| seg.generic_args.as_ref())
                        .as_ref()
                        .map(|args| {
                            args.iter()
                                .map(|arg| hir_ty_to_ty(arg, hir_id_to_ty_var))
                                .collect()
                        });
                    Ty::Adt(*def_id, generics)
                }
                Res::PrimTy(prim) => Ty::Prim(*prim),
                _ => Ty::Error,
            },
            QPath::TypeRelative { .. } => Ty::Error,
        },
        hir::TyKind::GenericParam(hir_id, _) => hir_id_to_ty_var
            .get(hir_id)
            .map(|&ty_var| Ty::Var(ty_var))
            .unwrap_or(Ty::Error),
    };
    assert!(!ty.is_error());
    ty
}
