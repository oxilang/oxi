use thin_vec::ThinVec;

use crate::ast::visit::VisitAction;
use crate::ast::{Literal, Mutability};
use crate::hir::{BinOp, DefId, HirId, UnOp};
use crate::interner::Symbol;
use crate::span::Span;
use crate::thir::scope::Scope;
use crate::typeck::{Ty, TyVarId, TyVisitable, TyVisitor, TypeckOutputs};
use fxhash::{FxHashMap, FxHashSet};

crate::newtype_ids!(ExprId, StmtId, BlockId, LocalVarId);

#[derive(Debug, Clone)]
pub struct ThirBody {
    pub exprs: Vec<Expr>,
    pub stmts: Vec<Stmt>,
    pub blocks: Vec<Block>,
    pub params: Vec<Param>,
    pub locals: FxHashMap<HirId, LocalVarId>,
    pub body_expr: ExprId,
}

#[derive(Debug, Clone)]
pub struct ThirCrate {
    pub bodies: FxHashMap<DefId, ThirBody>,
}

impl ThirCrate {
    pub fn assert_no_free_vars(&self, typeck: &TypeckOutputs) {
        for (&def_id, body) in &self.bodies {
            let mut bound_vars: FxHashSet<TyVarId> = typeck
                .coherence
                .generic_params
                .get(&def_id)
                .map(|info| {
                    info.hir_ids
                        .iter()
                        .filter_map(|hir_id| typeck.hir_id_to_ty_var.get(hir_id))
                        .copied()
                        .collect()
                })
                .unwrap_or_default();

            if let Some(&parent_def_id) = typeck.coherence.assoc_to_parent.get(&def_id)
                && let Some(info) = typeck.coherence.generic_params.get(&parent_def_id)
            {
                for hir_id in &info.hir_ids {
                    if let Some(&var_id) = typeck.hir_id_to_ty_var.get(hir_id) {
                        bound_vars.insert(var_id);
                    }
                }
            }

            for expr in &body.exprs {
                check_ty_no_free_vars(&expr.ty, &bound_vars, def_id, expr.hir_id);
                if let ExprKind::Cast { target_ty, .. } = &expr.kind {
                    check_ty_no_free_vars(target_ty, &bound_vars, def_id, expr.hir_id);
                }
            }

            for stmt in &body.stmts {
                if let StmtKind::Let { ty, .. } = &stmt.kind {
                    check_ty_no_free_vars(ty, &bound_vars, def_id, stmt.hir_id);
                }
            }

            for param in &body.params {
                check_ty_no_free_vars(&param.ty, &bound_vars, def_id, param.hir_id);
            }
        }
    }
}

fn check_ty_no_free_vars(ty: &Ty, bound_vars: &FxHashSet<TyVarId>, def_id: DefId, hir_id: HirId) {
    struct NoFreeVarVisitor<'a> {
        bound_vars: &'a FxHashSet<TyVarId>,
        def_id: DefId,
        hir_id: HirId,
    }

    impl TyVisitor for NoFreeVarVisitor<'_> {
        fn visit_ty(&mut self, ty: &Ty) -> VisitAction {
            if let Ty::Var(id) = ty {
                assert!(
                    self.bound_vars.contains(id),
                    "THIR contains free type variable {:?} in body {:?} (hir_id: {:?})",
                    id,
                    self.def_id,
                    self.hir_id
                );
            }
            VisitAction::Continue
        }
    }

    ty.visit(&mut NoFreeVarVisitor {
        bound_vars,
        def_id,
        hir_id,
    });
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub ty: Ty,
    pub span: Span,
    pub hir_id: HirId,
    pub temp_scope: Option<Scope>,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Scope {
        region_scope: Scope,
        value: ExprId,
    },
    Literal(Literal),
    VarRef(LocalVarId),
    Path {
        def_id: DefId,
    },
    /// Zero sized type: struct Unit {}
    ZstLiteral,
    Block(BlockId),
    If {
        cond: ExprId,
        then: ExprId,
        else_opt: Option<ExprId>,
    },
    Loop {
        body: ExprId,
    },
    Break {
        value: Option<ExprId>,
    },
    Return {
        value: Option<ExprId>,
    },
    Binary {
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
    },
    LogicalOp {
        op: LogOp,
        lhs: ExprId,
        rhs: ExprId,
    },
    Unary {
        op: UnOp,
        arg: ExprId,
    },
    Deref {
        arg: ExprId,
    },
    Borrow {
        kind: Mutability,
        arg: ExprId,
    },
    Call {
        callee: ExprId,
        args: ThinVec<ExprId>,
    },
    StructInit {
        def_id: DefId,
        fields: ThinVec<(Symbol, ExprId)>,
    },
    ArrayInit {
        elements: ThinVec<ExprId>,
    },
    TupleInit(ThinVec<ExprId>),
    Assign {
        target: ExprId,
        value: ExprId,
    },
    Field {
        base: ExprId,
        index: usize,
    },
    Index {
        base: ExprId,
        index: ExprId,
    },
    Cast {
        source: ExprId,
        target_ty: Ty,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LogOp {
    And,
    Or,
}

#[derive(Debug, Clone)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
    pub hir_id: HirId,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
    Semi {
        expr: ExprId,
    },
    Let {
        local_var: LocalVarId,
        name: Symbol,
        ty: Ty,
        init: Option<ExprId>,
        remainder_scope: Option<Scope>,
        init_scope: Option<Scope>,
    },
}

#[derive(Debug, Clone)]
pub struct Block {
    pub region_scope: Scope,
    pub stmts: ThinVec<StmtId>,
    pub expr: Option<ExprId>,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub name: Symbol,
    pub ty: Ty,
    pub hir_id: HirId,
    pub local_var: LocalVarId,
}
