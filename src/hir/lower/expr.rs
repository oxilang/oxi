use thin_vec::{ThinVec, thin_vec};

use crate::ast::{self, NodeId};
use crate::diag_params;
use crate::errors::builders;
use crate::hir::types::{AssOp, BinOp, Block, Expr, ExprKind, FromToken, Stmt, StmtKind, UnOp};
use crate::hir::{AstLoweringContext, DefId, diag};
use crate::lexer::token::{Token, TokenKind};
use crate::resolve::Res;

impl<'a, 'ctx> AstLoweringContext<'a, 'ctx> {
    pub(super) fn lower_expr(&mut self, expr: &ast::Expr) -> Expr {
        let hir_id = self.next_hir_id();
        let kind = self.lower_expr_kind(expr);
        Expr {
            hir_id,
            kind,
            span: expr.span,
        }
    }

    fn lower_expr_kind(&mut self, expr: &ast::Expr) -> ExprKind {
        match &expr.kind {
            ast::ExprKind::Path(path) => {
                let qpath = self.lower_qpath(path, expr.node_id);
                ExprKind::Path(qpath)
            }
            ast::ExprKind::Literal(lit) => ExprKind::Literal(*lit),
            ast::ExprKind::Binary {
                left,
                operator,
                right,
            } => {
                let left = self.lower_expr(left);
                let right = self.lower_expr(right);
                if operator.kind == TokenKind::Pipe {
                    match right.kind {
                        ExprKind::Call { callee, args } => {
                            let mut new_args = ThinVec::with_capacity(args.len() + 1);
                            new_args.push(left);
                            new_args.extend(args);
                            ExprKind::Call {
                                args: new_args,
                                callee,
                            }
                        }
                        _ => ExprKind::Call {
                            callee: right.into_box(),
                            args: thin_vec![left],
                        },
                    }
                } else {
                    let Some(op) = self.lower_operator(operator, "binary") else {
                        return ExprKind::Error;
                    };
                    ExprKind::Binary {
                        left: left.into_box(),
                        op,
                        right: right.into_box(),
                    }
                }
            }
            ast::ExprKind::Unary { operator, right } => {
                let right = self.lower_expr(right).into_box();
                let Some(op) = self.lower_operator(operator, "prefix") else {
                    return ExprKind::Error;
                };
                ExprKind::Unary { op, right }
            }
            ast::ExprKind::Range { .. } => {
                todo!("desugar range")
            }
            ast::ExprKind::Dereference { expr } => {
                let expr = self.lower_expr(expr).into_box();
                ExprKind::Dereference { expr }
            }
            ast::ExprKind::Reference { expr, mutability } => {
                let expr = self.lower_expr(expr).into_box();
                ExprKind::Reference {
                    expr,
                    mutability: *mutability,
                }
            }
            ast::ExprKind::Assignment {
                assignee,
                operator,
                value,
            } => {
                let Some(op) = self.lower_operator(operator, "assignment") else {
                    return ExprKind::Error;
                };
                match op {
                    AssOp::Ass => {
                        let target = self.lower_expr(assignee).into_box();
                        let value = self.lower_expr(value).into_box();
                        ExprKind::Assign { target, value }
                    }
                    _ => {
                        let target = self.lower_expr(assignee).into_box();
                        let value = self.lower_expr(value).into_box();
                        let lhs = target.clone();
                        let bin_op = match op {
                            AssOp::AssAdd => BinOp::Add,
                            AssOp::AssSub => BinOp::Sub,
                            AssOp::AssMul => BinOp::Mul,
                            AssOp::AssDiv => BinOp::Div,
                            AssOp::AssRem => BinOp::Rem,
                            AssOp::AssBitAnd => BinOp::BitAnd,
                            AssOp::AssBitOr => BinOp::BitOr,
                            AssOp::AssBitXor => BinOp::BitXor,
                            AssOp::AssShl => BinOp::Shl,
                            AssOp::AssShr => BinOp::Shr,
                            AssOp::Ass => unreachable!(),
                        };
                        ExprKind::Assign {
                            target,
                            value: Box::new(Expr {
                                kind: ExprKind::Binary {
                                    left: lhs,
                                    op: bin_op,
                                    right: value,
                                },
                                hir_id: self.next_hir_id(),
                                span: expr.span,
                            }),
                        }
                    }
                }
            }
            ast::ExprKind::FunctionCall { callee, arguments } => {
                let callee = self.lower_expr(callee).into_box();
                let args = arguments.iter().map(|expr| self.lower_expr(expr)).collect();
                ExprKind::Call { callee, args }
            }
            ast::ExprKind::StructInstantiation { path, fields } => {
                let def = match self.resolve_def_id(&expr.node_id) {
                    Some(def_id) => def_id,
                    _ => return ExprKind::Error,
                };
                let generic_args = path
                    .segments
                    .last()
                    .and_then(|seg| seg.generic_args.as_ref())
                    .map(|args| args.iter().map(|ty| self.lower_type(ty)).collect());
                let fields = fields
                    .iter()
                    .map(|(name, expr)| (*name, self.lower_expr(expr)))
                    .collect();
                ExprKind::StructInit {
                    def,
                    generic_args,
                    fields,
                }
            }
            ast::ExprKind::Array { contents } => {
                let contents = contents.iter().map(|expr| self.lower_expr(expr)).collect();
                ExprKind::ArrayInit { contents }
            }
            ast::ExprKind::Tuple { elements } => {
                let elements = elements.iter().map(|expr| self.lower_expr(expr)).collect();
                ExprKind::TupleInit(elements)
            }
            ast::ExprKind::MemberAccess { base, member } => {
                let base = self.lower_expr(base).into_box();
                ExprKind::MemberAccess {
                    member: member.value,
                    base,
                }
            }
            ast::ExprKind::Index { base, index } => {
                let base = self.lower_expr(base).into_box();
                let index = self.lower_expr(index).into_box();
                ExprKind::Index { base, index }
            }
            ast::ExprKind::Block(block) => {
                let block = self.lower_block(block);
                ExprKind::Block(block)
            }
            ast::ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let cond = self.lower_expr(condition).into_box();
                let then_branch = self.lower_block(then_branch);
                let else_branch = else_branch
                    .as_ref()
                    .map(|expr| self.lower_expr(expr).into_box());
                ExprKind::If {
                    cond,
                    then_branch,
                    else_branch,
                }
            }
            ast::ExprKind::Loop(block) => {
                let block = self.lower_block(block);
                ExprKind::Loop(block)
            }
            ast::ExprKind::While { condition, body } => {
                let cond = self.lower_expr(condition);
                let cond_check = self.while_cond_shim(cond);

                let mut new_body = ThinVec::with_capacity(body.stmts.len() + 1);
                new_body.push(cond_check);
                new_body.extend(body.stmts.iter().map(|stmt| self.lower_stmt(stmt)));
                if let Some(tail) = body.tail.as_ref() {
                    let tail = self.lower_expr(tail);
                    new_body.push(Stmt {
                        hir_id: self.next_hir_id(),
                        span: tail.span,
                        kind: StmtKind::Expr(tail),
                    });
                }

                ExprKind::Loop(Block {
                    stmts: new_body,
                    tail: None,
                    span: body.span,
                    hir_id: self.next_hir_id(),
                })
            }
            ast::ExprKind::Return(val) => {
                let val = val.as_ref().map(|expr| self.lower_expr(expr).into_box());
                ExprKind::Return(val)
            }
            ast::ExprKind::Break(val) => {
                let val = val.as_ref().map(|expr| self.lower_expr(expr).into_box());
                ExprKind::Break(val)
            }
            ast::ExprKind::As { expr, ty } => {
                let expr = self.lower_expr(expr).into_box();
                let ty = self.lower_type(ty);
                ExprKind::As { expr, ty }
            }
        }
    }

    fn lower_block(&mut self, block: &ast::Block) -> Block {
        let stmts = block
            .stmts
            .iter()
            .map(|stmt| self.lower_stmt(stmt))
            .collect();
        let tail = block
            .tail
            .as_ref()
            .map(|tail| self.lower_expr(tail).into_box());
        Block {
            stmts,
            tail,
            span: block.span,
            hir_id: self.next_hir_id(),
        }
    }

    fn resolve_def_id(&self, node_id: &NodeId) -> Option<DefId> {
        match self
            .resolver
            .res_map
            .get(node_id)
            .and_then(|p| p.full_res())
        {
            Some(Res::Def(def_id)) => Some(def_id),
            Some(Res::SelfTyAlias { alias_to }) => Some(alias_to),
            _ => None,
        }
    }

    fn lower_operator<T: FromToken<T>>(&mut self, op: &Token, kind: &str) -> Option<T> {
        T::from_token(op).or_else(|| {
            builders::emit_at(
                self.ctx,
                op.span,
                op.module_id,
                diag::InvalidOperator,
                diag_params! { kind = kind },
            );
            None
        })
    }

    #[inline]
    fn while_cond_shim(&mut self, cond: Expr) -> Stmt {
        let span = cond.span;
        let cond = cond.into_box();
        Stmt {
            kind: StmtKind::Expr(Expr {
                kind: ExprKind::If {
                    then_branch: Block {
                        stmts: thin_vec![Stmt {
                            kind: StmtKind::Expr(Expr {
                                kind: ExprKind::Break(None),
                                hir_id: self.next_hir_id(),
                                span,
                            }),
                            hir_id: self.next_hir_id(),
                            span,
                        }],
                        tail: None,
                        hir_id: self.next_hir_id(),
                        span,
                    },
                    cond: Box::new(Expr {
                        kind: ExprKind::Unary {
                            op: UnOp::Not,
                            right: cond,
                        },
                        hir_id: self.next_hir_id(),
                        span,
                    }),
                    else_branch: None,
                },
                hir_id: self.next_hir_id(),
                span,
            }),
            hir_id: self.next_hir_id(),
            span,
        }
    }
}
