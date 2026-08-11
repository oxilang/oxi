use crate::hir::{Expr, ExprKind, HirId, QPath, Stmt, StmtKind};
use crate::span::Span;
use crate::typeck::{MemberRes, Typeck};
use fxhash::FxHashMap;

impl<'ctx, 'hir, 'res> Typeck<'ctx, 'hir, 'res> {
    pub(crate) fn rewrite_member_access(&mut self) {
        for owner in self.krate.get_mut().owners.iter_mut() {
            let Some(info) = owner.as_owner_mut() else {
                continue;
            };
            for body in info.nodes.bodies.values_mut() {
                rewrite_expr(&mut body.value, &self.member_res);
            }
        }
    }
}

fn rewrite_expr(expr: &mut Expr, member_res: &FxHashMap<HirId, MemberRes>) {
    let res = member_res.get(&expr.hir_id).copied();
    match &mut expr.kind {
        ExprKind::MemberAccess { base, member } => {
            rewrite_expr(base, member_res);
            if let Some(MemberRes::Field { index }) = res {
                let base = std::mem::replace(
                    base,
                    Expr {
                        hir_id: expr.hir_id,
                        kind: ExprKind::Error,
                        span: Span::new(0, 0),
                    }
                    .into_box(),
                );
                expr.kind = ExprKind::Field {
                    base,
                    field: *member,
                    index,
                }
            }
        }
        ExprKind::Call { callee, args } => {
            let res = member_res.get(&callee.hir_id).copied();
            if let Some(MemberRes::Method { def_id, .. }) = res {
                let (mut base_owned, member_sym) =
                    match std::mem::replace(&mut callee.kind, ExprKind::Error) {
                        ExprKind::MemberAccess { base, member } => (base, member),
                        ExprKind::Path(QPath::TypeRelative { qself, segment }) => {
                            let receiver = Expr {
                                hir_id: callee.hir_id,
                                kind: ExprKind::Path(*qself),
                                span: callee.span,
                            }
                            .into_box();
                            (receiver, segment.ident.value)
                        }
                        _ => unreachable!(),
                    };
                rewrite_expr(&mut base_owned, member_res);
                let mut args_owned = std::mem::take(args);
                for arg in &mut args_owned {
                    rewrite_expr(arg, member_res);
                }
                expr.kind = ExprKind::MethodCall {
                    receiver: base_owned,
                    method: member_sym,
                    args: args_owned,
                    def_id,
                };
            } else {
                rewrite_expr(callee, member_res);
                for arg in args {
                    rewrite_expr(arg, member_res);
                }
            }
        }
        ExprKind::Binary { left, right, .. } => {
            rewrite_expr(left, member_res);
            rewrite_expr(right, member_res);
        }
        ExprKind::StructInit { fields, .. } => {
            for (_, field) in fields {
                rewrite_expr(field, member_res);
            }
        }
        ExprKind::ArrayInit { contents, .. } => {
            for expr in contents {
                rewrite_expr(expr, member_res);
            }
        }
        ExprKind::TupleInit(elements) => {
            for element in elements {
                rewrite_expr(element, member_res);
            }
        }
        ExprKind::Block(block) => {
            for stmt in &mut block.stmts {
                rewrite_stmt(stmt, member_res);
            }
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => {
            rewrite_expr(cond, member_res);
            for stmt in &mut then_branch.stmts {
                rewrite_stmt(stmt, member_res);
            }
            if let Some(else_branch) = else_branch {
                rewrite_expr(else_branch, member_res);
            }
        }
        ExprKind::Loop(block) => {
            for stmt in &mut block.stmts {
                rewrite_stmt(stmt, member_res);
            }
        }
        ExprKind::Break(expr) | ExprKind::Return(expr) => {
            if let Some(expr) = expr {
                rewrite_expr(expr, member_res);
            }
        }
        ExprKind::Assign { target, value, .. } => {
            rewrite_expr(target, member_res);
            rewrite_expr(value, member_res);
        }
        ExprKind::Dereference { expr } => {
            rewrite_expr(expr, member_res);
        }
        ExprKind::Reference { expr, .. } => {
            rewrite_expr(expr, member_res);
        }
        ExprKind::Unary { right: expr, .. } => {
            rewrite_expr(expr, member_res);
        }
        ExprKind::As { expr, .. } => {
            rewrite_expr(expr, member_res);
        }
        ExprKind::MethodCall { receiver, args, .. } => {
            rewrite_expr(receiver, member_res);
            for arg in args {
                rewrite_expr(arg, member_res);
            }
        }
        ExprKind::Field { base, .. } => {
            rewrite_expr(base, member_res);
        }
        ExprKind::Index { base, index } => {
            rewrite_expr(base, member_res);
            rewrite_expr(index, member_res);
        }
        ExprKind::Literal(_) | ExprKind::Path(_) | ExprKind::Error => {}
    }
}

fn rewrite_stmt(stmt: &mut Stmt, member_res: &FxHashMap<HirId, MemberRes>) {
    match &mut stmt.kind {
        StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
            rewrite_expr(expr, member_res);
        }
        StmtKind::Let { init, .. } => {
            if let Some(init) = init {
                rewrite_expr(init, member_res);
            }
        }
    }
}
