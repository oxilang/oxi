use crate::ast;
use crate::hir::AstLoweringContext;
use crate::hir::types::{Stmt, StmtKind};

impl<'a, 'ctx> AstLoweringContext<'a, 'ctx> {
    pub(super) fn lower_stmt(&mut self, stmt: &ast::Stmt) -> Stmt {
        let hir_id = self.next_hir_id();
        let kind = match &stmt.kind {
            ast::StmtKind::Let {
                name,
                ty,
                value,
                mutability,
            } => {
                let init = value.as_ref().map(|expr| self.lower_expr(expr));
                let ty = self.lower_type(ty);

                // Register the local's HirId so path expressions can resolve to it
                self.register_local(stmt.node_id, hir_id);

                StmtKind::Let {
                    name: name.value,
                    ty,
                    init,
                    local: hir_id,
                    mutability: *mutability,
                }
            }
            ast::StmtKind::Expr(expr) => StmtKind::Expr(self.lower_expr(expr)),
        };

        Stmt {
            hir_id,
            kind,
            span: stmt.span,
        }
    }
}
