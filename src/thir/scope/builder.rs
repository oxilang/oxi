use thin_vec::ThinVec;

use crate::hir::{
    AssocItemKind, Block, Body, Crate, DefId, Expr, ExprKind, ItemKind, MaybeOwner, Node, Param,
    StmtKind,
};
use crate::thir::scope::{Scope, ScopeKind, ScopeTree, ScopeTrees};

pub fn build_scope_tree(body: &Body) -> ScopeTree {
    let mut builder = ScopeTreeBuilder::new();
    builder.tree.root = Some(body.value.hir_id);
    builder.build_expr(&body.value);
    builder.tree
}

pub fn build_fn_scope_tree(params: &ThinVec<Param>, body: &Body) -> ScopeTree {
    let mut builder = ScopeTreeBuilder::new();
    let body_hir_id = body.value.hir_id;
    builder.tree.root = Some(body_hir_id);

    let callsite = Scope {
        local_id: body_hir_id.local_id,
        kind: ScopeKind::CallSite,
    };
    builder.scope_stack.push(callsite);

    if !params.is_empty() {
        let args = Scope {
            local_id: body_hir_id.local_id,
            kind: ScopeKind::Parameters,
        };
        builder.tree.record_parent(args, callsite);
        builder.scope_stack.push(args);
        for param in params {
            builder.tree.record_var_scope(param.hir_id.local_id, args);
        }
    }

    builder.build_expr(&body.value);

    builder.tree
}

pub fn build_scope_trees(hir_crate: &Crate) -> ScopeTrees {
    let mut trees = ScopeTrees::default();

    for (i, owner) in hir_crate.owners.iter().enumerate() {
        let def_id = DefId(i as u32);
        let MaybeOwner::Owner(info) = owner else {
            continue;
        };

        match &info.nodes.nodes[0].node {
            Node::Item(item) => match &item.kind {
                ItemKind::Fn(fun) => {
                    if let Some(body_id) = fun.body_id
                        && let Some(body) = info.nodes.body(body_id)
                    {
                        trees
                            .per_body
                            .insert(def_id, build_fn_scope_tree(&fun.decl.params, body));
                    }
                }
                ItemKind::Const { body_id, .. } => {
                    if let Some(body_id) = body_id
                        && let Some(body) = info.nodes.body(*body_id)
                    {
                        trees.per_body.insert(def_id, build_scope_tree(body));
                    }
                }
                _ => {}
            },
            Node::AssocItem(assoc) => {
                let AssocItemKind::Fn(fun) = &assoc.kind else {
                    continue;
                };
                if let Some(body_id) = fun.body_id
                    && let Some(body) = info.nodes.body(body_id)
                {
                    trees
                        .per_body
                        .insert(def_id, build_fn_scope_tree(&fun.decl.params, body));
                }
            }
            _ => {}
        }
    }

    trees
}

struct ScopeTreeBuilder {
    tree: ScopeTree,
    scope_stack: Vec<Scope>,
}

impl ScopeTreeBuilder {
    fn new() -> Self {
        ScopeTreeBuilder {
            tree: ScopeTree::default(),
            scope_stack: Vec::new(),
        }
    }

    fn current_scope(&self) -> Option<Scope> {
        self.scope_stack.last().copied()
    }

    fn push_scope(&mut self, kind: ScopeKind, local_id: crate::hir::ItemLocalId) -> Scope {
        let scope = Scope { local_id, kind };
        if let Some(parent) = self.current_scope() {
            self.tree.record_parent(scope, parent);
        }
        self.scope_stack.push(scope);
        scope
    }

    fn pop_scope(&mut self) {
        self.scope_stack.pop();
    }

    fn build_expr(&mut self, expr: &Expr) {
        self.push_scope(ScopeKind::Node, expr.hir_id.local_id);

        match &expr.kind {
            ExprKind::Block(block) => {
                self.build_block(block);
            }
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                self.build_if(cond, then_branch, else_branch.as_deref());
            }
            ExprKind::Loop(block) => {
                self.push_scope(ScopeKind::LoopBody, block.hir_id.local_id);
                self.build_block(block);
                self.pop_scope();
            }
            ExprKind::Binary { left, right, .. } => {
                self.build_expr(left);
                self.build_expr(right);
            }
            ExprKind::Call { callee, args } => {
                self.build_expr(callee);
                for arg in args {
                    self.build_expr(arg);
                }
            }
            ExprKind::MethodCall { receiver, args, .. } => {
                self.build_expr(receiver);
                for arg in args {
                    self.build_expr(arg);
                }
            }
            ExprKind::Field { base, .. } => {
                self.build_expr(base);
            }
            ExprKind::MemberAccess { base, .. } => {
                self.build_expr(base);
            }
            ExprKind::Index { base, index } => {
                self.build_expr(base);
                self.build_expr(index);
            }
            ExprKind::StructInit { fields, .. } => {
                for (_, field_expr) in fields {
                    self.build_expr(field_expr);
                }
            }
            ExprKind::ArrayInit { contents, .. } | ExprKind::TupleInit(contents) => {
                for element in contents {
                    self.build_expr(element);
                }
            }
            ExprKind::Unary { right, .. } => {
                self.build_expr(right);
            }
            ExprKind::Dereference { expr } => {
                self.build_expr(expr);
            }
            ExprKind::Reference { expr, .. } => {
                self.build_expr(expr);
            }
            ExprKind::Assign { target, value, .. } => {
                self.build_expr(target);
                self.build_expr(value);
            }
            ExprKind::Break(inner) | ExprKind::Return(inner) => {
                if let Some(inner) = inner {
                    self.build_expr(inner);
                }
            }
            ExprKind::As { expr: inner, .. } => {
                self.build_expr(inner);
            }
            ExprKind::Literal(_) | ExprKind::Path(_) | ExprKind::Error => {}
        }

        self.pop_scope();
    }

    fn build_block(&mut self, block: &Block) {
        self.push_scope(ScopeKind::Node, block.hir_id.local_id);

        let mut remainder_count = 0u32;
        for (i, stmt) in block.stmts.iter().enumerate() {
            match &stmt.kind {
                StmtKind::Let { init, local, .. } => {
                    if let Some(init_expr) = init {
                        self.build_expr(init_expr);
                    }
                    let rem = self.push_scope(
                        ScopeKind::Remainder { index: i as u32 },
                        stmt.hir_id.local_id,
                    );
                    self.tree.record_var_scope(local.local_id, rem);
                    remainder_count += 1;
                }
                StmtKind::Semi(expr) => {
                    self.push_scope(ScopeKind::Destruction, stmt.hir_id.local_id);
                    self.build_expr(expr);
                    self.pop_scope();
                }
                StmtKind::Expr(expr) => {
                    self.build_expr(expr);
                }
            }
        }

        for _ in 0..remainder_count {
            self.pop_scope();
        }

        self.pop_scope();
    }

    fn build_if(&mut self, cond: &Expr, then_branch: &Block, else_branch: Option<&Expr>) {
        self.push_scope(ScopeKind::IfThen, cond.hir_id.local_id);
        self.build_expr(cond);
        self.build_block(then_branch);
        self.pop_scope();

        if let Some(else_expr) = else_branch {
            self.build_expr(else_expr);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Literal, Mutability};
    use crate::hir::{
        BinOp, Block, Body, Expr, ExprKind, HirId, IntTy, ItemLocalId, OwnerId, Param, PrimTy,
        Stmt, StmtKind, Ty, TyKind,
    };
    use crate::span::Span;
    use thin_vec::thin_vec;

    fn hir_id(local: u32) -> HirId {
        HirId {
            owner: OwnerId(0),
            local_id: ItemLocalId(local),
        }
    }

    fn lit_expr(local: u32, val: i64) -> Expr {
        Expr {
            hir_id: hir_id(local),
            kind: ExprKind::Literal(Literal::Integer(val)),
            span: Span::new(0, 1),
        }
    }

    fn empty_block(local: u32) -> Block {
        Block {
            hir_id: hir_id(local),
            stmts: thin_vec![],
            span: Span::new(0, 1),
        }
    }

    #[test]
    fn literal_body() {
        // { 42 }
        let expr = lit_expr(1, 42);
        let body = Body { value: expr };
        let tree = build_scope_tree(&body);

        assert_eq!(tree.root, Some(hir_id(1)));
        let expected = Scope {
            local_id: ItemLocalId(1),
            kind: ScopeKind::Node,
        };
        assert_eq!(tree.encl_scope(expected), None);
    }

    fn param(id: u32) -> Param {
        Param {
            hir_id: hir_id(id),
            name: 1,
            ty: Ty {
                hir_id: hir_id(99),
                kind: TyKind::PrimTy(PrimTy::Int(IntTy::I32)),
                span: Span::new(0, 2),
            },
            span: Span::new(0, 1),
        }
    }

    fn infer_ty() -> Ty {
        Ty {
            hir_id: hir_id(99),
            kind: TyKind::Infer,
            span: Span::new(0, 1),
        }
    }

    #[test]
    fn fn_body_with_params() {
        // fn _(_: i32) _ { 0 }
        let body_expr = lit_expr(2, 0);
        let body = Body { value: body_expr };
        let params = thin_vec![param(1)];

        let tree = build_fn_scope_tree(&params, &body);
        let callsite = Scope {
            local_id: ItemLocalId(2),
            kind: ScopeKind::CallSite,
        };
        let params_scope = Scope {
            local_id: ItemLocalId(2),
            kind: ScopeKind::Parameters,
        };
        let expr_scope = Scope {
            local_id: ItemLocalId(2),
            kind: ScopeKind::Node,
        };

        assert_eq!(tree.encl_scope(callsite), None);
        assert_eq!(tree.encl_scope(params_scope), Some(callsite));
        assert_eq!(tree.encl_scope(expr_scope), Some(params_scope));
        assert_eq!(tree.var_scope(ItemLocalId(1)), Some(params_scope));
    }

    fn let_stmt(id: u32, local_id: u32, init: Option<Expr>) -> Stmt {
        Stmt {
            hir_id: hir_id(id),
            kind: StmtKind::Let {
                name: 1,
                ty: infer_ty(),
                init,
                local: hir_id(local_id),
                mutability: Mutability::Constant,
            },
            span: Span::new(0, 5),
        }
    }

    #[test]
    fn block_with_let() {
        // { let x = 1; }
        let init = lit_expr(2, 1);
        let stmt = let_stmt(3, 4, Some(init));
        let block = Block {
            hir_id: hir_id(1),
            stmts: thin_vec![stmt],
            span: Span::new(0, 5),
        };
        let body_expr = Expr {
            hir_id: hir_id(5),
            kind: ExprKind::Block(block),
            span: Span::new(0, 5),
        };
        let body = Body { value: body_expr };
        let tree = build_scope_tree(&body);

        let expr_scope = Scope {
            local_id: ItemLocalId(5),
            kind: ScopeKind::Node,
        };
        let block_scope = Scope {
            local_id: ItemLocalId(1),
            kind: ScopeKind::Node,
        };
        let init_scope = Scope {
            local_id: ItemLocalId(2),
            kind: ScopeKind::Node,
        };
        let remainder = Scope {
            local_id: ItemLocalId(3),
            kind: ScopeKind::Remainder { index: 0 },
        };

        assert_eq!(tree.encl_scope(block_scope), Some(expr_scope));
        assert_eq!(tree.encl_scope(remainder), Some(block_scope));
        assert_eq!(tree.encl_scope(init_scope), Some(block_scope));
        assert_eq!(tree.var_scope(ItemLocalId(4)), Some(remainder));
    }

    #[test]
    fn block_multiple_lets() {
        // { let x = 1; let y = 2; }
        let stmt_x = let_stmt(3, 4, Some(lit_expr(2, 1)));
        let stmt_y = let_stmt(6, 7, Some(lit_expr(5, 2)));
        let block = Block {
            hir_id: hir_id(1),
            stmts: thin_vec![stmt_x, stmt_y],
            span: Span::new(0, 10),
        };
        let body_expr = Expr {
            hir_id: hir_id(8),
            kind: ExprKind::Block(block),
            span: Span::new(0, 10),
        };
        let body = Body { value: body_expr };
        let tree = build_scope_tree(&body);

        let block_scope = Scope {
            local_id: ItemLocalId(1),
            kind: ScopeKind::Node,
        };
        let rem_x = Scope {
            local_id: ItemLocalId(3),
            kind: ScopeKind::Remainder { index: 0 },
        };
        let rem_y = Scope {
            local_id: ItemLocalId(6),
            kind: ScopeKind::Remainder { index: 1 },
        };

        assert_eq!(tree.encl_scope(rem_x), Some(block_scope));
        assert_eq!(tree.encl_scope(rem_y), Some(rem_x));

        assert_eq!(tree.var_scope(ItemLocalId(4)), Some(rem_x));
        assert_eq!(tree.var_scope(ItemLocalId(7)), Some(rem_y));

        assert!(tree.is_subscope_of(rem_y, block_scope));
        assert!(tree.is_subscope_of(rem_y, rem_x));
        assert!(!tree.is_subscope_of(rem_x, rem_y));
    }

    #[test]
    fn if_expression() {
        // if 1 { } else 2
        let cond = lit_expr(1, 1);
        let then_block = empty_block(2);
        let else_expr = lit_expr(3, 2);
        let if_expr = Expr {
            hir_id: hir_id(4),
            kind: ExprKind::If {
                cond: Box::new(cond),
                then_branch: then_block,
                else_branch: Some(Box::new(else_expr)),
            },
            span: Span::new(0, 10),
        };
        let body = Body { value: if_expr };
        let tree = build_scope_tree(&body);

        let if_scope = Scope {
            local_id: ItemLocalId(4),
            kind: ScopeKind::Node,
        };
        let if_then = Scope {
            local_id: ItemLocalId(1),
            kind: ScopeKind::IfThen,
        };
        let cond_scope = Scope {
            local_id: ItemLocalId(1),
            kind: ScopeKind::Node,
        };
        let then_block_scope = Scope {
            local_id: ItemLocalId(2),
            kind: ScopeKind::Node,
        };
        let else_scope = Scope {
            local_id: ItemLocalId(3),
            kind: ScopeKind::Node,
        };

        assert_eq!(tree.encl_scope(if_then), Some(if_scope));
        assert_eq!(tree.encl_scope(cond_scope), Some(if_then));
        assert_eq!(tree.encl_scope(then_block_scope), Some(if_then));
        assert_eq!(tree.encl_scope(else_scope), Some(if_scope));
    }

    #[test]
    fn loop_expression() {
        // loop { 1 }
        let body_block = Block {
            hir_id: hir_id(2),
            stmts: thin_vec![Stmt {
                hir_id: hir_id(3),
                kind: StmtKind::Expr(lit_expr(4, 1)),
                span: Span::new(0, 1),
            }],
            span: Span::new(0, 5),
        };
        let loop_expr = Expr {
            hir_id: hir_id(1),
            kind: ExprKind::Loop(body_block),
            span: Span::new(0, 5),
        };
        let body = Body { value: loop_expr };
        let tree = build_scope_tree(&body);

        let loop_scope = Scope {
            local_id: ItemLocalId(1),
            kind: ScopeKind::Node,
        };
        let loop_body = Scope {
            local_id: ItemLocalId(2),
            kind: ScopeKind::LoopBody,
        };
        let block_scope = Scope {
            local_id: ItemLocalId(2),
            kind: ScopeKind::Node,
        };

        assert_eq!(tree.encl_scope(loop_body), Some(loop_scope));
        assert_eq!(tree.encl_scope(block_scope), Some(loop_body));
    }

    #[test]
    fn binary_expression() {
        // { 1 + 2 }
        let left = lit_expr(1, 1);
        let right = lit_expr(2, 2);
        let bin_op = Expr {
            hir_id: hir_id(3),
            kind: ExprKind::Binary {
                left: Box::new(left),
                op: BinOp::Add,
                right: Box::new(right),
            },
            span: Span::new(0, 3),
        };
        let body = Body { value: bin_op };
        let tree = build_scope_tree(&body);

        let bin_scope = Scope {
            local_id: ItemLocalId(3),
            kind: ScopeKind::Node,
        };
        let left_scope = Scope {
            local_id: ItemLocalId(1),
            kind: ScopeKind::Node,
        };
        let right_scope = Scope {
            local_id: ItemLocalId(2),
            kind: ScopeKind::Node,
        };

        assert!(tree.is_subscope_of(left_scope, bin_scope));
        assert!(tree.is_subscope_of(right_scope, bin_scope));
    }

    #[test]
    fn nested_blocks() {
        // { { 42 } }
        let inner_block = empty_block(2);
        let inner_expr = Expr {
            hir_id: hir_id(3),
            kind: ExprKind::Block(inner_block),
            span: Span::new(0, 5),
        };
        let outer_block = Block {
            hir_id: hir_id(1),
            stmts: thin_vec![Stmt {
                hir_id: hir_id(4),
                kind: StmtKind::Expr(inner_expr),
                span: Span::new(0, 5),
            }],
            span: Span::new(0, 7),
        };
        let outer_expr = Expr {
            hir_id: hir_id(5),
            kind: ExprKind::Block(outer_block),
            span: Span::new(0, 7),
        };
        let body = Body { value: outer_expr };
        let tree = build_scope_tree(&body);

        let outer_expr_scope = Scope {
            local_id: ItemLocalId(5),
            kind: ScopeKind::Node,
        };
        let outer_block_scope = Scope {
            local_id: ItemLocalId(1),
            kind: ScopeKind::Node,
        };
        let inner_expr_scope = Scope {
            local_id: ItemLocalId(3),
            kind: ScopeKind::Node,
        };
        let inner_block_scope = Scope {
            local_id: ItemLocalId(2),
            kind: ScopeKind::Node,
        };

        assert!(tree.is_subscope_of(outer_block_scope, outer_expr_scope));
        assert!(tree.is_subscope_of(inner_expr_scope, outer_block_scope));
        assert!(tree.is_subscope_of(inner_block_scope, inner_expr_scope));
    }

    #[test]
    fn semi_statement() {
        // { 1; }
        let stmt = Stmt {
            hir_id: hir_id(2),
            kind: StmtKind::Semi(lit_expr(1, 1)),
            span: Span::new(0, 2),
        };
        let block = Block {
            hir_id: hir_id(3),
            stmts: thin_vec![stmt],
            span: Span::new(0, 3),
        };
        let body_expr = Expr {
            hir_id: hir_id(4),
            kind: ExprKind::Block(block),
            span: Span::new(0, 3),
        };
        let body = Body { value: body_expr };
        let tree = build_scope_tree(&body);

        let block_scope = Scope {
            local_id: ItemLocalId(3),
            kind: ScopeKind::Node,
        };
        let destruction = Scope {
            local_id: ItemLocalId(2),
            kind: ScopeKind::Destruction,
        };
        let expr_scope = Scope {
            local_id: ItemLocalId(1),
            kind: ScopeKind::Node,
        };

        assert_eq!(tree.encl_scope(destruction), Some(block_scope));
        assert_eq!(tree.encl_scope(expr_scope), Some(destruction));
    }

    #[test]
    fn return_statement() {
        // { return 42 }
        let inner = lit_expr(2, 42);
        let ret_expr = Expr {
            hir_id: hir_id(1),
            kind: ExprKind::Return(Some(Box::new(inner))),
            span: Span::new(0, 8),
        };
        let body = Body { value: ret_expr };
        let tree = build_scope_tree(&body);

        let ret_scope = Scope {
            local_id: ItemLocalId(1),
            kind: ScopeKind::Node,
        };
        let inner_scope = Scope {
            local_id: ItemLocalId(2),
            kind: ScopeKind::Node,
        };

        assert!(tree.is_subscope_of(inner_scope, ret_scope));
    }

    #[test]
    fn fn_body_no_params() {
        // fn _() { 42 }
        let body_expr = lit_expr(1, 42);
        let body = Body { value: body_expr };
        let tree = build_fn_scope_tree(&ThinVec::new(), &body);

        let callsite = Scope {
            local_id: ItemLocalId(1),
            kind: ScopeKind::CallSite,
        };
        let expr_scope = Scope {
            local_id: ItemLocalId(1),
            kind: ScopeKind::Node,
        };

        // No Parameters scope since there are no params
        assert_eq!(tree.encl_scope(callsite), None);
        assert_eq!(tree.encl_scope(expr_scope), Some(callsite));
    }

    #[test]
    fn scope_tree_default_empty() {
        let tree = ScopeTree::default();
        assert_eq!(tree.root, None);
        assert_eq!(
            tree.encl_scope(Scope {
                local_id: ItemLocalId(1),
                kind: ScopeKind::Node,
            }),
            None
        );
        assert_eq!(tree.var_scope(ItemLocalId(1)), None);
    }
}
