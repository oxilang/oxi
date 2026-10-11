use crate::hir::{
    AssocItemKind, Block, Body, Crate, DefId, Expr, ExprKind, ItemKind, MaybeOwner, Node, StmtKind,
};
use crate::thir::scope::{Scope, ScopeKind, ScopeTree, ScopeTrees};

pub fn build_scope_tree(body: &Body) -> ScopeTree {
    let mut builder = ScopeTreeBuilder::new();
    builder.tree.root = Some(body.value.hir_id);
    builder.build_expr(&body.value);
    builder.tree
}

pub fn build_fn_scope_tree(body: &Body) -> ScopeTree {
    let mut builder = ScopeTreeBuilder::new();
    let body_hir_id = body.value.hir_id;
    builder.tree.root = Some(body_hir_id);

    let callsite = Scope {
        local_id: body_hir_id.local_id,
        kind: ScopeKind::CallSite,
    };
    builder.scope_stack.push(callsite);

    if !body.params.is_empty() {
        let args = Scope {
            local_id: body_hir_id.local_id,
            kind: ScopeKind::Parameters,
        };
        builder.tree.record_parent(args, callsite);
        builder.scope_stack.push(args);
        for param in &body.params {
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
                        trees.per_body.insert(def_id, build_fn_scope_tree(body));
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
                let AssocItemKind::Fn(fun) = &assoc.kind;
                if let Some(body_id) = fun.body_id
                    && let Some(body) = info.nodes.body(body_id)
                {
                    trees.per_body.insert(def_id, build_fn_scope_tree(body));
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
                StmtKind::Expr(expr) => {
                    self.push_scope(ScopeKind::Destruction, stmt.hir_id.local_id);
                    self.build_expr(expr);
                    self.pop_scope();
                }
            }
        }

        if let Some(tail) = &block.tail {
            self.build_expr(tail);
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
