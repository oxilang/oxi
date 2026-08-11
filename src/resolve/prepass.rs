use thin_vec::ThinVec;

use crate::ast::visit::{VisitAction, Visitable, VisitorMut};
use crate::ast::{
    AssocItem, AssocItemKind, Ast, Expr, Fn, GenericParams, Item, ItemKind, NodeId, Stmt, Type,
    TypeKind,
};
use crate::context::Ctx;
use crate::resolve::Resolver;

// TODO: Check for id == NodeId::DEFAULT
impl<'a, 'ctx> Resolver<'a, 'ctx> {
    pub fn assign_node_ids(ctx: &mut Ctx, ast: &mut Ast) {
        ast.visit_mut(&mut NodeIdAssigner::new(ctx));
    }
}

#[derive(Debug)]
struct NodeIdAssigner<'ctx> {
    ctx: &'ctx mut Ctx,
}

impl<'ctx> NodeIdAssigner<'ctx> {
    pub fn new(ctx: &'ctx mut Ctx) -> Self {
        Self { ctx }
    }

    fn next_node_id(&mut self) -> NodeId {
        let id = self.ctx.next_node_id;
        self.ctx.next_node_id += 1;
        NodeId(id)
    }

    fn assign_to_assoc_items(&mut self, items: &mut ThinVec<AssocItem>) {
        for item in items {
            item.node_id = self.next_node_id();
            match &mut item.kind {
                AssocItemKind::Fn(fun) => self.assign_to_fn(fun),
                AssocItemKind::Type { .. } => {}
            }
        }
    }

    fn assign_to_fn(&mut self, fun: &mut Fn) {
        if let Some(generic_params) = &mut fun.generic_params {
            self.assign_to_generic_params(generic_params);
        }
        for arg in &mut fun.parameters {
            arg.2 = self.next_node_id();
        }
    }

    fn assign_to_generic_params(&mut self, generic_params: &mut GenericParams) {
        for param in &mut generic_params.params {
            param.node_id = self.next_node_id();
        }
    }
}

impl<'ctx> VisitorMut for NodeIdAssigner<'ctx> {
    // TODO: Doesn't the Visitor alrady handle this, could the match be removed?
    fn visit_item(&mut self, item: &mut Item) -> VisitAction {
        item.node_id = self.next_node_id();

        match &mut item.kind {
            ItemKind::Fn(fun) => {
                self.assign_to_fn(fun);
            }
            ItemKind::Impl {
                self_ty,
                trait_,
                items,
            } => {
                self_ty.1 = self.next_node_id();
                trait_.1 = self.next_node_id();
                self.assign_to_assoc_items(items);
            }
            ItemKind::Struct {
                items,
                generic_params,
                ..
            } => {
                self.assign_to_assoc_items(items);
                if let Some(generic_params) = generic_params {
                    self.assign_to_generic_params(generic_params);
                }
            }
            ItemKind::Trait {
                items,
                generic_params,
                ..
            } => {
                self.assign_to_assoc_items(items);
                if let Some(generic_params) = generic_params {
                    self.assign_to_generic_params(generic_params);
                }
            }
            ItemKind::Type { generic_params, .. } => {
                if let Some(generic_params) = generic_params {
                    self.assign_to_generic_params(generic_params);
                }
            }
            ItemKind::Import(_) | ItemKind::Module { .. } | ItemKind::Const { .. } => {}
        }

        VisitAction::Continue
    }

    fn visit_stmt(&mut self, stmt: &mut Stmt) -> VisitAction {
        stmt.node_id = self.next_node_id();
        VisitAction::Continue
    }

    fn visit_expr(&mut self, expr: &mut Expr) -> VisitAction {
        expr.node_id = self.next_node_id();
        VisitAction::Continue
    }

    fn visit_type(&mut self, ty: &mut Type) -> VisitAction {
        ty.node_id = self.next_node_id();

        if let TypeKind::Projection { base, trait_, .. } = &mut ty.kind {
            base.1 = self.next_node_id();
            trait_.1 = self.next_node_id();
        }

        VisitAction::Continue
    }
}
