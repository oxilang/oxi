use thin_vec::ThinVec;

use crate::ast::visit::{VisitAction, Visitable, Visitor};
use crate::ast::{
    AssocItem, AssocItemKind, Expr, ExprKind, Fn, Item, ItemKind, NodeId, Path, Stmt, StmtKind,
    Type, TypeKind, path_segments_to_string,
};
use crate::diag_params;
use crate::errors::builders;
use crate::hir::DefId;
use crate::interner::Symbol;
use crate::resolve::path::PathError;
use crate::resolve::{PartialRes, PrimTy, Res, Resolver, diag};
use fxhash::FxHashMap;

impl<'a, 'ctx> Resolver<'a, 'ctx> {
    pub(super) fn late_resolve(&mut self) {
        self.traverse_tree(|this, node_idx, items| {
            this.module_idx = node_idx;
            let mut visitor = LateResolutionVisitor::new(this);
            for item in items {
                item.visit(&mut visitor);
            }
        });
    }
}

#[derive(Debug, Default)]
struct Rib {
    pub bindings: FxHashMap<Symbol, Res>,
    pub kind: RibKind,
}

impl Rib {
    fn new(kind: RibKind) -> Self {
        Self {
            bindings: FxHashMap::default(),
            kind,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
enum RibKind {
    /// No restrictions on which bindings may be used.
    #[default]
    Normal,
    /// We have entered an item definition. Block upvars.
    /// ```ignore
    /// fn main() void {
    ///     let a = 0;
    ///     fn b() void {
    ///         do_stuff(a); // Block usage of `a` here
    ///     }
    /// }
    /// ```
    Item,
}

impl RibKind {
    fn blocks_enclosing_locals(self) -> bool {
        self == RibKind::Item
    }
}

#[derive(Debug)]
struct LateResolutionVisitor<'a, 'res, 'ctx> {
    resolver: &'a mut Resolver<'res, 'ctx>,
    ribs: ThinVec<Rib>,
}

impl<'a, 'res, 'ctx> LateResolutionVisitor<'a, 'res, 'ctx> {
    pub fn new(resolver: &'a mut Resolver<'res, 'ctx>) -> Self {
        Self {
            resolver,
            ribs: ThinVec::new(),
        }
    }

    fn with_rib(&mut self, kind: RibKind, f: impl FnOnce(&mut Self)) {
        self.ribs.push(Rib::new(kind));
        f(self);
        self.ribs.pop();
    }

    fn resolve_fn(&mut self, fun: &Fn) {
        self.with_rib(RibKind::Item, |this| {
            if let Some(generic_params) = &fun.generic_params {
                for param in &generic_params.params {
                    let sym = param.name.value;
                    let rib = this.ribs.last_mut().expect("rib exists");
                    rib.bindings.insert(sym, Res::GenericParam(param.node_id));
                    param.visit(this);
                }
            }
            for arg in &fun.parameters {
                arg.1.visit(this);

                let sym = arg.0.value;
                let rib = this.ribs.last_mut().expect("rib exists");
                rib.bindings.insert(sym, Res::Local(arg.2));
            }
            fun.return_type.visit(this);
            if let Some(body) = &fun.body {
                body.visit(this);
            }
        });
    }

    fn resolve_assoc_items(&mut self, items: &ThinVec<AssocItem>) {
        for item in items {
            match &item.kind {
                AssocItemKind::Fn(fun) => self.resolve_fn(fun),
                AssocItemKind::Type { type_, .. } => {
                    if let Some(type_) = type_ {
                        type_.visit(self);
                    }
                }
            }
        }
    }

    fn resolve_path(&mut self, path: &Path, node_id: NodeId) -> PartialRes {
        let segments = &path.segments;
        let partial_res = if segments.len() == 1 {
            PartialRes::new(self.resolve_ident(path, segments[0].ident.value))
        } else if let Some(partial_res) = self.defer_type_relative_path(path) {
            partial_res
        } else {
            self.resolve_module_path(path)
        };
        self.resolver.res_map.insert(node_id, partial_res);

        for segment in segments {
            if let Some(generic_args) = &segment.generic_args {
                for ty in generic_args {
                    ty.visit(self);
                }
            }
        }

        partial_res
    }

    fn resolve_ident(&mut self, path: &Path, name: Symbol) -> Res {
        // Check if the symbol is a primitive type.
        if let Some(prim) = PrimTy::from_name(name) {
            return Res::PrimTy(prim);
        }

        // Check the rib stack for a binding.
        let mut locals_visible = true;
        for rib in self.ribs.iter().rev() {
            if let Some(&res) = rib.bindings.get(&name) {
                if locals_visible || !matches!(res, Res::Local(_)) {
                    return res;
                }
                break;
            }

            if rib.kind.blocks_enclosing_locals() {
                locals_visible = false;
            }
        }

        // Check if the symbol is a module-level definition.
        if let Some(res) = self.resolver.current_module().resolutions.get(&name) {
            return Res::Def(res.best_binding().def_id);
        }

        // TODO: Emit a better error message
        builders::emit_at(
            self.resolver.ctx,
            path.span,
            self.resolver.source_module_id(),
            diag::FailedToResolvePath,
            diag_params! {},
        );
        Res::Err
    }

    fn probe_ident_type(&self, name: Symbol) -> Option<Res> {
        if let Some(prim) = PrimTy::from_name(name) {
            return Some(Res::PrimTy(prim));
        }

        for rib in self.ribs.iter().rev() {
            if let Some(&res) = rib.bindings.get(&name) {
                if res.is_type_ns(self.resolver) {
                    return Some(res);
                }
                return None;
            }
        }

        if let Some(resolution) = self.resolver.current_module().resolutions.get(&name) {
            let def = resolution.best_binding().def_id;
            if self.resolver.is_type_def(def) {
                return Some(Res::Def(def));
            }
        }

        None
    }

    fn defer_type_relative_path(&mut self, path: &Path) -> Option<PartialRes> {
        let segments = &path.segments;
        if segments.len() < 2 {
            return None;
        }

        // Case 1: first segment is already a type.
        if let Some(first) = self.probe_ident_type(segments[0].ident.value) {
            return Some(PartialRes::with_unresolved_segments(
                first,
                segments.len() - 1,
            ));
        }

        // Case 2: search for module::...::Type
        for prefix_len in (1..segments.len()).rev() {
            let module_prefix = &segments[..prefix_len];
            let type_seg = &segments[prefix_len];

            let Some(resolution) = self
                .resolver
                .resolve_module_path(self.resolver.module_idx, module_prefix)
                .ok()
                .and_then(|module| {
                    self.resolver.modules[module]
                        .resolutions
                        .get(&type_seg.ident.value)
                })
            else {
                continue;
            };

            let def = resolution.best_binding().def_id;

            if !self.resolver.is_type_def(def) {
                continue;
            }

            if prefix_len + 1 == segments.len() {
                continue;
            }

            return Some(PartialRes::with_unresolved_segments(
                Res::Def(def),
                segments.len() - prefix_len - 1,
            ));
        }

        None
    }

    fn resolve_module_path(&mut self, path: &Path) -> PartialRes {
        let segments = &path.segments;
        let module_prefix = &segments[..segments.len() - 1];
        let module_node_idx = match self
            .resolver
            .resolve_module_path(self.resolver.module_idx, module_prefix)
        {
            Ok(idx) => idx,
            Err(err) => {
                match err {
                    PathError::NoParentForSuper { span } => {
                        builders::emit_at(
                            self.resolver.ctx,
                            span,
                            self.resolver.source_module_id(),
                            diag::NoParentForSuper,
                            diag_params! {},
                        );
                    }
                    PathError::ModuleNotFound { name, span } => {
                        builders::emit_at(
                            self.resolver.ctx,
                            span,
                            self.resolver.source_module_id(),
                            diag::ModuleNotFound,
                            diag_params! { name = name },
                        );
                    }
                };
                return PartialRes::new(Res::Err);
            }
        };

        let last = &segments[segments.len() - 1];
        let sym = last.ident.value;

        if let Some(res) = self.resolver.modules[module_node_idx].resolutions.get(&sym) {
            return PartialRes::new(Res::Def(res.best_binding().def_id));
        }

        let name = self
            .resolver
            .ctx
            .interner
            .lookup(last.ident.value)
            .to_string();
        builders::emit_at(
            self.resolver.ctx,
            last.span,
            self.resolver.source_module_id(),
            diag::FailedToResolveInModule,
            diag_params! {
                name = name,
                module = path_segments_to_string(
                    &segments[..segments.len() - 1],
                    self.resolver.ctx
                )
            },
        );
        PartialRes::new(Res::Err)
    }

    fn inject_self_ty(&mut self, node_id: NodeId) {
        let def_id = self.resolver.def_id_for_node(node_id).expect("resolved");
        self.inject_self_ty_from_def_id(def_id);
    }

    fn inject_self_ty_from_def_id(&mut self, def_id: DefId) {
        let self_sym = self.resolver.ctx.interner.intern("Self");
        let rib = self.ribs.last_mut().expect("rib exists");
        rib.bindings
            .insert(self_sym, Res::SelfTyAlias { alias_to: def_id });
    }
}

impl<'a, 'res, 'ctx> Visitor for LateResolutionVisitor<'a, 'res, 'ctx> {
    fn visit_item(&mut self, item: &Item) -> VisitAction {
        match &item.kind {
            // Already resolved in a past stage
            ItemKind::Import(_) | ItemKind::Module { .. } => {}
            ItemKind::Const { value, ty, .. } => {
                value.visit(self);
                ty.visit(self);
            }
            ItemKind::Fn(fun) => {
                self.resolve_fn(fun);
            }
            ItemKind::Struct {
                fields,
                items,
                generic_params,
                ..
            } => {
                self.with_rib(RibKind::Item, |this| {
                    this.inject_self_ty(item.node_id);
                    if let Some(generic_params) = generic_params {
                        for param in &generic_params.params {
                            let sym = param.name.value;
                            let rib = this.ribs.last_mut().expect("rib exists");
                            rib.bindings.insert(sym, Res::GenericParam(param.node_id));
                            param.visit(this);
                        }
                    }
                    for field in fields {
                        field.1.visit(this);
                    }
                    this.resolve_assoc_items(items);
                });
            }
            ItemKind::Trait {
                items,
                generic_params,
                ..
            } => {
                self.with_rib(RibKind::Item, |this| {
                    this.inject_self_ty(item.node_id);
                    if let Some(generic_params) = generic_params {
                        for param in &generic_params.params {
                            let sym = param.name.value;
                            let rib = this.ribs.last_mut().expect("rib exists");
                            rib.bindings.insert(sym, Res::GenericParam(param.node_id));
                            param.visit(this);
                        }
                    }
                    this.resolve_assoc_items(items);
                });
            }
            ItemKind::Impl {
                self_ty,
                trait_,
                items,
            } => {
                let self_ty_res = self.resolve_path(&self_ty.0, self_ty.1);

                self.with_rib(RibKind::Item, |this| {
                    let self_sym = this.resolver.ctx.interner.intern("Self");
                    let rib = this.ribs.last_mut().expect("rib exists");
                    match self_ty_res.full_res() {
                        Some(Res::Def(def_id)) => {
                            rib.bindings
                                .insert(self_sym, Res::SelfTyAlias { alias_to: def_id });
                        }
                        Some(res) => {
                            rib.bindings.insert(self_sym, res);
                        }
                        None => {}
                    }
                    this.resolve_path(&trait_.0, trait_.1);
                    this.resolve_assoc_items(items);
                });
            }
            ItemKind::Type {
                generic_params,
                type_,
                ..
            } => {
                self.with_rib(RibKind::Item, |this| {
                    if let Some(generic_params) = generic_params {
                        for param in &generic_params.params {
                            let sym = param.name.value;
                            let rib = this.ribs.last_mut().expect("rib exists");
                            rib.bindings.insert(sym, Res::GenericParam(param.node_id));
                            param.visit(this);
                        }
                    }
                    type_.visit(this);
                });
            }
        }

        VisitAction::SkipChildren
    }

    fn visit_stmt(&mut self, stmt: &Stmt) -> VisitAction {
        match &stmt.kind {
            StmtKind::Let {
                name, ty, value, ..
            } => {
                ty.visit(self);
                if let Some(value) = value {
                    value.visit(self);
                }

                let sym = name.value;
                let rib = self.ribs.last_mut().expect("rib exists");
                rib.bindings.insert(sym, Res::Local(stmt.node_id));
            }
            StmtKind::Expr(expr) | StmtKind::Semi(expr) => expr.visit(self),
        }

        VisitAction::SkipChildren
    }

    fn visit_expr(&mut self, expr: &Expr) -> VisitAction {
        match &expr.kind {
            ExprKind::Path(path) => {
                self.resolve_path(path, expr.node_id);
            }
            ExprKind::Literal(_) => {}
            ExprKind::Binary { left, right, .. } => {
                left.visit(self);
                right.visit(self);
            }
            ExprKind::Dereference { expr } => expr.visit(self),
            ExprKind::Reference { expr, .. } => expr.visit(self),
            ExprKind::Unary { right, .. } => right.visit(self),
            ExprKind::Range { start, end, .. } => {
                start.visit(self);
                end.visit(self);
            }
            ExprKind::Assignment {
                assignee, value, ..
            } => {
                assignee.visit(self);
                value.visit(self);
            }
            ExprKind::StructInstantiation { fields, path } => {
                self.resolve_path(path, expr.node_id);
                for (_, expr) in fields {
                    expr.visit(self);
                }
            }
            ExprKind::Array { contents, .. } => {
                for elem in contents {
                    elem.visit(self);
                }
            }
            ExprKind::FunctionCall { callee, arguments } => {
                callee.visit(self);
                arguments.visit(self);
            }
            ExprKind::MemberAccess { base, .. } => base.visit(self),
            ExprKind::Index { base, index } => {
                base.visit(self);
                index.visit(self);
            }
            ExprKind::As { expr, ty } => {
                expr.visit(self);
                ty.visit(self);
            }
            ExprKind::Tuple { elements } => {
                for elem in elements {
                    elem.visit(self);
                }
            }
            ExprKind::Block(b) => {
                self.with_rib(RibKind::Normal, |this| {
                    b.visit(this);
                });
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                condition.visit(self);
                self.with_rib(RibKind::Normal, |this| {
                    then_branch.visit(this);
                });
                if let Some(else_expr) = else_branch {
                    else_expr.visit(self);
                }
            }
            ExprKind::While { condition, body } => {
                condition.visit(self);
                self.with_rib(RibKind::Normal, |this| {
                    body.visit(this);
                });
            }
            ExprKind::Loop(b) => {
                self.with_rib(RibKind::Normal, |this| {
                    b.visit(this);
                });
            }
            ExprKind::Break(val) => {
                if let Some(expr) = val {
                    expr.visit(self);
                }
            }
            ExprKind::Return(val) => {
                if let Some(expr) = val {
                    expr.visit(self);
                }
            }
        }

        VisitAction::SkipChildren
    }

    fn visit_type(&mut self, ty: &Type) -> VisitAction {
        match &ty.kind {
            TypeKind::Symbol(path) => {
                self.resolve_path(path, ty.node_id);
            }
            TypeKind::Pointer(ty, _) => ty.visit(self),
            TypeKind::Slice(ty) => ty.visit(self),
            TypeKind::FixedArray(ty, _) => {
                ty.visit(self);
            }
            TypeKind::Function { params, ret } => {
                params.visit(self);
                ret.visit(self);
            }
            TypeKind::Tuple(elements) => {
                elements.visit(self);
            }
            TypeKind::Projection {
                base,
                trait_,
                generic_args,
                ..
            } => {
                if let Some(generic_args) = generic_args {
                    for ty in generic_args {
                        ty.visit(self);
                    }
                }
                self.resolve_path(&base.0, base.1);
                self.resolve_path(&trait_.0, trait_.1);
            }
            TypeKind::Infer => {}
            TypeKind::Never => {}
        }

        VisitAction::SkipChildren
    }
}
