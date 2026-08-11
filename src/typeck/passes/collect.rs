use fxhash::{FxHashMap, FxHashSet};
use thin_vec::ThinVec;

use super::check::{emit_ty_from_hir_error, emit_unify_error};
use crate::ast::visit::VisitAction;
use crate::diag_params;
use crate::errors::builders;
use crate::hir::{
    self, AssocItemKind, Def, DefId, DefKind, FnDecl, GenericParam, ItemKind, ModuleId, OwnerNode,
};
use crate::interner::Symbol;
use crate::span::Span;
use crate::typeck::fold::{fold_ty, res_to_def_id, resolve_scheme_with_args};
use crate::typeck::infctx::TyVarId;
use crate::typeck::types::{Scheme, Ty};
use crate::typeck::{TyVisitable, TyVisitor, Typeck, diag};

impl<'ctx, 'hir, 'res> Typeck<'ctx, 'hir, 'res> {
    pub(crate) fn collect_signatures(&mut self) {
        self.iter_owners(&mut |this, def_id, module_id, owner| {
            let Some(info) = owner.as_owner() else {
                return;
            };

            this.current_self_ty = None;

            match &info.nodes.node() {
                OwnerNode::Item(item) => match &item.kind {
                    ItemKind::Fn(fun) => {
                        let vars = this.collect_generic_params(&fun.generic_params);
                        let body = this.fn_ty(&fun.decl, module_id);
                        this.item_schemes.insert(def_id, Scheme { vars, body });
                    }
                    ItemKind::Const { ty, .. } => {
                        let ty = this
                            .ty_from_hir(ty, module_id)
                            .unwrap_or_else(|err| {
                                emit_ty_from_hir_error(&err, this.ctx);
                                Ty::Error
                            })
                            .reject_vars();
                        this.item_schemes.insert(def_id, Scheme::monomorphic(ty));
                    }
                    ItemKind::Struct {
                        fields,
                        items,
                        generic_params,
                        ..
                    } => {
                        let vars = this.collect_generic_params(generic_params);

                        let scheme = Self::adt_scheme(def_id, vars);
                        this.coherence
                            .impl_self_types
                            .insert(def_id, scheme.body.clone());
                        this.item_schemes.insert(def_id, scheme);

                        let entry = this.coherence.struct_fields.entry(def_id).or_default();
                        for (index, field) in fields.iter().enumerate() {
                            entry.insert(field.name, (field.ty.clone(), index));
                        }

                        this.register_assoc_items(def_id, items);
                    }
                    ItemKind::TypeAlias {
                        type_,
                        generic_params,
                        ..
                    } => {
                        let vars = this.collect_generic_params(generic_params);
                        let body = this.ty_from_hir(type_, module_id).unwrap_or_else(|err| {
                            emit_ty_from_hir_error(&err, this.ctx);
                            Ty::Error
                        });
                        this.item_schemes.insert(def_id, Scheme { vars, body });
                    }
                    ItemKind::Trait {
                        items,
                        generic_params,
                        ..
                    } => {
                        let vars = this.collect_generic_params(generic_params);

                        let scheme = Self::adt_scheme(def_id, vars);
                        this.coherence
                            .impl_self_types
                            .insert(def_id, scheme.body.clone());
                        this.item_schemes.insert(def_id, scheme);

                        let methods: Vec<(Symbol, DefId)> = items
                            .iter()
                            .filter_map(|&item| {
                                let def = &this.resolver.defs[item.0 as usize];
                                (def.kind == DefKind::AssocFn).then_some((def.name?, item))
                            })
                            .collect();
                        this.coherence.register_trait(def_id, methods);
                        this.register_assoc_items(def_id, items);
                    }
                    ItemKind::Impl {
                        self_ty,
                        trait_ty,
                        items,
                    } => {
                        if let Some(struct_def_id) = this.resolve_struct(self_ty.res)
                            && let Some(trait_def_id) = this.resolve_trait(trait_ty.res)
                        {
                            this.coherence
                                .impls
                                .entry((trait_def_id, struct_def_id))
                                .or_default()
                                .push(def_id);
                            this.coherence.impl_to_trait.insert(def_id, trait_def_id);
                            this.coherence
                                .struct_to_traits
                                .entry(struct_def_id)
                                .or_default()
                                .push(trait_def_id);
                        }
                        if let Some(struct_def_id) = this.resolve_struct(self_ty.res) {
                            let self_generic_args =
                                this.ty_hir_generic_args(self_ty, module_id).unwrap_or(None);
                            this.coherence
                                .impl_self_types
                                .insert(def_id, Ty::Adt(struct_def_id, self_generic_args));
                            this.coherence
                                .impl_self_ty_hir
                                .insert(def_id, self_ty.clone());
                        }

                        this.register_assoc_items(def_id, items);
                    }
                },
                OwnerNode::AssocItem(assoc) => match &assoc.kind {
                    AssocItemKind::Fn(fun) => {
                        let scheme_vars = this.collect_generic_params(&fun.generic_params);
                        let parent_def_id = this
                            .coherence
                            .assoc_to_parent
                            .get(&def_id)
                            .copied()
                            .expect("assoc item has parent");
                        this.current_self_ty =
                            this.coherence.impl_self_types.get(&parent_def_id).cloned();

                        let body = this.fn_ty(&fun.decl, module_id);
                        let scheme = this.assoc_item_scheme(parent_def_id, scheme_vars, body);
                        this.item_schemes.insert(def_id, scheme);
                    }
                    AssocItemKind::Type { type_, .. } => {
                        let parent_def_id = this
                            .coherence
                            .assoc_to_parent
                            .get(&def_id)
                            .copied()
                            .expect("assoc item has parent");
                        this.current_self_ty =
                            this.coherence.impl_self_types.get(&parent_def_id).cloned();

                        match this.resolver.def(parent_def_id).kind {
                            DefKind::Trait => {}
                            DefKind::Impl | DefKind::Struct => {
                                let type_ = type_.as_ref().expect("assoc type is concrete");
                                let body =
                                    this.ty_from_hir(type_, module_id).unwrap_or_else(|err| {
                                        emit_ty_from_hir_error(&err, this.ctx);
                                        Ty::Error
                                    });
                                // impls/structs do not yet have generic params, but act as if
                                // they did so we can reuse logic
                                let scheme =
                                    this.assoc_item_scheme(parent_def_id, ThinVec::new(), body);
                                this.item_schemes.insert(def_id, scheme);
                            }
                            _ => {
                                unreachable!("other defs cannot have assoc types");
                            }
                        }
                    }
                },
                OwnerNode::Crate => {}
            }
        });

        let errors = self.icx.take_errors();
        for err in &errors {
            emit_unify_error(err, self.resolver, self.ctx, &self.icx);
        }
    }

    fn assoc_item_scheme(
        &self,
        parent_def_id: DefId,
        mut scheme_vars: ThinVec<TyVarId>,
        body: Ty,
    ) -> Scheme {
        let parent_info = self
            .coherence
            .generic_params
            .get(&parent_def_id)
            .expect("assoc item parent has generic params");
        let parent_vars: ThinVec<TyVarId> = parent_info
            .hir_ids
            .iter()
            .map(|hir_id| {
                *self
                    .icx
                    .hir_id_to_ty_var
                    .get(hir_id)
                    .expect("parent generic param registered")
            })
            .collect();
        let parent_params: ThinVec<Ty> = parent_vars.iter().map(|&v| Ty::Var(v)).collect();
        scheme_vars = parent_vars.into_iter().chain(scheme_vars).collect();
        let body = fold_ty(&body, &mut |ty| match ty {
            Ty::Adt(id, None) if id == parent_def_id => Ty::Adt(
                id,
                (!parent_params.is_empty()).then_some(parent_params.clone()),
            ),
            t => t,
        });
        Scheme {
            vars: scheme_vars,
            body,
        }
    }

    pub(crate) fn check_type_aliases(&mut self) {
        let type_aliases: Vec<_> = self
            .krate
            .get()
            .owners
            .iter()
            .enumerate()
            .filter_map(|(i, owner)| {
                let info = owner.as_owner()?;
                let OwnerNode::Item(item) = info.nodes.node() else {
                    return None;
                };

                matches!(item.kind, ItemKind::TypeAlias { .. })
                    .then_some((DefId(i as u32), item.span))
            })
            .collect();

        let mut visited = FxHashSet::default();

        for (def_id, span) in type_aliases {
            if !visited.insert(def_id) {
                continue;
            }

            let mut in_progress: Vec<(DefId, Option<ThinVec<Ty>>)> = Vec::new();
            if self.visit_alias(def_id, def_id, &mut in_progress) {
                let module_id = self.owner_module(def_id);
                builders::emit_at(
                    self.ctx,
                    span,
                    module_id,
                    diag::RecursiveType,
                    diag_params! {},
                );
            }
        }

        let mut full_assoc_type_index = self.coherence.assoc_type_index.clone();
        for (&(_, struct_def_id), impl_def_ids) in &self.coherence.impls {
            for &impl_def_id in impl_def_ids {
                if let Some(assoc_def_ids) = self.coherence.parent_to_assoc.get(&impl_def_id) {
                    for &assoc_def_id in assoc_def_ids {
                        let def = &self.resolver.def(assoc_def_id);
                        if def.kind == DefKind::AssocType {
                            let name = def.name.expect("assoc type has name");
                            full_assoc_type_index.insert((struct_def_id, name), assoc_def_id);
                        }
                    }
                }
            }
        }

        // The resolved scheme bodies for recursive associated types are
        // Ty::Error or Ty::Projection, so walk the original HIR types instead.
        let struct_assoc_types =
            self.krate
                .get()
                .owners
                .iter()
                .enumerate()
                .filter_map(|(i, owner)| {
                    let info = owner.as_owner()?;
                    let OwnerNode::AssocItem(assoc) = info.nodes.node() else {
                        return None;
                    };
                    let AssocItemKind::Type { type_: Some(_), .. } = &assoc.kind else {
                        return None;
                    };
                    let def_id = DefId(i as u32);
                    let parent_def_id = self.coherence.assoc_to_parent.get(&def_id).copied()?;
                    let kind = self.resolver.def(parent_def_id).kind;
                    matches!(kind, DefKind::Struct | DefKind::Impl).then_some(def_id)
                });

        for def_id in struct_assoc_types {
            if !visited.insert(def_id) {
                continue;
            }

            let mut in_progress = FxHashSet::default();

            if let Some(cycle_span) = Self::visit_hir_assoc_type_alias(
                def_id,
                def_id,
                self.krate.get(),
                &full_assoc_type_index,
                &self.coherence.assoc_to_parent,
                &self.resolver.defs,
                &mut visited,
                &mut in_progress,
            ) {
                let module_id = self.owner_module(def_id);
                builders::emit_at(
                    self.ctx,
                    cycle_span,
                    module_id,
                    diag::RecursiveType,
                    diag_params! {},
                );
            }
        }
    }

    fn visit_alias(
        &self,
        current: DefId,
        start: DefId,
        in_progress: &mut Vec<(DefId, Option<ThinVec<Ty>>)>,
    ) -> bool {
        const MAX_ALIAS_EXPANSION_DEPTH: usize = 128;

        struct AliasVisitor<'a> {
            start: DefId,
            item_schemes: &'a FxHashMap<DefId, Scheme>,
            in_progress: &'a mut Vec<(DefId, Option<ThinVec<Ty>>)>,
            found_cycle: bool,
        }

        impl TyVisitor for AliasVisitor<'_> {
            fn visit_ty(&mut self, ty: &Ty) -> VisitAction {
                if self.found_cycle {
                    return VisitAction::SkipChildren;
                }

                let Ty::Alias {
                    def_id,
                    generic_args,
                } = ty
                else {
                    return VisitAction::Continue;
                };
                if *def_id == self.start
                    || self
                        .in_progress
                        .iter()
                        .any(|(d, args)| d == def_id && args == generic_args)
                    || self.in_progress.len() >= MAX_ALIAS_EXPANSION_DEPTH
                {
                    self.found_cycle = true;
                    return VisitAction::SkipChildren;
                }

                let Some(scheme) = self.item_schemes.get(def_id) else {
                    return VisitAction::SkipChildren;
                };

                self.in_progress.push((*def_id, generic_args.clone()));
                if let Some(resolved) = resolve_scheme_with_args(scheme, generic_args) {
                    resolved.visit(self);
                }
                self.in_progress.pop();

                VisitAction::SkipChildren
            }
        }

        let Some(scheme) = self.item_schemes.get(&current) else {
            return false;
        };

        in_progress.push((current, None));

        let mut visitor = AliasVisitor {
            start,
            item_schemes: &self.item_schemes,
            in_progress,
            found_cycle: false,
        };

        scheme.body.visit(&mut visitor);

        let found_cycle = visitor.found_cycle;

        in_progress.pop();

        found_cycle
    }

    #[allow(clippy::too_many_arguments)]
    fn visit_hir_assoc_type_alias(
        current: DefId,
        start: DefId,
        krate: &hir::Crate,
        assoc_type_index: &FxHashMap<(DefId, Symbol), DefId>,
        assoc_to_parent: &FxHashMap<DefId, DefId>,
        defs: &ThinVec<Def>,
        visited: &mut FxHashSet<DefId>,
        in_progress: &mut FxHashSet<DefId>,
    ) -> Option<Span> {
        let info = krate.owner(current).expect("owner exists").as_owner()?;
        let OwnerNode::AssocItem(assoc) = info.nodes.node() else {
            return None;
        };
        let AssocItemKind::Type {
            type_: Some(type_), ..
        } = &assoc.kind
        else {
            return None;
        };

        in_progress.insert(current);
        let found = Self::walk_hir_ty_for_cycles(
            type_,
            start,
            krate,
            assoc_type_index,
            assoc_to_parent,
            defs,
            visited,
            in_progress,
        );
        in_progress.remove(&current);
        found
    }

    #[allow(clippy::too_many_arguments)]
    fn walk_hir_ty_for_cycles(
        ty: &hir::Ty,
        start: DefId,
        krate: &hir::Crate,
        assoc_type_index: &FxHashMap<(DefId, Symbol), DefId>,
        assoc_to_parent: &FxHashMap<DefId, DefId>,
        defs: &ThinVec<Def>,
        visited: &mut FxHashSet<DefId>,
        in_progress: &mut FxHashSet<DefId>,
    ) -> Option<Span> {
        match &ty.kind {
            hir::TyKind::Path(qpath) => Self::walk_hir_qpath_for_cycles(
                qpath,
                start,
                krate,
                assoc_type_index,
                assoc_to_parent,
                defs,
                visited,
                in_progress,
            ),
            hir::TyKind::Ptr(inner, _) | hir::TyKind::Slice(inner) => Self::walk_hir_ty_for_cycles(
                inner,
                start,
                krate,
                assoc_type_index,
                assoc_to_parent,
                defs,
                visited,
                in_progress,
            ),
            hir::TyKind::Array(inner, _) => Self::walk_hir_ty_for_cycles(
                inner,
                start,
                krate,
                assoc_type_index,
                assoc_to_parent,
                defs,
                visited,
                in_progress,
            ),
            hir::TyKind::Fn { params, ret } => {
                for param in params {
                    if let Some(cycle_span) = Self::walk_hir_ty_for_cycles(
                        param,
                        start,
                        krate,
                        assoc_type_index,
                        assoc_to_parent,
                        defs,
                        visited,
                        in_progress,
                    ) {
                        return Some(cycle_span);
                    }
                }
                Self::walk_hir_ty_for_cycles(
                    ret,
                    start,
                    krate,
                    assoc_type_index,
                    assoc_to_parent,
                    defs,
                    visited,
                    in_progress,
                )
            }
            hir::TyKind::Tuple(elements) => {
                for element in elements {
                    if let Some(cycle_span) = Self::walk_hir_ty_for_cycles(
                        element,
                        start,
                        krate,
                        assoc_type_index,
                        assoc_to_parent,
                        defs,
                        visited,
                        in_progress,
                    ) {
                        return Some(cycle_span);
                    }
                }
                None
            }
            hir::TyKind::Error
            | hir::TyKind::PrimTy(_)
            | hir::TyKind::GenericParam(_, _)
            | hir::TyKind::Infer
            | hir::TyKind::Never => None,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn walk_hir_qpath_for_cycles(
        qpath: &hir::QPath,
        start: DefId,
        krate: &hir::Crate,
        assoc_type_index: &FxHashMap<(DefId, Symbol), DefId>,
        assoc_to_parent: &FxHashMap<DefId, DefId>,
        defs: &ThinVec<Def>,
        visited: &mut FxHashSet<DefId>,
        in_progress: &mut FxHashSet<DefId>,
    ) -> Option<Span> {
        match qpath {
            hir::QPath::TypeRelative { qself, segment } => {
                if let Some(struct_def_id) = Self::resolve_qself_to_struct(qself, defs) {
                    let name = segment.ident.value;
                    if let Some(&assoc_def_id) = assoc_type_index.get(&(struct_def_id, name)) {
                        if assoc_def_id == start || in_progress.contains(&assoc_def_id) {
                            return Some(segment.ident.span);
                        }
                        if !visited.insert(assoc_def_id) {
                            return None;
                        }
                        return Self::visit_hir_assoc_type_alias(
                            assoc_def_id,
                            start,
                            krate,
                            assoc_type_index,
                            assoc_to_parent,
                            defs,
                            visited,
                            in_progress,
                        );
                    }
                }
                Self::walk_hir_qpath_for_cycles(
                    qself,
                    start,
                    krate,
                    assoc_type_index,
                    assoc_to_parent,
                    defs,
                    visited,
                    in_progress,
                )
            }
            hir::QPath::Resolved(_, path) => {
                for segment in &path.segments {
                    if let Some(generic_args) = &segment.generic_args {
                        for arg_ty in generic_args {
                            if let Some(cycle_span) = Self::walk_hir_ty_for_cycles(
                                arg_ty,
                                start,
                                krate,
                                assoc_type_index,
                                assoc_to_parent,
                                defs,
                                visited,
                                in_progress,
                            ) {
                                return Some(cycle_span);
                            }
                        }
                    }
                }
                None
            }
        }
    }

    #[allow(clippy::match_single_binding)]
    fn resolve_qself_to_struct(qpath: &hir::QPath, defs: &ThinVec<Def>) -> Option<DefId> {
        let hir::QPath::Resolved(_, path) = qpath else {
            return None;
        };
        let def_id = res_to_def_id(path.res)?;
        (defs[def_id.0 as usize].kind == DefKind::Struct).then_some(def_id)
    }

    fn register_assoc_items(&mut self, parent_def_id: DefId, items: &[DefId]) {
        for &item_def_id in items {
            let def = &self.resolver.def(item_def_id);
            if def.kind == DefKind::AssocType
                && let Some(name) = def.name
            {
                self.coherence
                    .assoc_type_index
                    .insert((parent_def_id, name), item_def_id);
            }
            self.coherence
                .assoc_to_parent
                .insert(item_def_id, parent_def_id);
            self.coherence
                .parent_to_assoc
                .entry(parent_def_id)
                .or_default()
                .push(item_def_id);
        }
    }

    fn collect_generic_params(
        &mut self,
        generic_params: &Option<ThinVec<GenericParam>>,
    ) -> ThinVec<TyVarId> {
        generic_params
            .as_ref()
            .map(|params| {
                params
                    .iter()
                    .map(|param| {
                        let ty_var = self.icx.next_ty_var();
                        self.icx.hir_id_to_ty_var.insert(param.hir_id, ty_var);
                        ty_var
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    fn fn_ty(&mut self, decl: &FnDecl, module_id: ModuleId) -> Ty {
        let params: ThinVec<Ty> = decl
            .params
            .iter()
            .map(|param| {
                self.ty_from_hir(&param.ty, module_id)
                    .unwrap_or_else(|err| {
                        emit_ty_from_hir_error(&err, self.ctx);
                        Ty::Error
                    })
            })
            .collect();
        let ret = self
            .ty_from_hir(&decl.ret, module_id)
            .unwrap_or_else(|err| {
                emit_ty_from_hir_error(&err, self.ctx);
                Ty::Error
            })
            .into_box();
        Ty::Fn { params, ret }
    }

    fn adt_scheme(def_id: DefId, vars: ThinVec<TyVarId>) -> Scheme {
        let generic_args = if vars.is_empty() {
            None
        } else {
            Some(vars.iter().map(|&v| Ty::Var(v)).collect())
        };
        let body = Ty::Adt(def_id, generic_args);
        Scheme { vars, body }
    }
}
