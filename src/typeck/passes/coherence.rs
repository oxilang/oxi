use thin_vec::ThinVec;

use crate::diag_params;
use crate::errors::builders;
use crate::hir::{self, DefId, DefKind, HirId, ItemKind, ModuleId, OwnerNode};
use crate::interner::Symbol;
use crate::resolve::Res;
use crate::typeck::fold::{fold_ty, substitute_ty_vars};
use crate::typeck::infctx::{InferCtx, TyVarId};
use crate::typeck::types::Ty;
use crate::typeck::{Scheme, Typeck, diag};

use super::check::{emit_ty_from_hir_error, emit_unexpected_generic_args};
use fxhash::FxHashMap;

impl<'ctx, 'hir, 'res> Typeck<'ctx, 'hir, 'res> {
    pub(crate) fn check_coherence(&mut self) {
        self.iter_owners(&mut |this, def_id, module_id, owner| {
            let Some(item) = owner
                .as_owner()
                .map(|info| info.nodes.node())
                .and_then(|node| match node {
                    OwnerNode::Item(item) => Some(item),
                    _ => None,
                })
            else {
                return;
            };
            let ItemKind::Impl {
                self_ty,
                trait_ty,
                items,
            } = &item.kind
            else {
                return;
            };

            let Some(struct_def_id) = this.resolve_struct(self_ty.res) else {
                builders::emit_at(
                    this.ctx,
                    self_ty.span,
                    module_id,
                    diag::ImplExpectedPathToStruct,
                    diag_params! { type = self_ty.display(this.ctx) },
                );
                return;
            };
            let Some(trait_def_id) = this.resolve_trait(trait_ty.res) else {
                builders::emit_at(
                    this.ctx,
                    trait_ty.span,
                    module_id,
                    diag::ImplExpectedPathToTrait,
                    diag_params! { type = trait_ty.display(this.ctx) },
                );
                return;
            };

            // 1. Extract and validate trait generic args from the path
            let trait_scheme = this.item_schemes.get(&trait_def_id).cloned();
            let trait_generic_args = match this.ty_hir_generic_args(trait_ty, module_id) {
                Ok(args) => args,
                Err(err) => {
                    emit_ty_from_hir_error(&err, this.ctx);
                    return;
                }
            };

            // If no explicit generic args were provided and the trait has defaults, fill them in
            let trait_generic_args = match (&trait_scheme, &trait_generic_args) {
                (Some(scheme), None) if !scheme.vars.is_empty() => {
                    if let Some(info) = this.coherence.generic_params.get(&trait_def_id).cloned()
                        && info.defaults.iter().all(|d| d.is_some())
                    {
                        let mut subst: FxHashMap<TyVarId, Ty> = FxHashMap::default();
                        let mut args: ThinVec<Ty> = ThinVec::new();
                        for (i, default) in info.defaults.iter().enumerate() {
                            let ty = this.resolve_default_generic_arg(
                                default.as_ref().expect("default exists"),
                                module_id,
                                &subst,
                                Some((trait_def_id, struct_def_id)),
                            );
                            if let Some(&var) = this.icx.hir_id_to_ty_var.get(&info.hir_ids[i]) {
                                subst.insert(var, ty.clone());
                            }
                            args.push(ty);
                        }
                        Some(args)
                    } else {
                        emit_unexpected_generic_args(
                            this.ctx,
                            trait_ty.span,
                            module_id,
                            scheme.vars.len(),
                            0,
                        );
                        return;
                    }
                }
                (Some(scheme), Some(args)) if scheme.vars.len() != args.len() => {
                    if args.len() < scheme.vars.len() {
                        match this.coherence.generic_params.get(&trait_def_id).cloned() {
                            Some(info)
                                if info.defaults[args.len()..].iter().all(|d| d.is_some()) =>
                            {
                                let mut subst: FxHashMap<TyVarId, Ty> = FxHashMap::default();
                                let mut full_args: ThinVec<Ty> = args.clone();
                                for (i, arg) in full_args.iter().enumerate() {
                                    if let Some(&var) =
                                        this.icx.hir_id_to_ty_var.get(&info.hir_ids[i])
                                    {
                                        subst.insert(var, arg.clone());
                                    }
                                }
                                let base = full_args.len();
                                for (i, default) in info.defaults[base..].iter().enumerate() {
                                    let idx = base + i;
                                    let ty = this.resolve_default_generic_arg(
                                        default.as_ref().expect("default exists"),
                                        module_id,
                                        &subst,
                                        Some((trait_def_id, struct_def_id)),
                                    );
                                    if let Some(&var) =
                                        this.icx.hir_id_to_ty_var.get(&info.hir_ids[idx])
                                    {
                                        subst.insert(var, ty.clone());
                                    }
                                    full_args.push(ty);
                                }
                                Some(full_args)
                            }
                            _ => {
                                emit_unexpected_generic_args(
                                    this.ctx,
                                    trait_ty.span,
                                    module_id,
                                    scheme.vars.len(),
                                    args.len(),
                                );
                                return;
                            }
                        }
                    } else {
                        emit_unexpected_generic_args(
                            this.ctx,
                            trait_ty.span,
                            module_id,
                            scheme.vars.len(),
                            args.len(),
                        );
                        return;
                    }
                }
                _ => trait_generic_args,
            };

            // 2. Check for duplicate impls using resolved generic args
            let self_type_generic_args = match this.ty_hir_generic_args(self_ty, module_id) {
                Ok(args) => args,
                Err(err) => {
                    emit_ty_from_hir_error(&err, this.ctx);
                    return;
                }
            };
            let self_type = Ty::Adt(struct_def_id, self_type_generic_args);
            this.coherence
                .impl_resolved_generic_args
                .insert(def_id, trait_generic_args.clone());

            let key = (trait_def_id, struct_def_id);
            // Check for conflicts against other existing impls (exclude self)
            let is_conflicting = this.coherence.impls.get(&key).is_some_and(|existing| {
                let others: Vec<_> = existing
                    .iter()
                    .copied()
                    .filter(|&id| id.0 < def_id.0)
                    .collect();
                if others.is_empty() {
                    false
                } else {
                    this.coherence
                        .has_conflicting_impl(&others, &trait_generic_args, &self_type)
                }
            });
            if is_conflicting {
                let trait_ = this
                    .ctx
                    .interner
                    .lookup(
                        this.resolver
                            .def(trait_def_id)
                            .name
                            .expect("trait has name"),
                    )
                    .to_string();
                let strct = this
                    .ctx
                    .interner
                    .lookup(
                        this.resolver
                            .def(struct_def_id)
                            .name
                            .expect("struct has name"),
                    )
                    .to_string();
                let impl_span = this.resolver.def(def_id).span;
                builders::emit_at(
                    this.ctx,
                    impl_span,
                    module_id,
                    diag::ConflictingImplementations,
                    diag_params! { trait = trait_, struct = strct },
                );
                return;
            }

            let mut generic_subst: FxHashMap<TyVarId, Ty> = FxHashMap::default();
            if let (Some(scheme), Some(ref args)) = (trait_scheme, trait_generic_args) {
                for (&var, arg) in scheme.vars.iter().zip(args.iter()) {
                    generic_subst.insert(var, arg.clone());
                }
            }

            // 3. Signatures check
            let Some(trait_methods) = this.coherence.trait_methods.get(&trait_def_id).cloned()
            else {
                return;
            };

            let mut impl_methods: FxHashMap<Symbol, DefId> = FxHashMap::default();
            for item in items {
                impl_methods.insert(this.resolver.def(*item).name.expect("item has name"), *item);
            }

            // Build assoc type substitution
            for (name, trait_method) in trait_methods.iter() {
                let Some(impl_method) = impl_methods.get(name) else {
                    let method = this.ctx.interner.lookup(*name).to_string();
                    builders::emit_at(
                        this.ctx,
                        item.span,
                        module_id,
                        diag::MissingImplementation,
                        diag_params! { method = method },
                    );
                    continue;
                };
                let trait_sig = this.item_schemes.get(trait_method);
                let impl_sig = this.item_schemes.get(impl_method);
                if let (Some(trait_sig), Some(impl_sig)) = (trait_sig, impl_sig) {
                    let trait_sig_sub = substitute_self(&trait_sig.body, trait_def_id, &self_type);
                    let trait_sig_sub = substitute_ty_vars(&trait_sig_sub, &generic_subst);
                    let trait_sig_sub =
                        instantiate_scheme_into_icx(&mut this.icx, trait_sig, &trait_sig_sub);
                    let impl_sig_sub = instantiate_scheme_into_icx(
                        &mut this.icx,
                        impl_sig,
                        &impl_sig.body.clone(),
                    );

                    let method_span = this.resolver.def(*impl_method).span;
                    if this
                        .unify(&trait_sig_sub, &impl_sig_sub, method_span, module_id)
                        .is_err()
                    {
                        let method = this.ctx.interner.lookup(*name).to_string();
                        builders::emit_at(
                            this.ctx,
                            method_span,
                            module_id,
                            diag::SignatureMismatch,
                            diag_params! { method = method },
                        );
                    }
                }
            }
        });
    }

    pub(super) fn resolve_struct(&self, res: Res<HirId>) -> Option<DefId> {
        self.resolve_def_kind(res, DefKind::Struct)
    }

    pub(super) fn resolve_trait(&self, res: Res<HirId>) -> Option<DefId> {
        self.resolve_def_kind(res, DefKind::Trait)
    }

    fn resolve_def_kind(&self, res: Res<HirId>, kind: DefKind) -> Option<DefId> {
        let Res::Def(def_id) = res else {
            return None;
        };
        (self.resolver.def(def_id).kind == kind).then_some(def_id)
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn resolve_default_generic_arg(
        &mut self,
        default: &hir::Ty,
        module_id: ModuleId,
        subst: &FxHashMap<TyVarId, Ty>,
        self_subst: Option<(DefId, DefId)>,
    ) -> Ty {
        let mut ty = self.ty_from_hir(default, module_id).unwrap_or_else(|err| {
            emit_ty_from_hir_error(&err, self.ctx);
            Ty::Error
        });
        if !subst.is_empty() {
            ty = substitute_ty_vars(&ty, subst);
        }
        if let Some((trait_def_id, struct_def_id)) = self_subst {
            ty = substitute_self(&ty, trait_def_id, &Ty::Adt(struct_def_id, None));
        }
        self.normalize_type_alias(&ty)
    }
}

fn instantiate_scheme_into_icx(icx: &mut InferCtx, scheme: &Scheme, body: &Ty) -> Ty {
    let mut mapping: FxHashMap<TyVarId, Ty> = FxHashMap::default();
    for &v in &scheme.vars {
        mapping.insert(v, Ty::Var(icx.next_ty_var()));
    }
    if mapping.is_empty() {
        body.clone()
    } else {
        substitute_ty_vars(body, &mapping)
    }
}

fn substitute_self(ty: &Ty, from: DefId, to: &Ty) -> Ty {
    fold_ty(ty, &mut |ty| match ty {
        Ty::Adt(d, _) if d == from => to.clone(),
        ty => ty,
    })
}
