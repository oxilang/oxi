use thin_vec::ThinVec;

use crate::diag_params;
use crate::errors::builders;
use crate::hir::{DefId, DefKind, HirId, ItemKind, MaybeOwner, ModuleId, Node};
use crate::interner::Symbol;
use crate::resolve::Res;
use crate::typeck::fold::{fold_ty, substitute_ty_vars};
use crate::typeck::infctx::{InferCtx, TyVarId};
use crate::typeck::types::Ty;
use crate::typeck::unify::unify;
use crate::typeck::{Typeck, diag};
use fxhash::FxHashMap;

impl<'ctx, 'hir, 'res> Typeck<'ctx, 'hir, 'res> {
    pub(crate) fn check_coherence(&mut self) {
        let mut icx = InferCtx::default();
        icx.push_level();

        for (i, owner) in self.krate.owners.iter().enumerate() {
            let def_id = DefId(i as u32);
            let MaybeOwner::Owner(info) = owner else {
                continue;
            };
            let Node::Item(item) = &info.nodes.nodes[0].node else {
                continue;
            };
            let ItemKind::Impl {
                self_ty,
                trait_ty,
                items,
            } = &item.kind
            else {
                continue;
            };

            let impl_module = self
                .resolver
                .def_to_module
                .get(&def_id)
                .copied()
                .unwrap_or(ModuleId(0));

            let Some(struct_def_id) = self.resolve_struct(self_ty.res) else {
                builders::emit_at(
                    self.ctx,
                    self_ty.span,
                    impl_module,
                    diag::ImplExpectedPathToStruct,
                    diag_params! { type = self_ty.display(self.ctx) },
                );
                continue;
            };
            let Some(trait_def_id) = self.resolve_trait(trait_ty.res) else {
                builders::emit_at(
                    self.ctx,
                    trait_ty.span,
                    impl_module,
                    diag::ImplExpectedPathToTrait,
                    diag_params! { type = trait_ty.display(self.ctx) },
                );
                continue;
            };

            // 1. Extract and validate trait generic args from the path
            let trait_scheme = self.item_schemes.get(&trait_def_id);
            let trait_generic_args = Ty::hir_generic_args(&mut icx, trait_ty);

            if let Some(scheme) = trait_scheme
                && !scheme.vars.is_empty()
                && let Some(info) = self.coherence.generic_params.get(&trait_def_id)
            {
                for &hir_id in &info.hir_ids {
                    if !icx.hir_id_to_ty_var.contains_key(&hir_id) {
                        let var = icx.next_ty_var();
                        icx.hir_id_to_ty_var.insert(hir_id, var);
                    }
                }
            }

            // If no explicit generic args were provided and the trait has defaults, fill them in
            let trait_generic_args = match (trait_scheme, &trait_generic_args) {
                (Some(scheme), None) if !scheme.vars.is_empty() => {
                    if let Some(info) = self.coherence.generic_params.get(&trait_def_id)
                        && info.defaults.iter().all(|d| d.is_some())
                    {
                        let mut subst: FxHashMap<TyVarId, Ty> = FxHashMap::default();
                        let mut args: ThinVec<Ty> = ThinVec::new();
                        for (i, default) in info.defaults.iter().enumerate() {
                            let mut ty =
                                Ty::from_hir(&mut icx, default.as_ref().expect("default exists"));
                            if !subst.is_empty() {
                                ty = substitute_ty_vars(&ty, &subst);
                            }
                            ty = substitute_self(&ty, trait_def_id, struct_def_id);
                            if let Some(&var) = icx.hir_id_to_ty_var.get(&info.hir_ids[i]) {
                                subst.insert(var, ty.clone());
                            }
                            args.push(ty);
                        }
                        Some(args)
                    } else {
                        let provided_args_len = 0;
                        builders::emit_at(
                            self.ctx,
                            trait_ty.span,
                            impl_module,
                            diag::UnexpectedGenericArgs,
                            diag_params! {
                                expected = scheme.vars.len(),
                                s = if scheme.vars.len() == 1 { "" } else { "s" },
                                found = provided_args_len
                            },
                        );
                        continue;
                    }
                }
                (Some(scheme), Some(args)) if scheme.vars.len() != args.len() => {
                    if args.len() < scheme.vars.len() {
                        match self.coherence.generic_params.get(&trait_def_id) {
                            Some(info)
                                if info.defaults[args.len()..].iter().all(|d| d.is_some()) =>
                            {
                                let mut subst: FxHashMap<TyVarId, Ty> = FxHashMap::default();
                                let mut full_args: ThinVec<Ty> = args.clone();
                                for (i, arg) in full_args.iter().enumerate() {
                                    if let Some(&var) = icx.hir_id_to_ty_var.get(&info.hir_ids[i]) {
                                        subst.insert(var, arg.clone());
                                    }
                                }
                                for (i, default) in
                                    info.defaults[full_args.len()..].iter().enumerate()
                                {
                                    let idx = full_args.len() + i;
                                    let mut ty = Ty::from_hir(
                                        &mut icx,
                                        default.as_ref().expect("default exists"),
                                    );
                                    if !subst.is_empty() {
                                        ty = substitute_ty_vars(&ty, &subst);
                                    }
                                    ty = substitute_self(&ty, trait_def_id, struct_def_id);
                                    if let Some(&var) = icx.hir_id_to_ty_var.get(&info.hir_ids[idx])
                                    {
                                        subst.insert(var, ty.clone());
                                    }
                                    full_args.push(ty);
                                }
                                Some(full_args)
                            }
                            _ => {
                                let provided_args_len = args.len();
                                builders::emit_at(
                                    self.ctx,
                                    trait_ty.span,
                                    impl_module,
                                    diag::UnexpectedGenericArgs,
                                    diag_params! {
                                        expected = scheme.vars.len(),
                                        s = if scheme.vars.len() == 1 { "" } else { "s" },
                                        found = provided_args_len
                                    },
                                );
                                continue;
                            }
                        }
                    } else {
                        let provided_args_len = args.len();
                        builders::emit_at(
                            self.ctx,
                            trait_ty.span,
                            impl_module,
                            diag::UnexpectedGenericArgs,
                            diag_params! {
                                expected = scheme.vars.len(),
                                s = if scheme.vars.len() == 1 { "" } else { "s" },
                                found = provided_args_len
                            },
                        );
                        continue;
                    }
                }
                _ => trait_generic_args,
            };

            // 2. Check for duplicate impls using resolved generic args
            self.coherence
                .impl_resolved_generic_args
                .insert(def_id, trait_generic_args.clone());

            let key = (trait_def_id, struct_def_id);
            let is_conflicting = self.coherence.impls.get(&key).is_some_and(|existing| {
                self.coherence
                    .has_conflicting_impl(existing, &trait_generic_args)
            });
            if is_conflicting {
                let trait_ = self
                    .ctx
                    .interner
                    .lookup(
                        self.resolver.defs[trait_def_id.0 as usize]
                            .name
                            .expect("trait has name"),
                    )
                    .to_string();
                let strct = self
                    .ctx
                    .interner
                    .lookup(
                        self.resolver.defs[struct_def_id.0 as usize]
                            .name
                            .expect("struct has name"),
                    )
                    .to_string();
                let impl_span = self.resolver.defs[def_id.0 as usize].span;
                builders::emit_at(
                    self.ctx,
                    impl_span,
                    impl_module,
                    diag::ConflictingImplementations,
                    diag_params! { trait = trait_, struct = strct },
                );
                continue;
            }
            self.coherence.impls.entry(key).or_default().push(def_id);

            let mut generic_subst: FxHashMap<TyVarId, Ty> = FxHashMap::default();
            if let (Some(scheme), Some(ref args)) = (trait_scheme, trait_generic_args) {
                for (&var, arg) in scheme.vars.iter().zip(args.iter()) {
                    generic_subst.insert(var, arg.clone());
                }
            }

            // 3. Signatures check
            let Some(trait_methods) = self.coherence.trait_methods.get(&trait_def_id) else {
                continue;
            };

            let mut impl_methods: FxHashMap<Symbol, DefId> = FxHashMap::default();
            for item in items {
                impl_methods.insert(
                    self.resolver.defs[item.0 as usize]
                        .name
                        .expect("item has name"),
                    *item,
                );
            }

            for (name, trait_method) in trait_methods.iter() {
                let Some(impl_method) = impl_methods.get(name) else {
                    let method = self.ctx.interner.lookup(*name).to_string();
                    builders::emit_at(
                        self.ctx,
                        item.span,
                        impl_module,
                        diag::MissingImplementation,
                        diag_params! { method = method },
                    );
                    continue;
                };
                let trait_sig = self.item_schemes.get(trait_method);
                let impl_sig = self.item_schemes.get(impl_method);
                if let (Some(trait_sig), Some(impl_sig)) = (trait_sig, impl_sig) {
                    let trait_sig_sub =
                        substitute_self(&trait_sig.body, trait_def_id, struct_def_id);
                    let trait_sig_sub = substitute_ty_vars(&trait_sig_sub, &generic_subst);

                    let method_span = self.resolver.defs[impl_method.0 as usize].span;
                    if unify(
                        &mut icx,
                        &trait_sig_sub,
                        &impl_sig.body,
                        method_span,
                        impl_module,
                    )
                    .is_err()
                    {
                        let method = self.ctx.interner.lookup(*name).to_string();
                        builders::emit_at(
                            self.ctx,
                            method_span,
                            impl_module,
                            diag::SignatureMismatch,
                            diag_params! { method = method },
                        );
                    }
                }
            }
        }
    }

    fn resolve_struct(&self, res: Res<HirId>) -> Option<DefId> {
        let Res::Def(def_id) = res else {
            return None;
        };
        match self.resolver.defs[def_id.0 as usize].kind {
            DefKind::Struct => Some(def_id),
            _ => None,
        }
    }

    fn resolve_trait(&self, res: Res<HirId>) -> Option<DefId> {
        let Res::Def(def_id) = res else {
            return None;
        };
        match self.resolver.defs[def_id.0 as usize].kind {
            DefKind::Trait => Some(def_id),
            _ => None,
        }
    }
}

fn substitute_self(ty: &Ty, from: DefId, to: DefId) -> Ty {
    fold_ty(ty, &mut |ty| match ty {
        Ty::Adt(d, generics) if d == from => Ty::Adt(to, generics),
        ty => ty,
    })
}
