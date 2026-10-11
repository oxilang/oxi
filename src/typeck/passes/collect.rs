use thin_vec::ThinVec;

use super::check::emit_unify_error;
use crate::hir::{
    self, AssocItemKind, DefId, FnDecl, GenericParam, HirId, ItemKind, MaybeOwner, Node,
};
use crate::interner::Symbol;
use crate::typeck::fold::fold_ty;
use crate::typeck::infctx::{InferCtx, TyVarId};
use crate::typeck::types::{Scheme, Ty};
use crate::typeck::{GenericParamInfo, Typeck};

impl<'ctx, 'hir, 'res> Typeck<'ctx, 'hir, 'res> {
    pub(crate) fn collect_signatures(&mut self) {
        let mut icx = InferCtx::default();
        icx.push_level();

        for (i, owner) in self.krate.owners.iter().enumerate() {
            let def_id = DefId(i as u32);
            let MaybeOwner::Owner(info) = owner else {
                continue;
            };

            match &info.nodes.nodes[0].node {
                Node::Item(item) => match &item.kind {
                    ItemKind::Fn(fun) => {
                        let (vars, hir_ids, defaults) =
                            Self::collect_generic_params(&mut icx, &fun.generic_params);
                        if !hir_ids.is_empty() {
                            self.coherence
                                .generic_params
                                .insert(def_id, GenericParamInfo { hir_ids, defaults });
                        }
                        let body = self.fn_ty(&mut icx, &fun.decl);
                        self.item_schemes.insert(def_id, Scheme { vars, body });
                    }
                    ItemKind::Const { ty, .. } => {
                        let ty = Ty::from_hir(&mut icx, ty).reject_vars();
                        self.item_schemes.insert(def_id, Scheme::monomorphic(ty));
                    }
                    ItemKind::Struct {
                        fields,
                        items,
                        generic_params,
                        ..
                    } => {
                        let (vars, hir_ids, defaults) =
                            Self::collect_generic_params(&mut icx, generic_params);
                        self.coherence
                            .generic_params
                            .insert(def_id, GenericParamInfo { hir_ids, defaults });

                        let scheme = Self::adt_scheme(def_id, vars);
                        self.item_schemes.insert(def_id, scheme);

                        let entry = self.coherence.struct_fields.entry(def_id).or_default();
                        for (index, field) in fields.iter().enumerate() {
                            entry.insert(field.name, (field.ty.clone(), index));
                        }

                        for &item_def_id in items {
                            self.coherence.assoc_to_parent.insert(item_def_id, def_id);
                        }
                    }
                    ItemKind::Trait {
                        items,
                        generic_params,
                        ..
                    } => {
                        let (vars, hir_ids, defaults) =
                            Self::collect_generic_params(&mut icx, generic_params);
                        self.coherence
                            .generic_params
                            .insert(def_id, GenericParamInfo { hir_ids, defaults });

                        let scheme = Self::adt_scheme(def_id, vars);
                        self.item_schemes.insert(def_id, scheme);

                        let methods: Vec<(Symbol, DefId)> = items
                            .iter()
                            .filter_map(|&item| {
                                self.resolver.defs[item.0 as usize]
                                    .name
                                    .map(|name| (name, item))
                            })
                            .collect();
                        self.coherence.register_trait(def_id, methods);

                        for &item_def_id in items {
                            self.coherence.assoc_to_parent.insert(item_def_id, def_id);
                        }
                    }
                    ItemKind::Impl { items, .. } => {
                        self.coherence.generic_params.insert(
                            def_id,
                            GenericParamInfo {
                                hir_ids: Vec::new(),
                                defaults: ThinVec::new(),
                            },
                        );

                        for &item_def_id in items {
                            self.coherence.assoc_to_parent.insert(item_def_id, def_id);
                        }
                    }
                },
                Node::AssocItem(assoc) => {
                    let AssocItemKind::Fn(fun) = &assoc.kind;
                    let (mut scheme_vars, hir_ids, defaults) =
                        Self::collect_generic_params(&mut icx, &fun.generic_params);

                    let parent_def_id = self
                        .coherence
                        .assoc_to_parent
                        .get(&def_id)
                        .expect("assoc item has parent");
                    let parent_info = self
                        .coherence
                        .generic_params
                        .get(parent_def_id)
                        .expect("assoc item parent has generic params");
                    let parent_vars: ThinVec<TyVarId> = parent_info
                        .hir_ids
                        .iter()
                        .map(|hir_id| {
                            *icx.hir_id_to_ty_var
                                .get(hir_id)
                                .expect("parent generic param registered")
                        })
                        .collect();
                    let parent_args: ThinVec<Ty> =
                        parent_vars.iter().map(|&v| Ty::Var(v)).collect();
                    scheme_vars = parent_vars.into_iter().chain(scheme_vars).collect();
                    let body = self.fn_ty(&mut icx, &fun.decl);
                    let body = fold_ty(&body, &mut |ty| match ty {
                        Ty::Adt(id, None) if id == *parent_def_id => {
                            Ty::Adt(id, (!parent_args.is_empty()).then_some(parent_args.clone()))
                        }
                        t => t,
                    });
                    self.item_schemes.insert(
                        def_id,
                        Scheme {
                            vars: scheme_vars,
                            body,
                        },
                    );
                    if !hir_ids.is_empty() {
                        self.coherence
                            .generic_params
                            .insert(def_id, GenericParamInfo { hir_ids, defaults });
                    }
                }
                _ => {}
            }
        }

        for err in &icx.errors {
            emit_unify_error(err, self.resolver, self.ctx, &icx);
        }
    }

    fn collect_generic_params(
        icx: &mut InferCtx,
        generic_params: &Option<ThinVec<GenericParam>>,
    ) -> (ThinVec<TyVarId>, Vec<HirId>, ThinVec<Option<hir::Ty>>) {
        generic_params
            .as_ref()
            .map(|params| {
                params
                    .iter()
                    .map(|param| {
                        let ty_var = icx.next_ty_var();
                        icx.hir_id_to_ty_var.insert(param.hir_id, ty_var);
                        (ty_var, param.hir_id, param.default.clone())
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    fn fn_ty(&self, icx: &mut InferCtx, decl: &FnDecl) -> Ty {
        let params: ThinVec<Ty> = decl
            .params
            .iter()
            .map(|param| Ty::from_hir(icx, param))
            .collect();
        let ret = Ty::from_hir(icx, &decl.ret).into_box();
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
