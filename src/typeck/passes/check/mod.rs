mod call;

use std::cmp::Ordering;

use thin_vec::ThinVec;

use crate::ast::{Ident, Literal, Mutability};
use crate::context::Ctx;
use crate::diag_params;
use crate::errors::builders;
use crate::hir::{
    self, AssocItemKind, BinOp, Block, Body, DefId, DefKind, Expr, ExprKind, FloatTy, FnDecl,
    HirId, IntTy, ItemKind, ModuleId, OwnerNode, PrimTy, QPath, Stmt, StmtKind, UintTy, UnOp,
};
use crate::interner::{Interner, Symbol};
use crate::resolve::{Res, ResolverOutputs};
use crate::span::Span;
use crate::typeck::env::ScopeEnv;
use crate::typeck::fold::{
    expand_type_alias, fold_ty, resolve_scheme_with_args, substitute_ty_vars,
    try_expand_type_alias, try_fold_ty,
};
use crate::typeck::infctx::{InferCtx, TyVarSource};
use crate::typeck::types::{Scheme, Ty, TyFromHirError, TyFromHirResult};
use crate::typeck::unify::{OrPushErr, UnifyError};
use crate::typeck::{Adjustment, AssocTypesMap, MemberRes, TyVarId, Typeck, diag};
use fxhash::{FxHashMap, FxHashSet};

// Labels aren't supported yet, so early returns are only checked for loops. AST Validation should
// catch uses of `break` outside of loops
#[derive(Debug)]
struct BlockTyRes {
    tail: Ty,
    early: Option<Ty>,
}

enum StructInitDef {
    /// `def` is a plain struct; no expansion is needed
    Struct,
    /// `def` was a type alias expanded to the underlying struct def and its
    /// fully-instantiated generic args
    Expanded(DefId, ThinVec<Ty>),
    /// Expansion failed; an error has been emitted
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ProjectionRecKey {
    trait_def_id: DefId,
    assoc_def_id: DefId,
    self_ty: Ty,
    trait_generic_args: Option<ThinVec<Ty>>,
    generic_args: Option<ThinVec<Ty>>,
}

impl ProjectionRecKey {
    pub fn new(
        trait_def_id: DefId,
        assoc_def_id: DefId,
        self_ty: &Ty,
        trait_generic_args: &Option<ThinVec<Ty>>,
        generic_args: &Option<ThinVec<Ty>>,
    ) -> Self {
        Self {
            trait_def_id,
            assoc_def_id,
            self_ty: self_ty.clone(),
            trait_generic_args: trait_generic_args.clone(),
            generic_args: generic_args.clone(),
        }
    }
}

fn tail_span(expr: &Expr) -> Span {
    match &expr.kind {
        ExprKind::Block(block) => block
            .stmts
            .last()
            .and_then(|stmt| match &stmt.kind {
                StmtKind::Expr(expr) => Some(expr.span),
                _ => None,
            })
            .unwrap_or(expr.span),
        _ => expr.span,
    }
}

impl<'ctx, 'hir, 'res> Typeck<'ctx, 'hir, 'res> {
    pub(crate) fn check_bodies(&mut self) {
        let mut node_types: FxHashMap<HirId, Ty> = FxHashMap::default();
        let mut member_res: FxHashMap<HirId, MemberRes> = FxHashMap::default();
        let mut local_schemes: FxHashMap<HirId, Scheme> = FxHashMap::default();
        let mut adjustments: FxHashMap<HirId, Vec<Adjustment>> = FxHashMap::default();

        self.with_owners(|this, owners| {
            let owners = owners
                .into_iter()
                .enumerate()
                .map(|(i, owner)| {
                    let def_id = DefId(i as u32);
                    let module_id = this.owner_module(def_id);
                    (def_id, owner, module_id)
                })
                .collect::<Vec<_>>();

            let mut checker = BodyChecker {
                typeck: this,
                node_types: &mut node_types,
                member_res: &mut member_res,
                local_schemes: &mut local_schemes,
                adjustments: &mut adjustments,
                env: ScopeEnv::new(),
                module_id: ModuleId(0),
                current_assoc_types: FxHashMap::default(),
            };

            for (def_id, owner, module_id) in owners.iter() {
                checker.module_id = *module_id;
                checker.typeck.current_self_ty = None;

                let Some(info) = owner.as_owner() else {
                    continue;
                };

                match &info.nodes.node() {
                    OwnerNode::Item(item) => match &item.kind {
                        ItemKind::Fn(fun) => {
                            checker.current_assoc_types = FxHashMap::default();
                            if let Some(body_id) = fun.body_id
                                && let Some(body) = info.nodes.body(body_id)
                            {
                                checker.check_fn_body(&fun.decl, body);
                            }
                        }
                        ItemKind::Const { ty, body_id, .. } => {
                            checker.current_assoc_types = FxHashMap::default();
                            if let Some(body_id) = body_id
                                && let Some(body) = info.nodes.body(*body_id)
                            {
                                checker.check_const_body(ty, body);
                            }
                        }
                        _ => {}
                    },
                    OwnerNode::AssocItem(assoc) => match &assoc.kind {
                        AssocItemKind::Fn(fun) => {
                            let parent_def_id = checker
                                .typeck
                                .coherence
                                .assoc_to_parent
                                .get(def_id)
                                .copied()
                                .expect("assoc item has parent");
                            checker.current_assoc_types =
                                checker.typeck.compute_assoc_types(parent_def_id);
                            checker.set_self_ty_for_parent(parent_def_id);
                            if let Some(body_id) = fun.body_id
                                && let Some(body) = info.nodes.body(body_id)
                            {
                                checker.check_fn_body(&fun.decl, body);
                            }
                        }
                        AssocItemKind::Type { .. } => {
                            let parent_def_id = checker
                                .typeck
                                .coherence
                                .assoc_to_parent
                                .get(def_id)
                                .copied()
                                .expect("assoc item has parent");
                            checker.current_assoc_types =
                                checker.typeck.compute_assoc_types(parent_def_id);
                            checker.set_self_ty_for_parent(parent_def_id);
                        }
                    },
                    OwnerNode::Crate => {}
                }
            }

            owners.into_iter().map(|(_, owner, _)| owner).collect()
        });

        let int_ids = self.icx.vars_with_source(TyVarSource::IntLit);
        let i32_ty = Ty::Prim(PrimTy::Int(IntTy::I32));
        for var in int_ids {
            if self.icx.is_bound(var) {
                continue;
            }
            let var_span = self.icx.ty_var_span(var).unwrap_or(Span::new(0, 0));
            let var_module = self.icx.ty_var_module(var);
            self.unify(&Ty::Var(var), &i32_ty, var_span, var_module)
                .or_push_err(&mut self.icx);
        }
        let float_ids = self.icx.vars_with_source(TyVarSource::FloatLit);
        let f64_ty = Ty::Prim(PrimTy::Float(FloatTy::F64));
        for var in float_ids {
            if self.icx.is_bound(var) {
                continue;
            }
            let var_span = self.icx.ty_var_span(var).unwrap_or(Span::new(0, 0));
            let var_module = self.icx.ty_var_module(var);
            self.unify(&Ty::Var(var), &f64_ty, var_span, var_module)
                .or_push_err(&mut self.icx);
        }

        let empty_array_ids = self.icx.vars_with_source(TyVarSource::EmptyArray);
        for var in empty_array_ids {
            if self.icx.is_bound(var) {
                continue;
            }
            let var_span = self.icx.ty_var_span(var).unwrap_or(Span::new(0, 0));
            let var_module = self.icx.ty_var_module(var);
            builders::emit_at(
                self.ctx,
                var_span,
                var_module,
                diag::InferEmptyArray,
                diag_params! {},
            )
        }

        let generic_defaults = std::mem::take(&mut self.icx.generic_defaults);
        for (var, default_ty) in generic_defaults {
            if self.icx.is_bound(var) {
                continue;
            }
            let span = self.icx.ty_var_span(var).unwrap_or(Span::new(0, 0));
            let module_id = self.icx.ty_var_module(var);
            self.unify(&Ty::Var(var), &default_ty, span, module_id)
                .or_push_err(&mut self.icx);
        }

        let resolved: FxHashMap<HirId, Ty> = node_types
            .iter()
            .map(|(&id, ty)| {
                let mut ty = self.icx.resolve(ty);
                if let Ty::Adt(def_id, None) = &ty {
                    let info = self.coherence.generic_params.get(def_id).cloned();
                    if let Some(info) = info
                        && !info.hir_ids.is_empty()
                        && info.defaults.iter().all(|d| d.is_some())
                    {
                        let mut subst: FxHashMap<TyVarId, Ty> = FxHashMap::default();
                        let mut args: ThinVec<Ty> = ThinVec::new();
                        for (i, default) in info.defaults.iter().enumerate() {
                            let module_id = self.owner_module(*def_id);
                            let default_ty = self.resolve_default_generic_arg(
                                default.as_ref().expect("default exists"),
                                module_id,
                                &subst,
                                None,
                            );
                            if let Some(&var) = self.icx.hir_id_to_ty_var.get(&info.hir_ids[i]) {
                                subst.insert(var, default_ty.clone());
                            }
                            args.push(default_ty);
                        }
                        if !args.iter().any(|t| t.is_error()) {
                            let mut unresolved = ThinVec::new();
                            self.icx
                                .vars_in(&Ty::Adt(*def_id, Some(args.clone())), &mut unresolved);
                            if unresolved.is_empty() {
                                ty = Ty::Adt(*def_id, Some(args));
                            }
                        }
                    }
                }
                (id, ty)
            })
            .collect();

        self.node_types.extend(resolved);
        self.member_res.extend(member_res);
        self.adjustments.extend(adjustments);

        let errors = self.icx.take_errors();
        for err in &errors {
            emit_unify_error(err, self.resolver, self.ctx, &self.icx);
        }
    }

    fn impl_trait_def_id(&self, impl_def_id: DefId) -> Option<DefId> {
        self.coherence.impl_to_trait.get(&impl_def_id).copied()
    }

    pub(crate) fn compute_assoc_types(&mut self, parent_def_id: DefId) -> AssocTypesMap {
        if let Some(cached) = self.coherence.assoc_types_cache.get(&parent_def_id) {
            return cached.clone();
        }
        let mut assoc_types: AssocTypesMap = FxHashMap::default();
        if self.resolver.def(parent_def_id).kind == DefKind::Impl
            && let Some(item_ids) = self.coherence.parent_to_assoc.get(&parent_def_id)
            && let Some(trait_def_id) = self.impl_trait_def_id(parent_def_id)
        {
            for &item_def_id in item_ids {
                let def = self.resolver.def(item_def_id);
                if def.kind == DefKind::AssocType
                    && let Some(name) = def.name
                    && let Some(scheme) = self.item_schemes.get(&item_def_id)
                {
                    assoc_types.insert((trait_def_id, name), scheme.body.clone());
                }
            }
        }
        self.coherence
            .assoc_types_cache
            .insert(parent_def_id, assoc_types.clone());
        assoc_types
    }

    pub(crate) fn normalize_type_alias(&mut self, ty: &Ty) -> Ty {
        self.normalize_assoc_projections_inner(ty, &mut FxHashSet::default(), &mut Vec::new())
    }

    fn normalize_assoc_projections_inner(
        &mut self,
        ty: &Ty,
        aliases_in_progress: &mut FxHashSet<DefId>,
        projections_in_progress: &mut Vec<ProjectionRecKey>,
    ) -> Ty {
        fold_ty(ty, &mut |ty| match &ty {
            Ty::Alias {
                def_id,
                generic_args,
            } => expand_type_alias(
                *def_id,
                generic_args,
                aliases_in_progress,
                |aliases_in_progress, def_id, generic_args| match self.item_schemes.get(&def_id) {
                    Some(scheme) => match resolve_scheme_with_args(scheme, generic_args) {
                        Some(resolved) => self.normalize_assoc_projections_inner(
                            &resolved,
                            aliases_in_progress,
                            projections_in_progress,
                        ),
                        None => Ty::Alias {
                            def_id,
                            generic_args: generic_args.clone(),
                        },
                    },
                    None => Ty::Alias {
                        def_id,
                        generic_args: generic_args.clone(),
                    },
                },
            ),
            Ty::Projection {
                trait_def_id,
                assoc_def_id,
                self_ty,
                generic_args,
                trait_generic_args,
            } => {
                if let Some(args) = generic_args
                    && !args.is_empty()
                {
                    return ty;
                }
                if let Some(name) = self.resolver.def(*assoc_def_id).name
                    && let Ty::Adt(self_def_id, self_generic_args) = self_ty.as_ref()
                    && let Some(impl_def_ids) =
                        self.coherence.impls.get(&(*trait_def_id, *self_def_id))
                {
                    let target_self_ty = Ty::Adt(*self_def_id, self_generic_args.clone());
                    let matching = self
                        .coherence
                        .impls_matching_self(impl_def_ids, &target_self_ty);
                    if let Some(impl_def_id) =
                        self.impl_matching_trait_args(&matching, trait_generic_args)
                    {
                        let key = ProjectionRecKey::new(
                            *trait_def_id,
                            *assoc_def_id,
                            self_ty.as_ref(),
                            trait_generic_args,
                            generic_args,
                        );
                        if !projections_in_progress.contains(&key) {
                            projections_in_progress.push(key.clone());
                            let assoc_types = self.compute_assoc_types(impl_def_id);
                            let concrete = assoc_types.get(&(*trait_def_id, name));
                            if let Some(concrete) = concrete {
                                let normalized = self.normalize_assoc_projections_inner(
                                    concrete,
                                    aliases_in_progress,
                                    projections_in_progress,
                                );
                                projections_in_progress.retain(|k| k != &key);
                                return normalized;
                            }
                            projections_in_progress.retain(|k| k != &key);
                        }
                    }
                }
                ty
            }
            ty => ty.clone(),
        })
    }

    fn impl_matching_trait_args(
        &self,
        matching: &[DefId],
        trait_generic_args: &Option<ThinVec<Ty>>,
    ) -> Option<DefId> {
        match trait_generic_args {
            Some(args) => {
                let mut candidates = matching.iter().copied().filter(|impl_id| {
                    self.coherence
                        .impl_resolved_generic_args
                        .get(impl_id)
                        .cloned()
                        .flatten()
                        == Some(args.clone())
                });
                match (candidates.next(), candidates.next()) {
                    (Some(first), None) => Some(first),
                    _ => None,
                }
            }
            None if matching.len() == 1 => Some(matching[0]),
            None => None,
        }
    }
}

#[allow(clippy::type_complexity)]
struct BodyChecker<'a, 'ctx, 'hir, 'res> {
    typeck: &'a mut Typeck<'ctx, 'hir, 'res>,
    module_id: ModuleId,

    node_types: &'a mut FxHashMap<HirId, Ty>,
    member_res: &'a mut FxHashMap<HirId, MemberRes>,
    local_schemes: &'a mut FxHashMap<HirId, Scheme>,
    adjustments: &'a mut FxHashMap<HirId, Vec<Adjustment>>,
    env: ScopeEnv,
    current_assoc_types: FxHashMap<(DefId, Symbol), Ty>,
}

impl<'a, 'ctx, 'hir, 'res> BodyChecker<'a, 'ctx, 'hir, 'res> {
    fn set_self_ty_for_parent(&mut self, parent_def_id: DefId) {
        self.typeck.current_self_ty = self.current_self_ty_for_parent(parent_def_id);
    }

    fn current_self_ty_for_parent(&mut self, parent_def_id: DefId) -> Option<Ty> {
        match self.typeck.resolver.def(parent_def_id).kind {
            // For a struct or trait, `Self` is that entity instantiated with its
            // own generic params, freshly registered in the active icx
            DefKind::Struct | DefKind::Trait => {
                let info = self.typeck.coherence.generic_params.get(&parent_def_id);
                let generic_args = info.filter(|info| !info.hir_ids.is_empty()).map(|info| {
                    info.hir_ids
                        .iter()
                        .map(|hir_id| {
                            let var = self
                                .typeck
                                .icx
                                .hir_id_to_ty_var
                                .get(hir_id)
                                .copied()
                                .expect("parent generic param registered");
                            Ty::Var(var)
                        })
                        .collect()
                });
                Some(Ty::Adt(parent_def_id, generic_args))
            }
            // For an impl, re-infer the declared self path through the active
            // icx so generic references resolve to body-inference vars
            DefKind::Impl => {
                let path = self
                    .typeck
                    .coherence
                    .impl_self_ty_hir
                    .get(&parent_def_id)?
                    .clone();
                let generic_args = self
                    .typeck
                    .ty_hir_generic_args(&path, self.module_id)
                    .ok()?;
                let Res::Def(struct_def_id) = path.res else {
                    return None;
                };
                Some(Ty::Adt(struct_def_id, generic_args))
            }
            _ => self
                .typeck
                .coherence
                .impl_self_types
                .get(&parent_def_id)
                .cloned(),
        }
    }

    fn try_ty_from_hir_resolved(&mut self, hir_ty: &hir::Ty) -> TyFromHirResult<Ty> {
        let ty = self.typeck.ty_from_hir(hir_ty, self.module_id)?;
        self.normalize_aliases(ty, hir_ty.span)
    }

    fn ty_from_hir_resolved(&mut self, hir_ty: &hir::Ty) -> Ty {
        match self.try_ty_from_hir_resolved(hir_ty) {
            Ok(ty) => ty,
            Err(err) => {
                self.report_ty_from_hir_error(err);
                Ty::Error
            }
        }
    }

    fn report_ty_from_hir_error(&mut self, err: TyFromHirError) {
        emit_ty_from_hir_error(&err, self.typeck.ctx);
    }

    fn normalize_aliases(&mut self, ty: Ty, span: Span) -> TyFromHirResult<Ty> {
        self.normalize_aliases_inner(ty, span, &mut FxHashSet::default(), &mut Vec::new())
    }

    fn normalize_aliases_inner(
        &mut self,
        ty: Ty,
        span: Span,
        in_progress: &mut FxHashSet<DefId>,
        projections_in_progress: &mut Vec<ProjectionRecKey>,
    ) -> TyFromHirResult<Ty> {
        try_fold_ty(&ty, &mut |ty| match ty {
            Ty::Alias {
                def_id,
                generic_args,
            } => try_expand_type_alias(
                def_id,
                &generic_args,
                in_progress,
                |in_progress, def_id, generic_args| match self.typeck.item_schemes.get(&def_id) {
                    Some(scheme) => match resolve_scheme_with_args(scheme, generic_args) {
                        Some(resolved) => self.normalize_aliases_inner(
                            resolved,
                            span,
                            in_progress,
                            projections_in_progress,
                        ),
                        None => {
                            let expected = scheme.vars.len();
                            let found = generic_args.as_ref().map(|a| a.len()).unwrap_or(0);
                            Err(TyFromHirError::UnexpectedGenericArgs {
                                span,
                                module_id: self.module_id,
                                expected,
                                found,
                            })
                        }
                    },
                    None => Ok(Ty::Alias {
                        def_id,
                        generic_args: generic_args.clone(),
                    }),
                },
            ),
            Ty::Projection {
                trait_def_id,
                assoc_def_id,
                self_ty,
                generic_args,
                trait_generic_args,
            } => {
                if let Some(args) = generic_args.as_ref()
                    && !args.is_empty()
                {
                    return Err(TyFromHirError::UnexpectedGenericArgs {
                        span,
                        module_id: self.module_id,
                        expected: 0,
                        found: args.len(),
                    });
                }
                let Some(name) = self.typeck.resolver.def(assoc_def_id).name else {
                    return Err(TyFromHirError::UnresolvedAssocType {
                        span,
                        module_id: self.module_id,
                    });
                };
                let key = ProjectionRecKey::new(
                    trait_def_id,
                    assoc_def_id,
                    self_ty.as_ref(),
                    &trait_generic_args,
                    &generic_args,
                );
                if projections_in_progress.contains(&key) {
                    return Err(TyFromHirError::UnresolvedAssocType {
                        span,
                        module_id: self.module_id,
                    });
                }
                projections_in_progress.push(key.clone());
                let resolved = if self
                    .typeck
                    .current_self_ty
                    .as_ref()
                    .is_some_and(|current| current == self_ty.as_ref())
                    && let Some(concrete) = self.current_assoc_types.get(&(trait_def_id, name))
                {
                    self.normalize_aliases_inner(
                        concrete.clone(),
                        span,
                        in_progress,
                        projections_in_progress,
                    )
                } else if let Ty::Adt(self_def_id, self_generic_args) = self_ty.as_ref()
                    && let Some(impl_def_ids) = self
                        .typeck
                        .coherence
                        .impls
                        .get(&(trait_def_id, *self_def_id))
                {
                    let target_self_ty = Ty::Adt(*self_def_id, self_generic_args.clone());
                    let matching = self
                        .typeck
                        .coherence
                        .impls_matching_self(impl_def_ids, &target_self_ty);
                    if let Some(impl_def_id) = self
                        .typeck
                        .impl_matching_trait_args(&matching, &trait_generic_args)
                    {
                        let assoc_types = self.typeck.compute_assoc_types(impl_def_id);
                        if let Some(concrete) = assoc_types.get(&(trait_def_id, name)) {
                            self.normalize_aliases_inner(
                                concrete.clone(),
                                span,
                                in_progress,
                                projections_in_progress,
                            )
                        } else {
                            Err(TyFromHirError::UnresolvedAssocType {
                                span,
                                module_id: self.module_id,
                            })
                        }
                    } else {
                        Err(TyFromHirError::UnresolvedAssocType {
                            span,
                            module_id: self.module_id,
                        })
                    }
                } else {
                    Err(TyFromHirError::UnresolvedAssocType {
                        span,
                        module_id: self.module_id,
                    })
                };
                projections_in_progress.retain(|k| k != &key);
                resolved
            }
            ty => Ok(ty),
        })
    }

    fn check_const_body(&mut self, ty: &hir::Ty, body: &Body) {
        let expected = self.ty_from_hir_resolved(ty);
        self.node_types.insert(ty.hir_id, expected.clone());
        let body_ty = self.check_expr(&body.value);
        if let Err(err) = self
            .typeck
            .unify(&expected, &body_ty, body.value.span, self.module_id)
        {
            self.report_type_error(err);
        }
    }

    fn check_fn_body(&mut self, decl: &FnDecl, body: &Body) {
        self.env.push();
        for param in &decl.params {
            let param_ty = self.ty_from_hir_resolved(&param.ty);
            self.node_types.insert(param.ty.hir_id, param_ty.clone());
            let scheme = Scheme::monomorphic(param_ty);
            self.local_schemes.insert(param.hir_id, scheme.clone());
            self.env.insert(param.hir_id, scheme);
        }
        let expected = self.ty_from_hir_resolved(&decl.ret);
        self.node_types.insert(decl.ret.hir_id, expected.clone());
        self.check_expr(&body.value);
        self.check_return_values(&body.value, &expected, body.value.span);
        if let Some(body_ty) = self.node_types.get(&body.value.hir_id).cloned()
            && let Err(err) =
                self.typeck
                    .unify(&expected, &body_ty, tail_span(&body.value), self.module_id)
        {
            self.report_type_error(err);
        }
        self.env.pop();
    }

    fn check_return_values(&mut self, expr: &Expr, expected: &Ty, span: Span) {
        match &expr.kind {
            ExprKind::Return(inner) => {
                let inner = if let Some(inner) = inner {
                    self.node_types
                        .get(&inner.hir_id)
                        .cloned()
                        .unwrap_or(Ty::Error)
                } else {
                    Ty::Prim(PrimTy::Void)
                };
                if let Err(err) = self.typeck.unify(expected, &inner, span, self.module_id) {
                    self.report_type_error(err);
                }
            }
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.check_return_values_in_block(then_branch, expected);
                if let Some(else_branch) = else_branch {
                    self.check_return_values(else_branch, expected, span);
                }
            }
            ExprKind::Block(block) => self.check_return_values_in_block(block, expected),
            ExprKind::Loop(block) => self.check_return_values_in_block(block, expected),
            _ => {}
        }
    }

    fn check_return_values_in_block(&mut self, block: &Block, expected: &Ty) {
        for stmt in &block.stmts {
            if let StmtKind::Expr(expr) | StmtKind::Semi(expr) = &stmt.kind {
                self.check_return_values(expr, expected, stmt.span);
            }
        }
    }

    fn check_expr(&mut self, expr: &Expr) -> Ty {
        let id = expr.hir_id;
        let ty = self.check_expr_kind(&expr.kind, id, expr.span);
        self.node_types.insert(id, ty.clone());
        ty
    }

    fn check_expr_kind(&mut self, kind: &ExprKind, hir_id: HirId, expr_span: Span) -> Ty {
        match kind {
            ExprKind::Error => {
                builders::emit_at(
                    self.typeck.ctx,
                    expr_span,
                    self.module_id,
                    diag::UnresolvedExpression,
                    diag_params! {},
                );
                Ty::Error
            }
            ExprKind::Literal(lit) => self.check_lit(lit, expr_span),
            ExprKind::Path(qpath) => self.check_path(qpath, hir_id),
            ExprKind::Binary { left, op, right } => self.check_binary(left, *op, right),
            ExprKind::Unary { op, right } => self.check_unary(*op, right),
            ExprKind::Dereference { expr } => self.check_dereference(expr),
            ExprKind::Reference { expr, mutability } => self.check_reference(expr, *mutability),
            ExprKind::Call { callee, args } => self.check_call(callee, args, expr_span),
            ExprKind::StructInit {
                def,
                generic_args,
                fields,
            } => self.check_struct_init(*def, generic_args, fields, expr_span),
            ExprKind::ArrayInit { contents } => self.check_array_init(contents, expr_span),
            ExprKind::TupleInit(elements) => {
                Ty::Tuple(elements.iter().map(|expr| self.check_expr(expr)).collect())
            }
            ExprKind::Block(block) => self.check_block(block).tail,
            ExprKind::Loop(block) => self.check_loop(block),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_ty = self.check_expr(cond);
                let bool_ty = Ty::Prim(PrimTy::Bool);
                if let Err(err) = self
                    .typeck
                    .unify(&bool_ty, &cond_ty, cond.span, self.module_id)
                {
                    self.report_type_error(err);
                }
                let then_span = then_branch.span;
                let then_ty = self.check_block(then_branch).tail;
                let void_ty = Ty::Prim(PrimTy::Void);
                let else_ty = else_branch.as_ref().map(|expr| self.check_expr(expr));
                match else_ty {
                    Some(else_ty) => {
                        if let Err(err) =
                            self.typeck
                                .unify(&then_ty, &else_ty, then_span, self.module_id)
                        {
                            self.report_type_error(err);
                        }
                        then_ty
                    }
                    None => {
                        if let Err(err) =
                            self.typeck
                                .unify(&void_ty, &then_ty, then_span, self.module_id)
                        {
                            self.report_type_error(err);
                        }
                        void_ty
                    }
                }
            }
            ExprKind::Break(expr) | ExprKind::Return(expr) => {
                if let Some(expr) = expr {
                    self.check_expr(expr);
                }
                Ty::Never
            }
            ExprKind::Assign { target, value, .. } => {
                let target_ty = self.check_expr(target);
                let value_ty = self.check_expr(value);
                if let Err(err) =
                    self.typeck
                        .unify(&target_ty, &value_ty, value.span, self.module_id)
                {
                    self.report_type_error(err);
                }
                Ty::Prim(PrimTy::Void)
            }
            ExprKind::MemberAccess { base, member } => {
                self.check_member_access(*member, base, expr_span, hir_id)
            }
            ExprKind::Index { base, index } => self.check_index(base, index, expr_span, hir_id),
            ExprKind::As { expr, ty } => {
                self.check_expr(expr);
                let target_ty = self.ty_from_hir_resolved(ty);
                self.node_types.insert(ty.hir_id, target_ty.clone());
                target_ty
            }
            ExprKind::MethodCall { .. } | ExprKind::Field { .. } => {
                // MethodCall and Field cannot exist yet
                unreachable!()
            }
        }
    }

    fn check_lit(&mut self, lit: &Literal, span: Span) -> Ty {
        match lit {
            Literal::Integer(_) => Ty::Var(self.typeck.icx.next_int_var(span, self.module_id)),
            Literal::Float(_) => Ty::Var(self.typeck.icx.next_float_var(span, self.module_id)),
            Literal::Bool(_) => Ty::Prim(PrimTy::Bool),
            Literal::Char(_) => Ty::Prim(PrimTy::Uint(UintTy::U8)),
            Literal::String(_) => Ty::Slice(Ty::Prim(PrimTy::Uint(UintTy::U8)).into_box()),
        }
    }

    fn check_path(&mut self, qpath: &QPath, hir_id: HirId) -> Ty {
        match qpath {
            QPath::Resolved(_, path) => match &path.res {
                Res::Def(def_id) => self.check_resolved_path(*def_id, path, hir_id),
                Res::SelfTyAlias { alias_to } => match &self.typeck.current_self_ty {
                    Some(Ty::Adt(id, _)) => self.check_resolved_path(*id, path, hir_id),
                    _ => self.check_resolved_path(*alias_to, path, hir_id),
                },
                Res::Local(id) | Res::GenericParam(id) => match self.env.get(id) {
                    Some(scheme) => self.typeck.icx.instantiate(scheme),
                    None => Ty::Error,
                },
                Res::PrimTy(prim) => Ty::Prim(*prim),
                Res::Err => Ty::Error,
            },
            QPath::TypeRelative { .. } => Ty::Error,
        }
    }

    fn check_resolved_path(&mut self, def_id: DefId, path: &hir::Path, hir_id: HirId) -> Ty {
        let scheme = match self.typeck.item_schemes.get(&def_id) {
            Some(scheme) => scheme.clone(),
            None => return Ty::Error,
        };
        let explicit_args = path
            .segments
            .last()
            .and_then(|seg| seg.generic_args.as_ref());
        if matches!(scheme.body, Ty::Adt(_, _)) {
            match explicit_args {
                Some(args) => self
                    .instantiate_with_explicit_args(def_id, &scheme, args, path.span, false)
                    .unwrap_or_else(|err| {
                        self.report_ty_from_hir_error(err);
                        Ty::Error
                    }),
                None if scheme.vars.is_empty() => self.typeck.icx.instantiate(&scheme),
                None => Ty::Adt(def_id, None),
            }
        } else {
            let ty = self
                .instantiate_fn_scheme(def_id, &scheme, explicit_args, path.span, false)
                .unwrap_or_else(|err| {
                    self.report_ty_from_hir_error(err);
                    Ty::Error
                });
            let ty = self.typeck.normalize_type_alias(&ty);
            self.node_types.insert(hir_id, ty.clone());
            ty
        }
    }

    fn parent_var_count(&self, def_id: DefId) -> usize {
        self.typeck
            .coherence
            .assoc_to_parent
            .get(&def_id)
            .and_then(|parent_def_id| self.typeck.coherence.generic_params.get(parent_def_id))
            .map(|parent_info| parent_info.hir_ids.len())
            .unwrap_or(0)
    }

    fn try_complete_generic_args(
        &self,
        def_id: DefId,
        args: &mut ThinVec<hir::Ty>,
        expected_len: usize,
    ) -> bool {
        match args.len().cmp(&expected_len) {
            Ordering::Equal => true,
            Ordering::Greater => false,
            Ordering::Less => {
                let Some(info) = self.typeck.coherence.generic_params.get(&def_id) else {
                    return false;
                };
                for i in args.len()..expected_len {
                    match info.defaults.get(i) {
                        Some(Some(default_ty)) => args.push(default_ty.clone()),
                        _ => return false,
                    }
                }
                true
            }
        }
    }

    fn instantiate_with_explicit_args(
        &mut self,
        def_id: DefId,
        scheme: &Scheme,
        explicit_args: &ThinVec<hir::Ty>,
        span: Span,
        suppress_errors: bool,
    ) -> TyFromHirResult<Ty> {
        let provided = explicit_args.len();
        let parent_var_count = self.parent_var_count(def_id);
        let method_vars = &scheme.vars[parent_var_count..];
        let mut args = explicit_args.clone();
        if !self.try_complete_generic_args(def_id, &mut args, method_vars.len()) {
            return Err(TyFromHirError::UnexpectedGenericArgs {
                span,
                module_id: self.module_id,
                expected: method_vars.len(),
                found: provided,
            });
        }
        let mut mapping = FxHashMap::default();
        for &v in &scheme.vars {
            mapping.insert(v, self.typeck.icx.next_ty_var());
        }
        if let Some(info) = self.typeck.coherence.generic_params.get(&def_id) {
            for (hir_id, &v) in info.hir_ids.iter().zip(method_vars) {
                if let Some(&fresh) = mapping.get(&v) {
                    self.typeck
                        .icx
                        .hir_id_to_ty_var
                        .entry(*hir_id)
                        .or_insert(fresh);
                }
            }
        }
        let mut completed_subst: FxHashMap<TyVarId, Ty> = FxHashMap::default();
        for (hir_arg_ty, &v) in args.iter().zip(method_vars) {
            let mut arg_ty = match self.try_ty_from_hir_resolved(hir_arg_ty) {
                Ok(ty) => ty,
                Err(err) if suppress_errors => return Err(err),
                Err(err) => {
                    self.report_ty_from_hir_error(err);
                    Ty::Error
                }
            };
            if !completed_subst.is_empty() {
                arg_ty = substitute_ty_vars(&arg_ty, &completed_subst);
            }
            self.node_types.insert(hir_arg_ty.hir_id, arg_ty.clone());
            let &fresh = mapping.get(&v).expect("fresh var exists");
            self.typeck
                .unify(&Ty::Var(fresh), &arg_ty, span, self.module_id)
                .or_push_err(&mut self.typeck.icx);
            completed_subst.insert(v, arg_ty);
        }
        Ok(self.typeck.icx.instantiate_with(&scheme.body, &mapping))
    }

    fn instantiate_fn_scheme(
        &mut self,
        def_id: DefId,
        scheme: &Scheme,
        explicit_args: Option<&ThinVec<hir::Ty>>,
        span: Span,
        suppress_errors: bool,
    ) -> TyFromHirResult<Ty> {
        match explicit_args {
            Some(args) => {
                self.instantiate_with_explicit_args(def_id, scheme, args, span, suppress_errors)
            }
            None => Ok(self.typeck.icx.instantiate(scheme)),
        }
    }

    fn qpath_recv_ty(&mut self, qpath: &QPath) -> Option<Ty> {
        let base = match qpath {
            QPath::Resolved(_, path) => match &path.res {
                Res::Def(def_id) => match self.typeck.item_schemes.get(def_id).cloned() {
                    Some(scheme) => {
                        if let Some(explicit_args) = path
                            .segments
                            .last()
                            .and_then(|seg| seg.generic_args.as_ref())
                        {
                            match self.instantiate_with_explicit_args(
                                *def_id,
                                &scheme,
                                explicit_args,
                                path.span,
                                false,
                            ) {
                                Ok(ty) => ty,
                                Err(err) => {
                                    self.report_ty_from_hir_error(err);
                                    return None;
                                }
                            }
                        } else {
                            if matches!(scheme.body, Ty::Adt(_, _)) {
                                Ty::Adt(*def_id, None)
                            } else {
                                self.typeck.icx.instantiate(&scheme)
                            }
                        }
                    }
                    None => Ty::Error,
                },
                Res::SelfTyAlias { alias_to } => match &self.typeck.current_self_ty {
                    Some(ty) => ty.clone(),
                    None => Ty::Adt(*alias_to, None),
                },
                _ => return None,
            },
            QPath::TypeRelative { qself, .. } => return self.qpath_recv_ty(qself),
        };
        let base = self.typeck.icx.resolve(&base);
        if matches!(base, Ty::Adt(_, _)) {
            Some(base)
        } else {
            None
        }
    }

    fn check_binary(&mut self, left: &Expr, op: BinOp, right: &Expr) -> Ty {
        let left_span = left.span;
        let right_span = right.span;
        let left = self.check_expr(left);
        let right = self.check_expr(right);
        match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                self.typeck
                    .unify(&left, &right, left_span, self.module_id)
                    .or_push_err(&mut self.typeck.icx);
                Ty::Prim(PrimTy::Bool)
            }
            BinOp::And | BinOp::Or => {
                let bool_ty = Ty::Prim(PrimTy::Bool);
                self.typeck
                    .unify(&bool_ty, &left, left_span, self.module_id)
                    .or_push_err(&mut self.typeck.icx);
                self.typeck
                    .unify(&bool_ty, &right, right_span, self.module_id)
                    .or_push_err(&mut self.typeck.icx);
                bool_ty
            }
            _ => {
                if !left.is_numeric(&self.typeck.icx) {
                    builders::emit_at(
                        self.typeck.ctx,
                        left_span,
                        self.module_id,
                        diag::NonNumericOperand,
                        diag_params! { operator = op },
                    );
                    return Ty::Error;
                } else if !right.is_numeric(&self.typeck.icx) {
                    builders::emit_at(
                        self.typeck.ctx,
                        right_span,
                        self.module_id,
                        diag::NonNumericOperand,
                        diag_params! { operator = op },
                    );
                    return Ty::Error;
                }

                self.typeck
                    .unify(&left, &right, left_span, self.module_id)
                    .or_push_err(&mut self.typeck.icx);
                left
            }
        }
    }

    fn check_unary(&mut self, op: UnOp, right: &Expr) -> Ty {
        let right_span = right.span;
        let right = self.check_expr(right);
        match op {
            UnOp::Not => {
                let bool_ty = Ty::Prim(PrimTy::Bool);
                self.typeck
                    .unify(&bool_ty, &right, right_span, self.module_id)
                    .or_push_err(&mut self.typeck.icx);
                bool_ty
            }
            UnOp::Neg => {
                let resolved = self.typeck.icx.resolve(&right);
                if !resolved.is_numeric(&self.typeck.icx) {
                    builders::emit_at(
                        self.typeck.ctx,
                        right_span,
                        self.module_id,
                        diag::NonNumericOperand,
                        diag_params! { operator = op },
                    );
                    return Ty::Error;
                }
                resolved
            }
        }
    }

    fn check_reference(&mut self, expr: &Expr, mutability: Mutability) -> Ty {
        let expr = self.check_expr(expr);
        Ty::Ptr(expr.into_box(), mutability)
    }

    fn check_dereference(&mut self, expr: &Expr) -> Ty {
        let span = expr.span;
        let left = self.check_expr(expr);
        match left {
            Ty::Ptr(inner, _) => (*inner).clone(),
            _ => {
                builders::emit_at(
                    self.typeck.ctx,
                    span,
                    self.module_id,
                    diag::DerefNonPointer,
                    diag_params! { type = ty_display(&left, self.typeck.resolver, &self.typeck.ctx.interner) },
                );
                Ty::Error
            }
        }
    }

    fn def_ty_var_subst(&self, def: DefId, args: &[Ty]) -> FxHashMap<TyVarId, Ty> {
        let mut subst = FxHashMap::default();
        if let Some(info) = self.typeck.coherence.generic_params.get(&def) {
            for (hir_id, arg_ty) in info.hir_ids.iter().zip(args.iter()) {
                if let Some(&registered_var) = self.typeck.icx.hir_id_to_ty_var.get(hir_id) {
                    subst.insert(registered_var, arg_ty.clone());
                }
            }
        }
        subst
    }

    fn check_struct_init(
        &mut self,
        def: DefId,
        generic_args: &Option<ThinVec<hir::Ty>>,
        fields: &ThinVec<(Ident, Expr)>,
        span: Span,
    ) -> Ty {
        match self.expand_struct_init_def(def, generic_args, span) {
            StructInitDef::Expanded(def, args) => {
                let param_hir_ids = self
                    .typeck
                    .coherence
                    .generic_params
                    .get(&def)
                    .expect("struct exists")
                    .hir_ids
                    .len();
                assert_eq!(args.len(), param_hir_ids);
                let ty_var_subst = self.def_ty_var_subst(def, &args);
                let struct_ty = Ty::Adt(def, Some(args));
                self.check_struct_fields(def, struct_ty, fields, span, &ty_var_subst)
            }
            StructInitDef::Struct => {
                let param_hir_ids = self
                    .typeck
                    .coherence
                    .generic_params
                    .get(&def)
                    .expect("struct exists")
                    .hir_ids
                    .clone();

                let fresh_var_map: FxHashMap<HirId, TyVarId> = param_hir_ids
                    .iter()
                    .map(|&hir_id| (hir_id, self.typeck.icx.next_ty_var()))
                    .collect();

                let (struct_ty, ty_var_subst) = if let Some(generic_args) = generic_args {
                    let provided = generic_args.len();
                    let mut hir_args = generic_args.clone();
                    if !self.try_complete_generic_args(def, &mut hir_args, param_hir_ids.len()) {
                        emit_unexpected_generic_args(
                            self.typeck.ctx,
                            span,
                            self.module_id,
                            param_hir_ids.len(),
                            provided,
                        );
                        return Ty::Error;
                    }
                    let mut completed_subst: FxHashMap<TyVarId, Ty> = FxHashMap::default();
                    let mut args: ThinVec<Ty> = ThinVec::new();
                    for (i, arg) in hir_args.iter().enumerate() {
                        let mut arg_ty = self.ty_from_hir_resolved(arg);
                        if i >= provided && !completed_subst.is_empty() {
                            arg_ty = substitute_ty_vars(&arg_ty, &completed_subst);
                        }
                        self.node_types.insert(arg.hir_id, arg_ty.clone());
                        if let Some(&var) = self.typeck.icx.hir_id_to_ty_var.get(&param_hir_ids[i])
                        {
                            completed_subst.insert(var, arg_ty.clone());
                        }
                        args.push(arg_ty);
                    }
                    for (arg, hir_id) in args.iter().zip(param_hir_ids.iter()) {
                        if let Some(&fresh) = fresh_var_map.get(hir_id) {
                            self.typeck
                                .unify(&Ty::Var(fresh), arg, span, self.module_id)
                                .or_push_err(&mut self.typeck.icx);
                        }
                    }
                    let subst = self.def_ty_var_subst(def, &args);
                    (Ty::Adt(def, Some(args)), subst)
                } else {
                    if param_hir_ids.is_empty() {
                        (Ty::Adt(def, None), FxHashMap::default())
                    } else {
                        let args: ThinVec<Ty> = param_hir_ids
                            .iter()
                            .map(|&hir_id| {
                                Ty::Var(*fresh_var_map.get(&hir_id).expect("fresh var exists"))
                            })
                            .collect();
                        self.stash_generic_defaults(def, &fresh_var_map);
                        let subst = self.def_ty_var_subst(def, &args);
                        (Ty::Adt(def, Some(args)), subst)
                    }
                };

                self.check_struct_fields(def, struct_ty, fields, span, &ty_var_subst)
            }
            StructInitDef::Error => Ty::Error,
        }
    }

    fn expand_struct_init_def(
        &mut self,
        def: DefId,
        generic_args: &Option<ThinVec<hir::Ty>>,
        span: Span,
    ) -> StructInitDef {
        if self.typeck.resolver.def(def).kind != DefKind::TypeAlias {
            return StructInitDef::Struct;
        }
        let Some(scheme) = self.typeck.item_schemes.get(&def).cloned() else {
            return StructInitDef::Error;
        };
        let alias_info = self.typeck.coherence.generic_params.get(&def).cloned();

        let alias_args: ThinVec<Ty> = match generic_args {
            Some(args) => {
                if args.len() > scheme.vars.len() {
                    emit_unexpected_generic_args(
                        self.typeck.ctx,
                        span,
                        self.module_id,
                        scheme.vars.len(),
                        args.len(),
                    );
                    return StructInitDef::Error;
                }
                let mut resolved: ThinVec<Ty> = ThinVec::new();
                let mut subst: FxHashMap<TyVarId, Ty> = FxHashMap::default();
                for (i, arg) in args.iter().enumerate() {
                    let arg_ty = self.ty_from_hir_resolved(arg);
                    self.node_types.insert(arg.hir_id, arg_ty.clone());
                    if let Some(info) = &alias_info
                        && let Some(&var) = self.typeck.icx.hir_id_to_ty_var.get(&info.hir_ids[i])
                    {
                        subst.insert(var, arg_ty.clone());
                    }
                    resolved.push(arg_ty);
                }
                if let Some(info) = alias_info {
                    for i in resolved.len()..info.hir_ids.len() {
                        match info.defaults.get(i).and_then(|d| d.as_ref()) {
                            Some(default_ty) => {
                                let mut default_ty = self.ty_from_hir_resolved(default_ty);
                                if !subst.is_empty() {
                                    default_ty = substitute_ty_vars(&default_ty, &subst);
                                }
                                if let Some(&var) =
                                    self.typeck.icx.hir_id_to_ty_var.get(&info.hir_ids[i])
                                {
                                    subst.insert(var, default_ty.clone());
                                }
                                resolved.push(default_ty);
                            }
                            None => break,
                        }
                    }
                }
                resolved
            }
            None => {
                let fresh_vars: ThinVec<Ty> = (0..scheme.vars.len())
                    .map(|_| Ty::Var(self.typeck.icx.next_ty_var()))
                    .collect();
                if let Some(info) = alias_info {
                    let subst: FxHashMap<TyVarId, Ty> = scheme
                        .vars
                        .iter()
                        .copied()
                        .zip(fresh_vars.iter().cloned())
                        .collect();
                    for (i, default_ty) in info.defaults.iter().enumerate() {
                        if let Some(default_ty) = default_ty
                            && let Ty::Var(var) = fresh_vars[i]
                        {
                            let default_ty =
                                substitute_ty_vars(&self.ty_from_hir_resolved(default_ty), &subst);
                            self.typeck.icx.add_generic_default(var, default_ty);
                        }
                    }
                }
                fresh_vars
            }
        };

        if alias_args.len() != scheme.vars.len() {
            emit_unexpected_generic_args(
                self.typeck.ctx,
                span,
                self.module_id,
                scheme.vars.len(),
                alias_args.len(),
            );
            return StructInitDef::Error;
        }

        let Some(body) = resolve_scheme_with_args(&scheme, &Some(alias_args)) else {
            return StructInitDef::Error;
        };
        let Ok(body) = self.normalize_aliases(body, span) else {
            return StructInitDef::Error;
        };
        if body.is_error() {
            return StructInitDef::Error;
        }

        match body {
            Ty::Adt(struct_def, Some(mut args)) => {
                let struct_info = self
                    .typeck
                    .coherence
                    .generic_params
                    .get(&struct_def)
                    .cloned();
                if let Some(info) = &struct_info {
                    if args.len() > info.hir_ids.len() {
                        emit_unexpected_generic_args(
                            self.typeck.ctx,
                            span,
                            self.module_id,
                            info.hir_ids.len(),
                            args.len(),
                        );
                        return StructInitDef::Error;
                    }
                    let mut subst: FxHashMap<TyVarId, Ty> = FxHashMap::default();
                    for (i, arg) in args.iter().enumerate() {
                        if let Some(&var) = self.typeck.icx.hir_id_to_ty_var.get(&info.hir_ids[i]) {
                            subst.insert(var, arg.clone());
                        }
                    }
                    for i in args.len()..info.hir_ids.len() {
                        let var = self.typeck.icx.next_ty_var();
                        if let Some(&declared) =
                            self.typeck.icx.hir_id_to_ty_var.get(&info.hir_ids[i])
                        {
                            subst.insert(declared, Ty::Var(var));
                        }
                        if let Some(Some(default_ty)) = info.defaults.get(i) {
                            let mut default_ty = self.ty_from_hir_resolved(default_ty);
                            if !subst.is_empty() {
                                default_ty = substitute_ty_vars(&default_ty, &subst);
                            }
                            self.typeck.icx.add_generic_default(var, default_ty);
                        }
                        args.push(Ty::Var(var));
                    }
                }
                StructInitDef::Expanded(struct_def, args)
            }
            Ty::Adt(struct_def, None) => {
                let struct_info = self
                    .typeck
                    .coherence
                    .generic_params
                    .get(&struct_def)
                    .cloned();
                let mut args: ThinVec<Ty> = ThinVec::new();
                if let Some(info) = &struct_info {
                    let fresh_vars: ThinVec<TyVarId> = (0..info.hir_ids.len())
                        .map(|_| self.typeck.icx.next_ty_var())
                        .collect();
                    let subst: FxHashMap<TyVarId, Ty> = fresh_vars
                        .iter()
                        .enumerate()
                        .filter_map(|(i, &fresh)| {
                            self.typeck
                                .icx
                                .hir_id_to_ty_var
                                .get(&info.hir_ids[i])
                                .map(|&var| (var, Ty::Var(fresh)))
                        })
                        .collect();
                    for (i, &fresh) in fresh_vars.iter().enumerate() {
                        if let Some(Some(default_ty)) = info.defaults.get(i) {
                            let mut default_ty = self.ty_from_hir_resolved(default_ty);
                            if !subst.is_empty() {
                                default_ty = substitute_ty_vars(&default_ty, &subst);
                            }
                            self.typeck.icx.add_generic_default(fresh, default_ty);
                        }
                        args.push(Ty::Var(fresh));
                    }
                }
                StructInitDef::Expanded(struct_def, args)
            }
            _ => {
                let name = self
                    .typeck
                    .resolver
                    .def(def)
                    .name
                    .map(|sym| self.typeck.ctx.interner.lookup(sym).to_string())
                    .unwrap_or_default();
                builders::emit_at(
                    self.typeck.ctx,
                    span,
                    self.module_id,
                    diag::TypeAliasNotStruct,
                    diag_params! { name = name },
                );
                StructInitDef::Error
            }
        }
    }

    fn stash_generic_defaults(&mut self, def: DefId, fresh_var_map: &FxHashMap<HirId, TyVarId>) {
        let info = match self.typeck.coherence.generic_params.get(&def).cloned() {
            Some(info) => info,
            None => return,
        };

        let subst: FxHashMap<TyVarId, Ty> = info
            .hir_ids
            .iter()
            .filter_map(|hir_id| {
                fresh_var_map.get(hir_id).and_then(|&fresh| {
                    self.typeck
                        .icx
                        .hir_id_to_ty_var
                        .get(hir_id)
                        .map(|&def_var| (def_var, Ty::Var(fresh)))
                })
            })
            .collect();
        for (hir_id, default) in info.hir_ids.iter().zip(info.defaults.iter()) {
            if let Some(default_ty) = default
                && let Some(&fresh) = fresh_var_map.get(hir_id)
            {
                let default_ty = self.ty_from_hir_resolved(default_ty);
                let default_ty = substitute_ty_vars(&default_ty, &subst);
                self.typeck.icx.add_generic_default(fresh, default_ty);
            }
        }
    }

    fn check_struct_fields(
        &mut self,
        def: DefId,
        struct_ty: Ty,
        fields: &ThinVec<(Ident, Expr)>,
        span: Span,
        ty_var_subst: &FxHashMap<TyVarId, Ty>,
    ) -> Ty {
        let field_table = self
            .typeck
            .coherence
            .struct_fields
            .get(&def)
            .cloned()
            .unwrap_or_default();

        let sym_to_span: FxHashMap<Symbol, Span> = fields
            .iter()
            .map(|(name, _)| (name.value, name.span))
            .collect();
        let init_names: FxHashSet<Symbol> = fields.iter().map(|(name, _)| name.value).collect();
        let struct_names: FxHashSet<Symbol> = field_table.keys().copied().collect();

        for name in init_names.difference(&struct_names) {
            let field = self.typeck.ctx.interner.lookup(*name).to_string();
            builders::emit_at(
                self.typeck.ctx,
                *sym_to_span.get(name).expect("field exists"),
                self.module_id,
                diag::UnknownField,
                diag_params! {
                    field = field,
                    type = ty_display(&struct_ty, self.typeck.resolver, &self.typeck.ctx.interner)
                },
            );
        }

        for name in struct_names.difference(&init_names) {
            let field = self.typeck.ctx.interner.lookup(*name).to_string();
            builders::emit_at(
                self.typeck.ctx,
                span,
                self.module_id,
                diag::MissingField,
                diag_params! {
                    field = field,
                    type = ty_display(&struct_ty, self.typeck.resolver, &self.typeck.ctx.interner)
                },
            );
        }

        for (name, expr) in fields {
            let expr_span = expr.span;
            let expr = self.check_expr(expr);
            if let Some((hir_field_ty, _)) = field_table.get(&name.value) {
                let mut field_ty = self.ty_from_hir_resolved(hir_field_ty);
                if !ty_var_subst.is_empty() {
                    field_ty = substitute_ty_vars(&field_ty, ty_var_subst);
                }
                if let Err(err) = self
                    .typeck
                    .unify(&field_ty, &expr, expr_span, self.module_id)
                {
                    self.typeck.icx.errors.push(err);
                }
            }
        }

        struct_ty
    }

    fn check_array_init(&mut self, contents: &ThinVec<Expr>, span: Span) -> Ty {
        let mut elem_ty = None;
        for expr in contents {
            let expr_ty = self.check_expr(expr);
            if let Some(elem_ty) = &elem_ty {
                if let Err(err) = self
                    .typeck
                    .unify(elem_ty, &expr_ty, expr.span, self.module_id)
                {
                    self.report_type_error(err);
                }
            } else {
                elem_ty = Some(expr_ty);
            }
        }
        let elem_ty = elem_ty.unwrap_or_else(|| {
            let var = self.typeck.icx.next_ty_var_at(
                self.typeck.icx.current_level(),
                TyVarSource::EmptyArray,
                Some(span),
                Some(self.module_id),
            );
            Ty::Var(var)
        });
        Ty::Slice(elem_ty.into_box())
    }

    fn check_block(&mut self, block: &Block) -> BlockTyRes {
        self.env.push();
        let mut break_ty = None;
        let mut last_ty = Ty::Prim(PrimTy::Void);
        let mut diverged = false;
        for stmt in &block.stmts {
            if diverged {
                match &stmt.kind {
                    StmtKind::Let {
                        ty: hir_ty, init, ..
                    } => {
                        let ty = self.ty_from_hir_resolved(hir_ty);
                        self.node_types.insert(hir_ty.hir_id, ty);
                        if let Some(init) = init {
                            self.check_expr(init);
                        }
                    }
                    StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
                        self.check_expr(expr);
                    }
                }
                continue;
            }
            match &stmt.kind {
                StmtKind::Let {
                    ty: hir_ty,
                    init,
                    local,
                    ..
                } => {
                    let ty = self.ty_from_hir_resolved(hir_ty);
                    self.node_types.insert(hir_ty.hir_id, ty.clone());
                    self.typeck.icx.push_level();
                    let init_span = init.as_ref().map(|e| e.span).unwrap_or(stmt.span);
                    let bound = init
                        .as_ref()
                        .map(|expr| self.check_expr(expr))
                        .unwrap_or_else(|| ty.clone());
                    if let Err(err) = self.typeck.unify(&ty, &bound, init_span, self.module_id) {
                        self.typeck.icx.errors.push(err);
                    }
                    let scope = self.typeck.icx.current_level();
                    let parent = scope.saturating_sub(1);
                    let quantified = self.typeck.icx.generalize(&ty, parent);
                    let scheme = Scheme {
                        vars: quantified,
                        body: ty.clone(),
                    };
                    self.local_schemes.insert(*local, scheme.clone());
                    self.env.insert(*local, scheme);
                    self.typeck.icx.pop_level();
                    if let Some(init) = init {
                        self.collect_break_ty_from_expr(init, &mut break_ty, stmt.span);
                    }
                }
                StmtKind::Expr(expr) => {
                    last_ty = self.check_expr(expr);
                    self.collect_break_ty_from_expr(expr, &mut break_ty, expr.span);
                    if matches!(last_ty, Ty::Never) {
                        diverged = true;
                    }
                }
                StmtKind::Semi(expr) => {
                    self.collect_break_ty_from_expr(expr, &mut break_ty, expr.span);
                    let expr = self.check_expr(expr);
                    if matches!(expr, Ty::Never) {
                        last_ty = Ty::Never;
                        diverged = true;
                    } else {
                        last_ty = Ty::Prim(PrimTy::Void)
                    }
                }
            }
        }
        self.env.pop();
        BlockTyRes {
            tail: if diverged { Ty::Never } else { last_ty },
            early: break_ty,
        }
    }

    fn collect_break_ty_from_stmts(
        &mut self,
        stmts: &[Stmt],
        break_ty: &mut Option<Ty>,
        span: Span,
    ) {
        for stmt in stmts {
            match &stmt.kind {
                StmtKind::Expr(expr) | StmtKind::Semi(expr) => {
                    self.collect_break_ty_from_expr(expr, break_ty, span);
                }
                StmtKind::Let { init, .. } => {
                    if let Some(init) = init {
                        self.collect_break_ty_from_expr(init, break_ty, span);
                    }
                }
            }
        }
    }

    fn collect_break_ty_from_expr(&mut self, expr: &Expr, break_ty: &mut Option<Ty>, span: Span) {
        match &expr.kind {
            ExprKind::Break(break_expr) => {
                let break_value_ty = break_expr
                    .as_ref()
                    .map_or(Ty::Prim(PrimTy::Void), |inner| self.check_expr(inner));

                if let Some(existing_break_ty) = break_ty
                    && let Err(err) =
                        self.typeck
                            .unify(existing_break_ty, &break_value_ty, span, self.module_id)
                {
                    self.report_type_error(err);
                    return;
                }

                *break_ty = Some(break_value_ty);
            }
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.collect_break_ty_from_stmts(&then_branch.stmts, break_ty, span);
                if let Some(else_expr) = else_branch {
                    self.collect_break_ty_from_expr(else_expr, break_ty, span);
                }
            }
            ExprKind::Block(block) => {
                self.collect_break_ty_from_stmts(&block.stmts, break_ty, span);
            }
            ExprKind::Loop(_) => {}
            _ => {}
        }
    }

    fn check_loop(&mut self, block: &Block) -> Ty {
        let block_ty_res = self.check_block(block);

        let void_ty = Ty::Prim(PrimTy::Void);
        if let Err(err) =
            self.typeck
                .unify(&void_ty, &block_ty_res.tail, block.span, self.module_id)
        {
            self.report_type_error(err);
        }

        block_ty_res.early.unwrap_or(Ty::Never)
    }

    fn lookup_adt_field(
        &mut self,
        struct_id: DefId,
        generic_args: &Option<ThinVec<Ty>>,
        member: Symbol,
        hir_id: HirId,
    ) -> Option<Ty> {
        let fields = self.typeck.coherence.struct_fields.get(&struct_id)?.clone();
        let (hir_field_ty, index) = fields.get(&member)?;
        self.member_res
            .insert(hir_id, MemberRes::Field { index: *index });
        let mut field_ty = self.ty_from_hir_resolved(hir_field_ty);
        match generic_args {
            Some(generic_args) => {
                let subst = self.def_ty_var_subst(struct_id, generic_args);
                if !subst.is_empty() {
                    field_ty = substitute_ty_vars(&field_ty, &subst);
                }
            }
            None => {
                if let Some(info) = self
                    .typeck
                    .coherence
                    .generic_params
                    .get(&struct_id)
                    .cloned()
                {
                    let mut subst: FxHashMap<TyVarId, Ty> = FxHashMap::default();
                    let mut resolved: ThinVec<Ty> = ThinVec::new();
                    let mut has_missing = false;
                    for (i, default) in info.defaults.iter().enumerate() {
                        match default {
                            Some(ty) => {
                                let mut ty = self.ty_from_hir_resolved(ty);
                                if !subst.is_empty() {
                                    ty = substitute_ty_vars(&ty, &subst);
                                }
                                if let Some(&var) =
                                    self.typeck.icx.hir_id_to_ty_var.get(&info.hir_ids[i])
                                {
                                    subst.insert(var, ty.clone());
                                }
                                resolved.push(ty);
                            }
                            None => {
                                has_missing = true;
                                break;
                            }
                        }
                    }
                    if !has_missing {
                        let subst = self.def_ty_var_subst(struct_id, &resolved);
                        if !subst.is_empty() {
                            field_ty = substitute_ty_vars(&field_ty, &subst);
                        }
                    }
                }
            }
        }
        Some(field_ty)
    }

    fn check_member_access(
        &mut self,
        member: Symbol,
        base: &Expr,
        expr_span: Span,
        hir_id: HirId,
    ) -> Ty {
        let member_span = Span::new(base.span.end() + 1, expr_span.end());
        let recv_ty = self.check_expr(base);
        let recv_ty = self.typeck.icx.resolve(&recv_ty);
        let recv_ty = self.typeck.normalize_type_alias(&recv_ty);

        // TODO: Maybe run in a loop to dereference types like `&&T`
        let recv_ty = if let Ty::Ptr(inner, _) = &recv_ty {
            self.adjustments
                .entry(base.hir_id)
                .or_default()
                .push(Adjustment::AutoDeref);
            inner.as_ref()
        } else {
            &recv_ty
        };

        match recv_ty {
            Ty::Adt(struct_id, generic_args) => {
                if let Some(field_ty) =
                    self.lookup_adt_field(*struct_id, generic_args, member, hir_id)
                {
                    return field_ty;
                }

                let field = self.typeck.ctx.interner.lookup(member).to_string();
                builders::emit_at(
                    self.typeck.ctx,
                    member_span,
                    self.module_id,
                    diag::UnknownField,
                    diag_params! {
                        field = field,
                        type = ty_display(recv_ty, self.typeck.resolver, &self.typeck.ctx.interner)
                    },
                );
            }
            Ty::Slice(elem) => {
                let interner = &self.typeck.ctx.interner;
                if interner.lookup(member) == "len" {
                    self.member_res
                        .insert(hir_id, MemberRes::Field { index: 1 });
                    return Ty::Prim(PrimTy::Uint(UintTy::Usize));
                }
                if interner.lookup(member) == "ptr" {
                    self.member_res
                        .insert(hir_id, MemberRes::Field { index: 0 });
                    return Ty::Ptr(elem.clone(), Mutability::Constant);
                }
                let field = self.typeck.ctx.interner.lookup(member).to_string();
                builders::emit_at(
                    self.typeck.ctx,
                    member_span,
                    self.module_id,
                    diag::UnknownFieldInSlice,
                    diag_params! { field = field },
                );
            }
            _ => {
                let field = self.typeck.ctx.interner.lookup(member).to_string();
                builders::emit_at(
                    self.typeck.ctx,
                    member_span,
                    self.module_id,
                    diag::TypeWithNoFields,
                    diag_params! {
                        field = field,
                        type = ty_display(recv_ty, self.typeck.resolver, &self.typeck.ctx.interner)
                    },
                );
            }
        }
        Ty::Error
    }

    fn check_index(&mut self, base: &Expr, index: &Expr, expr_span: Span, _hir_id: HirId) -> Ty {
        let base_ty = self.check_expr(base);
        let base = self.typeck.icx.resolve(&base_ty);
        match base {
            Ty::Slice(elem) | Ty::Array(elem, _) => {
                let index_ty = self.check_expr(index);
                let usize_ty = Ty::Prim(PrimTy::Uint(UintTy::Usize));
                if let Err(err) =
                    self.typeck
                        .unify(&usize_ty, &index_ty, index.span, self.module_id)
                {
                    self.report_type_error(err);
                }
                *elem.clone()
            }
            _ => {
                self.check_expr(index);
                builders::emit_at(
                    self.typeck.ctx,
                    expr_span,
                    self.module_id,
                    diag::CannotIndex,
                    diag_params! { type = ty_display(&base, self.typeck.resolver, &self.typeck.ctx.interner) },
                );
                Ty::Error
            }
        }
    }

    fn report_type_error(&mut self, err: UnifyError) {
        emit_unify_error(
            &err,
            self.typeck.resolver,
            self.typeck.ctx,
            &self.typeck.icx,
        );
    }
}

pub(super) fn emit_unexpected_generic_args(
    ctx: &mut Ctx,
    span: Span,
    module_id: ModuleId,
    expected: usize,
    found: usize,
) {
    builders::emit_at(
        ctx,
        span,
        module_id,
        diag::UnexpectedGenericArgs,
        diag_params! {
            expected = expected,
            s = if expected == 1 { "" } else { "s" },
            found = found,
        },
    );
}

pub(super) fn emit_ty_from_hir_error(err: &TyFromHirError, ctx: &mut Ctx) {
    match err {
        TyFromHirError::ExpectedPathToTrait {
            span,
            module_id,
            path,
        } => {
            builders::emit_at(
                ctx,
                *span,
                *module_id,
                hir::diag::ExpectedPathToTrait,
                diag_params! { path = path.display(ctx) },
            );
        }
        TyFromHirError::UnresolvedAssocType { span, module_id } => {
            builders::emit_at(
                ctx,
                *span,
                *module_id,
                diag::UnresolvedAssocType,
                diag_params! {},
            );
        }
        TyFromHirError::UnexpectedGenericArgs {
            span,
            module_id,
            expected,
            found,
        } => {
            emit_unexpected_generic_args(ctx, *span, *module_id, *expected, *found);
        }
    }
}

pub(super) fn emit_unify_error(
    err: &UnifyError,
    resolver: &ResolverOutputs,
    ctx: &mut Ctx,
    icx: &InferCtx,
) {
    match err {
        UnifyError::Mismatch {
            expected,
            found,
            span,
            module_id,
        } => {
            let expected = icx.resolve(expected);
            let found = icx.resolve(found);
            let expected_str = ty_display(&expected, resolver, &ctx.interner);
            let found_str = ty_display(&found, resolver, &ctx.interner);
            let info = generic_mismatch_info(&expected, &found, resolver, &ctx.interner);
            if let Some(info) = info {
                builders::emit_at_with_info(
                    ctx,
                    *span,
                    *module_id,
                    &info,
                    diag::TypeMismatch,
                    diag_params! {
                        expected = expected_str,
                        found = found_str
                    },
                );
            } else {
                builders::emit_at(
                    ctx,
                    *span,
                    *module_id,
                    diag::TypeMismatch,
                    diag_params! {
                        expected = expected_str,
                        found = found_str
                    },
                );
            }
        }
        UnifyError::OccursCheck {
            span, module_id, ..
        } => {
            builders::emit_at(ctx, *span, *module_id, diag::RecursiveType, diag_params! {});
        }
    };
}

fn generic_mismatch_info(
    expected: &Ty,
    found: &Ty,
    resolver: &ResolverOutputs,
    interner: &Interner,
) -> Option<String> {
    match (expected, found) {
        (Ty::Adt(d1, Some(g1)), Ty::Adt(d2, Some(g2))) if d1 == d2 && g1.len() != g2.len() => {
            let name = resolver
                .def(*d1)
                .name
                .map(|sym| interner.lookup(sym).to_string())
                .unwrap_or_else(|| format!("Struct#{}", d1.0));
            Some(format!(
                "struct `{name}` has {} generic parameter{}, but {} {} provided",
                g1.len(),
                if g1.len() == 1 { "" } else { "s" },
                g2.len(),
                if g2.len() == 1 { "was" } else { "were" },
            ))
        }
        _ => None,
    }
}

fn ty_display(ty: &Ty, resolver: &ResolverOutputs, interner: &Interner) -> String {
    match ty {
        Ty::Var(id) => format!("Var#{}", id),
        Ty::Prim(p) => p.name_str().to_string(),
        Ty::Ptr(inner, m) => format!(
            "&{}{}",
            if matches!(m, crate::ast::Mutability::Mutable) {
                "mut "
            } else {
                ""
            },
            ty_display(inner, resolver, interner)
        ),
        Ty::Slice(inner) => format!("[]{}", ty_display(inner, resolver, interner)),
        Ty::Array(inner, n) => format!("[{}]{}", n, ty_display(inner, resolver, interner)),
        Ty::Fn { params, ret } => {
            let ps: Vec<String> = params
                .iter()
                .map(|t| ty_display(t, resolver, interner))
                .collect();
            format!(
                "({}) -> {}",
                ps.join(", "),
                ty_display(ret, resolver, interner)
            )
        }
        Ty::Tuple(elements) => {
            let es: Vec<String> = elements
                .iter()
                .map(|t| ty_display(t, resolver, interner))
                .collect();
            format!("({})", es.join(", "))
        }
        Ty::Adt(d, generics) => {
            let name = resolver
                .def(*d)
                .name
                .map(|sym| interner.lookup(sym).to_string())
                .unwrap_or_else(|| format!("Struct#{}", d.0));
            format!(
                "{}{}",
                name,
                generics_to_string(generics.as_ref(), resolver, interner)
            )
        }
        Ty::Alias {
            def_id,
            generic_args,
        } => {
            let name = resolver
                .def(*def_id)
                .name
                .map(|sym| interner.lookup(sym).to_string())
                .unwrap_or_else(|| format!("Alias#{}", def_id.0));
            format!(
                "{}{}",
                name,
                generics_to_string(generic_args.as_ref(), resolver, interner)
            )
        }
        Ty::Projection {
            trait_def_id,
            assoc_def_id,
            self_ty,
            generic_args,
            trait_generic_args,
        } => {
            let name = resolver
                .def(*trait_def_id)
                .name
                .map(|sym| interner.lookup(sym).to_string())
                .unwrap_or_else(|| format!("Trait#{}", trait_def_id.0));
            let assoc_name = resolver
                .def(*assoc_def_id)
                .name
                .map(|sym| interner.lookup(sym).to_string())
                .unwrap_or_else(|| format!("Ty#{}", assoc_def_id.0));
            format!(
                "<{} as {}{}>::{}{}",
                ty_display(self_ty, resolver, interner),
                name,
                generics_to_string(trait_generic_args.as_ref(), resolver, interner),
                assoc_name,
                generics_to_string(generic_args.as_ref(), resolver, interner)
            )
        }
        Ty::Never => "!".to_string(),
        Ty::MethodCallee => "<method-callee>".to_string(),
        Ty::Error => "<error>".to_string(),
    }
}

fn generics_to_string(
    generics: Option<&ThinVec<Ty>>,
    resolver: &ResolverOutputs,
    interner: &Interner,
) -> String {
    if generics.is_none() {
        return String::new();
    }
    let generics = generics.expect("generics exists");
    let mut s = String::new();
    s.push_str("::<");
    for (i, ty_var) in generics.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        s.push_str(&ty_display(ty_var, resolver, interner));
    }
    s.push('>');
    s
}
