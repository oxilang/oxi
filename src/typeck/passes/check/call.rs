use fxhash::FxHashMap;
use thin_vec::ThinVec;

use crate::ast::Mutability;
use crate::errors::builders;
use crate::hir::{DefId, Expr, ExprKind, HirId, QPath};
use crate::interner::Symbol;
use crate::span::Span;
use crate::typeck::fold::{fold_ty, substitute_ty_vars};
use crate::typeck::passes::check::{BodyChecker, ty_display};
use crate::typeck::unify::OrPushErr;
use crate::typeck::{Adjustment, MemberRes, MethodKind, Scheme, Ty, diag};
use crate::{diag_params, hir};

impl<'a, 'ctx, 'hir, 'res> BodyChecker<'a, 'ctx, 'hir, 'res> {
    pub fn check_call(&mut self, callee: &Expr, args: &ThinVec<Expr>, call_span: Span) -> Ty {
        let callee_span = callee.span;

        if let Some((recv_ty, member, is_method_call, receiver_hir_id, generic_args)) =
            match &callee.kind {
                ExprKind::MemberAccess { base, member } => Some((
                    self.check_expr(base),
                    *member,
                    true,
                    Some(base.hir_id),
                    None,
                )),
                ExprKind::Path(QPath::TypeRelative { qself, segment }) => {
                    self.qpath_recv_ty(qself).map(|ty| {
                        (
                            ty,
                            segment.ident.value,
                            false,
                            None,
                            segment.generic_args.as_ref(),
                        )
                    })
                }
                _ => None,
            }
        {
            return self.check_member_call(
                callee,
                callee_span,
                call_span,
                recv_ty,
                member,
                is_method_call,
                args,
                receiver_hir_id,
                generic_args,
            );
        }

        self.check_direct_call(callee, callee_span, call_span, args)
    }

    // Direct calls

    fn check_direct_call(
        &mut self,
        callee: &Expr,
        callee_span: Span,
        call_span: Span,
        args: &ThinVec<Expr>,
    ) -> Ty {
        let callee_ty = self.check_expr(callee);
        let callee_ty = self.typeck.icx.resolve(&callee_ty);
        let callee_ty = self.typeck.normalize_type_alias(&callee_ty);
        self.node_types.insert(callee.hir_id, callee_ty.clone());
        match callee_ty {
            Ty::Fn {
                params: param_tys,
                ret,
            } => {
                if !self.check_call_args(args, &param_tys, None, false, call_span, None) {
                    return Ty::Error;
                }

                *ret
            }
            _ => {
                builders::emit_at(
                    self.typeck.ctx,
                    callee_span,
                    self.module_id,
                    diag::CallNonFunction,
                    diag_params! {},
                );
                Ty::Error
            }
        }
    }

    fn check_call_args(
        &mut self,
        args: &ThinVec<Expr>,
        param_tys: &[Ty],
        recv_ty: Option<&Ty>,
        is_method_call: bool,
        call_span: Span,
        receiver_hir_id: Option<HirId>,
    ) -> bool {
        let param_tys_without_self = if is_method_call && !param_tys.is_empty() {
            &param_tys[1..]
        } else {
            param_tys
        };

        if args.len() != param_tys_without_self.len() {
            let expected = param_tys_without_self.len();
            builders::emit_at(
                self.typeck.ctx,
                call_span,
                self.module_id,
                diag::UnexpectedParameters,
                diag_params! {
                    expected = expected,
                    s = if expected == 1 { "" } else { "s" },
                    found = args.len()
                },
            );
            return false;
        }

        if let Some(recv_ty) = recv_ty {
            self.apply_auto_ref_adjustment(
                recv_ty,
                param_tys,
                is_method_call,
                call_span,
                receiver_hir_id,
            );
        }

        for (i, arg) in args.iter().enumerate() {
            let arg_span = arg.span;
            let arg_ty = self.check_expr(arg);
            let expected_ty = &param_tys_without_self[i];

            self.typeck
                .unify(expected_ty, &arg_ty, arg_span, self.module_id)
                .or_push_err(&mut self.typeck.icx);
        }

        true
    }

    // Member calls

    #[allow(clippy::too_many_arguments)]
    fn check_member_call(
        &mut self,
        callee: &Expr,
        callee_span: Span,
        call_span: Span,
        recv_ty: Ty,
        member: Symbol,
        is_method_call: bool,
        args: &ThinVec<Expr>,
        receiver_hir_id: Option<HirId>,
        explicit_generic_args: Option<&ThinVec<hir::Ty>>,
    ) -> Ty {
        let recv_ty = self.typeck.normalize_type_alias(&recv_ty);
        let candidates = self.resolve_method_candidates(&recv_ty, member);
        if candidates.is_empty() {
            builders::emit_at(
                self.typeck.ctx,
                callee_span,
                self.module_id,
                diag::MethodNotFound,
                diag_params! {
                    method = member,
                    type = ty_display(&recv_ty, self.typeck.resolver, &self.typeck.ctx.interner)
                },
            );
            return Ty::Error;
        }

        // Type-check args once (side effects: node_types, adjustments)
        let arg_tys: ThinVec<Ty> = args.iter().map(|arg| self.check_expr(arg)).collect();

        for (def_id, kind) in &candidates {
            let Some(mut scheme) = self.typeck.item_schemes.get(def_id).cloned() else {
                continue;
            };

            if let MethodKind::Trait { trait_, impl_def } = kind
                && let Some(trait_scheme) = self.typeck.item_schemes.get(trait_)
                && let Some(Some(args)) = self
                    .typeck
                    .coherence
                    .impl_resolved_generic_args
                    .get(impl_def)
            {
                let mut subst = FxHashMap::default();
                for (&var, arg) in trait_scheme.vars.iter().zip(args.iter()) {
                    subst.insert(var, arg.clone());
                }
                if !subst.is_empty() {
                    scheme.body = substitute_ty_vars(&scheme.body, &subst);
                }
            }

            // Substitute receiver's concrete type args into the method scheme,
            // so that e.g. Foo::<u32>::do_stuff(&foo) checks that foo: Foo<u32>
            let scheme = self.fold_recv_into_scheme(def_id, scheme, &recv_ty);

            let snap = self.typeck.icx.snapshot();

            // Silently skip arity-mismatched candidates during speculative probing;
            // diagnostics are deferred to the fallback path (all candidates failed).
            if let Some(args) = explicit_generic_args {
                let mut completed = args.clone();
                let method_var_len = scheme.vars.len() - self.parent_var_count(*def_id);
                if !self.try_complete_generic_args(*def_id, &mut completed, method_var_len) {
                    self.typeck.icx.rollback(snap);
                    continue;
                }
            }

            let Ok(instantiated) = self.instantiate_fn_scheme(
                *def_id,
                &scheme,
                explicit_generic_args,
                callee_span,
                true,
            ) else {
                self.typeck.icx.rollback(snap);
                continue;
            };
            let Ty::Fn {
                params: param_tys,
                ret,
            } = instantiated
            else {
                self.typeck.icx.rollback(snap);
                continue;
            };

            let before_errors = self.typeck.icx.errors.len();

            if !self.try_match_method_args(
                &recv_ty,
                &param_tys,
                &arg_tys,
                is_method_call,
                call_span,
            ) {
                self.typeck.icx.rollback(snap);
                continue;
            }

            if self.typeck.icx.errors.len() != before_errors {
                self.typeck.icx.rollback(snap);
                continue;
            }

            // Success, keep bindings and finalize
            self.apply_auto_ref_adjustment(
                &recv_ty,
                &param_tys,
                is_method_call,
                call_span,
                receiver_hir_id,
            );
            self.node_types.insert(callee.hir_id, recv_ty.clone());
            self.member_res.insert(
                callee.hir_id,
                MemberRes::Method {
                    def_id: *def_id,
                    kind: *kind,
                },
            );

            let ret = self.typeck.icx.resolve(&ret);
            let ret = if let Ty::Adt(recv_id, Some(recv_args)) = self.typeck.icx.resolve(&recv_ty) {
                let recv_args = recv_args.clone();
                fold_ty(&ret, &mut |ty| match ty {
                    Ty::Adt(id, None) if id == recv_id => Ty::Adt(id, Some(recv_args.clone())),
                    t => t,
                })
            } else {
                ret
            };
            return self.typeck.normalize_type_alias(&ret);
        }

        // All candidates failed
        let (def_id, kind) = candidates.first().expect("candidates not empty");
        let Some(mut scheme) = self.typeck.item_schemes.get(def_id).cloned() else {
            return Ty::Error;
        };

        if let MethodKind::Trait { trait_, impl_def } = kind
            && let Some(trait_scheme) = self.typeck.item_schemes.get(trait_)
            && let Some(Some(args)) = self
                .typeck
                .coherence
                .impl_resolved_generic_args
                .get(impl_def)
        {
            let mut subst = FxHashMap::default();
            for (&var, arg) in trait_scheme.vars.iter().zip(args.iter()) {
                subst.insert(var, arg.clone());
            }
            if !subst.is_empty() {
                scheme.body = substitute_ty_vars(&scheme.body, &subst);
            }
        }

        let scheme = self.fold_recv_into_scheme(def_id, scheme, &recv_ty);
        let instantiated = match self.instantiate_fn_scheme(
            *def_id,
            &scheme,
            explicit_generic_args,
            callee_span,
            false,
        ) {
            Ok(ty) => ty,
            Err(err) => {
                self.report_ty_from_hir_error(err);
                return Ty::Error;
            }
        };
        let Ty::Fn {
            params: param_tys, ..
        } = instantiated
        else {
            return Ty::Error;
        };

        let param_tys_without_self = if is_method_call && !param_tys.is_empty() {
            &param_tys[1..]
        } else {
            &param_tys
        };

        if arg_tys.len() != param_tys_without_self.len() {
            let expected = param_tys_without_self.len();
            builders::emit_at(
                self.typeck.ctx,
                call_span,
                self.module_id,
                diag::UnexpectedParameters,
                diag_params! {
                    expected = expected,
                    s = if expected == 1 { "" } else { "s" },
                    found = arg_tys.len()
                },
            );
        } else {
            if is_method_call && !param_tys.is_empty() {
                let first = param_tys.first().expect("method has at least 1 param");
                let (target, _) = self.receiver_auto_ref(&recv_ty, first);
                self.typeck
                    .unify(&target, &recv_ty, call_span, self.module_id)
                    .or_push_err(&mut self.typeck.icx);
            }
            for ((arg, arg_ty), param_ty) in
                args.iter().zip(arg_tys.iter()).zip(param_tys_without_self)
            {
                self.typeck
                    .unify(param_ty, arg_ty, arg.span, self.module_id)
                    .or_push_err(&mut self.typeck.icx);
            }
        }
        Ty::Error
    }

    fn fold_recv_into_scheme(&self, def_id: &DefId, scheme: Scheme, recv_ty: &Ty) -> Scheme {
        let Ty::Adt(_, Some(recv_args)) = recv_ty else {
            return scheme;
        };

        let parent_def_id = self
            .typeck
            .coherence
            .assoc_to_parent
            .get(def_id)
            .expect("assoc item has parent");

        let parent_info = self
            .typeck
            .coherence
            .generic_params
            .get(parent_def_id)
            .expect("assoc item parent has generic params");

        let parent_var_count = parent_info.hir_ids.len();
        if parent_var_count == 0 {
            return scheme;
        }

        assert!(scheme.vars.len() >= parent_var_count);
        assert!(recv_args.len() >= parent_var_count);

        let subst: FxHashMap<_, _> = scheme
            .vars
            .iter()
            .take(parent_var_count)
            .copied()
            .zip(recv_args.iter().take(parent_var_count).cloned())
            .collect();

        Scheme {
            vars: scheme.vars,
            body: substitute_ty_vars(&scheme.body, &subst),
        }
    }

    fn try_match_method_args(
        &mut self,
        recv_ty: &Ty,
        param_tys: &[Ty],
        arg_tys: &[Ty],
        is_method_call: bool,
        call_span: Span,
    ) -> bool {
        let param_tys_withut_self = if is_method_call && !param_tys.is_empty() {
            &param_tys[1..]
        } else {
            param_tys
        };

        if arg_tys.len() != param_tys_withut_self.len() {
            return false;
        }

        // Match receiver against first param
        if is_method_call && !param_tys.is_empty() {
            let first = param_tys.first().expect("method has at least 1 param");
            let (target, _) = self.receiver_auto_ref(recv_ty, first);
            if self
                .typeck
                .unify(&target, recv_ty, call_span, self.module_id)
                .is_err()
            {
                return false;
            }
        }

        for (arg_ty, param_ty) in arg_tys.iter().zip(param_tys_withut_self) {
            if self
                .typeck
                .unify(param_ty, arg_ty, call_span, self.module_id)
                .is_err()
            {
                return false;
            }
        }

        true
    }

    fn resolve_method_candidates(&self, recv_ty: &Ty, member: Symbol) -> Vec<(DefId, MethodKind)> {
        let recv_ty = self.typeck.icx.resolve(recv_ty);
        let Ty::Adt(struct_id, _) = recv_ty else {
            return vec![];
        };

        let mut candidates = vec![];

        if let Some(method) = self.typeck.coherence.inherent_methods.get(&struct_id)
            && let Some(&method_def_id) = method.get(&member)
        {
            candidates.push((method_def_id, MethodKind::Inherent));
        }

        if let Some(method) = self.typeck.coherence.struct_trait_methods.get(&struct_id)
            && let Some(entries) = method.get(&member)
        {
            for &(trait_, method_def_id) in entries {
                if let Some(impl_def_ids) = self.typeck.coherence.impls.get(&(trait_, struct_id)) {
                    for &impl_def in impl_def_ids {
                        candidates.push((method_def_id, MethodKind::Trait { trait_, impl_def }));
                    }
                }
            }
        }

        candidates
    }

    // Shared by direct and member calls

    /// Decide whether the receiver should be auto-referenced to match a
    /// `&Self` first parameter. Returns the type to unify against the
    /// receiver and, when auto-reference applies, the pointer's mutability.
    fn receiver_auto_ref(&self, recv_ty: &Ty, first_param: &Ty) -> (Ty, Option<Mutability>) {
        let arg_r = self.typeck.icx.resolve(recv_ty);
        let param_r = self.typeck.icx.resolve(first_param);
        if !matches!(arg_r, Ty::Ptr(..) | Ty::Var(_))
            && let Ty::Ptr(inner, mutability) = param_r
        {
            (*inner, Some(mutability))
        } else {
            (first_param.clone(), None)
        }
    }

    pub fn apply_auto_ref_adjustment(
        &mut self,
        recv_ty: &Ty,
        param_tys: &[Ty],
        is_method_call: bool,
        call_span: Span,
        receiver_hir_id: Option<HirId>,
    ) {
        if is_method_call && !param_tys.is_empty() {
            let first = param_tys.first().expect("method has at least 1 param");
            let (target, auto_ref) = self.receiver_auto_ref(recv_ty, first);
            if let (Some(hir_id), Some(mutability)) = (receiver_hir_id, auto_ref) {
                self.adjustments
                    .entry(hir_id)
                    .or_default()
                    .push(Adjustment::AutoRef(mutability));
            }
            self.typeck
                .unify(&target, recv_ty, call_span, self.module_id)
                .or_push_err(&mut self.typeck.icx);
        }
    }
}
