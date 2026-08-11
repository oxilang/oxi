use crate::ast::visit::VisitAction;
use crate::hir::{FloatTy, IntTy, ModuleId, PrimTy};
use crate::span::Span;
use crate::typeck::infctx::{InferCtx, TyVarId, TyVarSource};
use crate::typeck::types::Ty;
use crate::typeck::{TyVisitable, TyVisitor, Typeck};
use thin_vec::ThinVec;

#[derive(Debug, Clone)]
pub enum UnifyError {
    /// Cannot unify `expected` and `found`
    Mismatch {
        expected: Ty,
        found: Ty,
        span: Span,
        module_id: ModuleId,
    },
    /// Unification variable contains itself
    OccursCheck {
        var: TyVarId,
        span: Span,
        module_id: ModuleId,
    },
}

pub type UnifyResult<T> = Result<T, UnifyError>;

pub trait OrPushErr {
    fn or_push_err(self, icx: &mut InferCtx);
}

impl<T> OrPushErr for UnifyResult<T> {
    fn or_push_err(self, icx: &mut InferCtx) {
        if let Err(err) = self {
            icx.errors.push(err);
        }
    }
}

impl<'ctx, 'hir, 'res> Typeck<'ctx, 'hir, 'res> {
    pub fn unify(&mut self, a: &Ty, b: &Ty, span: Span, module_id: ModuleId) -> UnifyResult<()> {
        let a = self.icx.resolve(a);
        let b = self.icx.resolve(b);
        match (&a, &b) {
            (Ty::Error, _) | (_, Ty::Error) => Ok(()),
            (Ty::Never, _) | (_, Ty::Never) => Ok(()),
            (Ty::MethodCallee, _) | (_, Ty::MethodCallee) => Ok(()),
            (Ty::Var(v), t) | (t, Ty::Var(v)) => {
                let t = match t {
                    Ty::Projection { .. } | Ty::Alias { .. } => self.normalize_type_alias(t),
                    _ => t.clone(),
                };
                bind(&mut self.icx, *v, &t, span, module_id)
            }
            (Ty::Prim(p1), Ty::Prim(p2)) => {
                if p1 == p2 {
                    Ok(())
                } else {
                    Err(mismatch(a, b, span, module_id))
                }
            }
            (Ty::Ptr(i1, m1), Ty::Ptr(i2, m2)) => {
                if m1 == m2 {
                    self.unify(i1, i2, span, module_id)
                } else {
                    Err(mismatch(a, b, span, module_id))
                }
            }
            (Ty::Slice(i1), Ty::Slice(i2)) => self.unify(i1, i2, span, module_id),
            (Ty::Adt(d1, g1), Ty::Adt(d2, g2)) => {
                if d1 == d2 {
                    if let (Some(g1), Some(g2)) = (g1, g2) {
                        if g1.len() != g2.len() {
                            return Err(mismatch(a, b, span, module_id));
                        }
                        for (a, b) in g1.iter().zip(g2) {
                            self.unify(a, b, span, module_id)?;
                        }
                    }
                    Ok(())
                } else {
                    Err(mismatch(a, b, span, module_id))
                }
            }
            (Ty::Array(i1, n1), Ty::Array(i2, n2)) => {
                if n1 == n2 {
                    self.unify(i1, i2, span, module_id)
                } else {
                    Err(mismatch(a, b, span, module_id))
                }
            }
            (
                Ty::Fn {
                    params: p1,
                    ret: r1,
                },
                Ty::Fn {
                    params: p2,
                    ret: r2,
                },
            ) => {
                if p1.len() != p2.len() {
                    return Err(mismatch(a, b, span, module_id));
                }
                for (a, b) in p1.iter().zip(p2) {
                    self.unify(a, b, span, module_id)?;
                }
                self.unify(r1, r2, span, module_id)
            }
            (Ty::Tuple(e1), Ty::Tuple(e2)) => {
                if e1.len() != e2.len() {
                    return Err(mismatch(a, b, span, module_id));
                }
                for (a, b) in e1.iter().zip(e2) {
                    self.unify(a, b, span, module_id)?;
                }
                Ok(())
            }
            (Ty::Projection { .. }, Ty::Projection { .. }) => {
                let a = self.normalize_type_alias(&a);
                let b = self.normalize_type_alias(&b);
                if let (
                    Ty::Projection {
                        trait_def_id: t1,
                        assoc_def_id: ad1,
                        self_ty: s1,
                        generic_args: g1,
                        trait_generic_args: tg1,
                    },
                    Ty::Projection {
                        trait_def_id: t2,
                        assoc_def_id: ad2,
                        self_ty: s2,
                        generic_args: g2,
                        trait_generic_args: tg2,
                    },
                ) = (&a, &b)
                {
                    if t1 == t2 && ad1 == ad2 {
                        self.unify(s1, s2, span, module_id)?;
                        self.unify_alias_args(g1, g2, &a, &b, span, module_id)?;
                        self.unify_alias_args(tg1, tg2, &a, &b, span, module_id)?;
                        Ok(())
                    } else {
                        Err(mismatch(a, b, span, module_id))
                    }
                } else {
                    self.unify(&a, &b, span, module_id)
                }
            }
            (Ty::Projection { .. }, _) => {
                let a = self.normalize_type_alias(&a);
                let b = self.normalize_type_alias(&b);
                if matches!(&a, Ty::Projection { .. }) {
                    Err(mismatch(a, b, span, module_id))
                } else {
                    self.unify(&a, &b, span, module_id)
                }
            }
            (_, Ty::Projection { .. }) => {
                let a = self.normalize_type_alias(&a);
                let b = self.normalize_type_alias(&b);
                if matches!(&b, Ty::Projection { .. }) {
                    Err(mismatch(a, b, span, module_id))
                } else {
                    self.unify(&a, &b, span, module_id)
                }
            }
            (Ty::Alias { .. }, _) => {
                let a = self.normalize_type_alias(&a);
                if matches!(&a, Ty::Alias { .. }) {
                    Err(mismatch(a, b, span, module_id))
                } else {
                    self.unify(&a, &b, span, module_id)
                }
            }
            (_, Ty::Alias { .. }) => {
                let b = self.normalize_type_alias(&b);
                if matches!(&b, Ty::Alias { .. }) {
                    Err(mismatch(a, b, span, module_id))
                } else {
                    self.unify(&a, &b, span, module_id)
                }
            }
            _ => Err(mismatch(a, b, span, module_id)),
        }
    }

    fn unify_alias_args(
        &mut self,
        left: &Option<ThinVec<Ty>>,
        right: &Option<ThinVec<Ty>>,
        a: &Ty,
        b: &Ty,
        span: Span,
        module_id: ModuleId,
    ) -> UnifyResult<()> {
        match (left, right) {
            (Some(left), Some(right)) => {
                if left.len() != right.len() {
                    return Err(mismatch(a.clone(), b.clone(), span, module_id));
                }
                for (x, y) in left.iter().zip(right) {
                    self.unify(x, y, span, module_id)?;
                }
            }
            (None, None) => {}
            _ => return Err(mismatch(a.clone(), b.clone(), span, module_id)),
        }
        Ok(())
    }
}

fn bind(
    icx: &mut InferCtx,
    var: TyVarId,
    to: &Ty,
    span: Span,
    module_id: ModuleId,
) -> UnifyResult<()> {
    let to = icx.resolve(to);
    if let Ty::Var(other) = &to
        && *other == var
    {
        return Ok(());
    }
    match icx.ty_var_source(var) {
        TyVarSource::IntLit => match &to {
            Ty::Var(to_var) if matches!(icx.ty_var_source(*to_var), TyVarSource::IntLit) => {}
            Ty::Prim(PrimTy::Int(_) | PrimTy::Uint(_)) => {}
            _ => {
                return Err(mismatch(
                    to.clone(),
                    Ty::Prim(PrimTy::Int(IntTy::I32)),
                    span,
                    module_id,
                ));
            }
        },
        TyVarSource::FloatLit => match &to {
            Ty::Var(to_var) if matches!(icx.ty_var_source(*to_var), TyVarSource::FloatLit) => {}
            Ty::Prim(PrimTy::Float(_)) => {}
            _ => {
                return Err(mismatch(
                    to.clone(),
                    Ty::Prim(PrimTy::Float(FloatTy::F64)),
                    span,
                    module_id,
                ));
            }
        },
        TyVarSource::Generic | TyVarSource::EmptyArray => {}
    }
    if occurs(icx, var, &to) {
        return Err(UnifyError::OccursCheck {
            var,
            span,
            module_id,
        });
    }
    let var_level = icx.ty_var(var).level;
    let adjusted = icx.adjust(&to, var_level + 1);
    icx.set_root(var, adjusted);
    Ok(())
}

fn occurs(icx: &InferCtx, var: TyVarId, to: &Ty) -> bool {
    struct OccursVisitor<'a> {
        icx: &'a InferCtx,
        target: TyVarId,
        occurs: bool,
    }

    impl TyVisitor for OccursVisitor<'_> {
        fn visit_ty(&mut self, ty: &Ty) -> VisitAction {
            if self.occurs {
                return VisitAction::SkipChildren;
            }

            let Ty::Var(var) = ty else {
                return VisitAction::Continue;
            };
            if *var == self.target {
                self.occurs = true;
            } else if let Some(bound) = self.icx.root_of(*var) {
                bound.visit(self);
            }

            VisitAction::SkipChildren
        }
    }

    let mut visitor = OccursVisitor {
        icx,
        target: var,
        occurs: false,
    };
    to.visit(&mut visitor);
    visitor.occurs
}

fn mismatch(expected: Ty, found: Ty, span: Span, module_id: ModuleId) -> UnifyError {
    UnifyError::Mismatch {
        expected,
        found,
        span,
        module_id,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::Ctx;
    use crate::hir::{Crate, Def, DefId, DefKind, IntTy, PrimTy, UintTy};
    use crate::resolve::{PerModule, ResolverOutputs};
    use crate::typeck::types::Scheme;
    use fxhash::FxHashMap;
    use thin_vec::thin_vec;

    const NO_MODULE: ModuleId = ModuleId(0);

    fn no_span() -> Span {
        Span::new(0, 0)
    }

    fn int() -> Ty {
        Ty::Prim(PrimTy::Int(IntTy::I32))
    }

    fn assoc_type_def() -> Def {
        Def {
            name: Some(0),
            visibility: None,
            kind: DefKind::AssocType,
            span: no_span(),
        }
    }

    fn projection(
        trait_def_id: DefId,
        assoc_def_id: DefId,
        generic_args: Option<thin_vec::ThinVec<Ty>>,
    ) -> Ty {
        Ty::Projection {
            trait_def_id,
            assoc_def_id,
            self_ty: Box::new(int()),
            generic_args,
            trait_generic_args: None,
        }
    }

    fn projection_with_trait_args(
        trait_def_id: DefId,
        assoc_def_id: DefId,
        generic_args: Option<thin_vec::ThinVec<Ty>>,
        trait_generic_args: Option<thin_vec::ThinVec<Ty>>,
    ) -> Ty {
        Ty::Projection {
            trait_def_id,
            assoc_def_id,
            self_ty: Box::new(int()),
            generic_args,
            trait_generic_args,
        }
    }

    fn typeck() -> Typeck<'static, 'static, 'static> {
        let ctx = Box::leak(Box::new(Ctx::new()));
        let krate = Box::leak(Box::new(Crate::new()));
        // `resolver.def` indexes `defs` directly; the projection-normalization
        // code reads the assoc type's name, so pre-populate spare entries.
        let defs: thin_vec::ThinVec<Def> = (0..4).map(|_| assoc_type_def()).collect();
        let resolver = Box::leak(Box::new(ResolverOutputs {
            res_map: FxHashMap::default(),
            def_map: FxHashMap::default(),
            defs,
            modules: PerModule::new(0),
            def_to_module: FxHashMap::default(),
        }));
        Typeck::new(ctx, krate, resolver)
    }

    #[test]
    fn unify_same_prim() {
        let mut tc = typeck();
        assert!(tc.unify(&int(), &int(), no_span(), NO_MODULE).is_ok());
    }

    #[test]
    fn unify_different_prims_fails() {
        let mut tc = typeck();
        let u8 = Ty::Prim(PrimTy::Uint(UintTy::U8));
        assert!(tc.unify(&int(), &u8, no_span(), NO_MODULE).is_err());
    }

    #[test]
    fn unify_var_with_concrete() {
        let mut tc = typeck();
        let v = tc.icx.next_ty_var();
        assert!(tc.unify(&Ty::Var(v), &int(), no_span(), NO_MODULE).is_ok());
        assert!(matches!(
            tc.icx.resolve(&Ty::Var(v)),
            Ty::Prim(PrimTy::Int(IntTy::I32))
        ));
    }

    #[test]
    fn unify_two_vars_binds_them() {
        let mut tc = typeck();
        let a = tc.icx.next_ty_var();
        let b = tc.icx.next_ty_var();
        assert!(
            tc.unify(&Ty::Var(a), &Ty::Var(b), no_span(), NO_MODULE)
                .is_ok()
        );
        let ra = tc.icx.resolve(&Ty::Var(a));
        let rb = tc.icx.resolve(&Ty::Var(b));
        assert!(matches!(ra, Ty::Var(_)));
        assert!(matches!(rb, Ty::Var(_)));
    }

    #[test]
    fn unify_fn_types() {
        let mut tc = typeck();
        let a = Ty::Fn {
            params: thin_vec![int()],
            ret: Box::new(int()),
        };
        let b = Ty::Fn {
            params: thin_vec![int()],
            ret: Box::new(int()),
        };
        assert!(tc.unify(&a, &b, no_span(), NO_MODULE).is_ok());
    }

    #[test]
    fn unify_fn_arity_mismatch() {
        let mut tc = typeck();
        let a = Ty::Fn {
            params: thin_vec![int()],
            ret: Box::new(int()),
        };
        let b = Ty::Fn {
            params: thin_vec![],
            ret: Box::new(int()),
        };
        assert!(tc.unify(&a, &b, no_span(), NO_MODULE).is_err());
    }

    #[test]
    fn occurs_check() {
        let mut tc = typeck();
        let v = tc.icx.next_ty_var();
        let bad = Ty::Fn {
            params: thin_vec![Ty::Var(v)],
            ret: Box::new(int()),
        };
        assert!(tc.unify(&Ty::Var(v), &bad, no_span(), NO_MODULE).is_err());
    }

    #[test]
    fn error_ty_unifies_with_anything() {
        let mut tc = typeck();
        assert!(tc.unify(&Ty::Error, &int(), no_span(), NO_MODULE).is_ok());
        assert!(tc.unify(&int(), &Ty::Error, no_span(), NO_MODULE).is_ok());
    }

    #[test]
    fn never_unifies_with_everything() {
        let mut tc = typeck();
        assert!(tc.unify(&Ty::Never, &int(), no_span(), NO_MODULE).is_ok());
        let v = tc.icx.next_ty_var();
        assert!(
            tc.unify(&Ty::Var(v), &Ty::Never, no_span(), NO_MODULE)
                .is_ok()
        );
    }

    #[test]
    fn unify_same_adt() {
        let mut tc = typeck();
        let a = Ty::Adt(DefId(7), None);
        let b = Ty::Adt(DefId(7), None);
        assert!(tc.unify(&a, &b, no_span(), NO_MODULE).is_ok());
    }

    #[test]
    fn unify_different_adts_fails() {
        let mut tc = typeck();
        let a = Ty::Adt(DefId(7), None);
        let b = Ty::Adt(DefId(8), None);
        assert!(tc.unify(&a, &b, no_span(), NO_MODULE).is_err());
    }

    #[test]
    fn unify_adt_with_ptr_inner_succeeds_after_autoref() {
        let mut tc = typeck();
        let param = Ty::Ptr(
            Box::new(Ty::Adt(DefId(3), None)),
            crate::ast::Mutability::Constant,
        );
        let arg = Ty::Adt(DefId(3), None);
        let inner = match &param {
            Ty::Ptr(i, _) => i.as_ref().clone(),
            _ => unreachable!(),
        };
        assert!(tc.unify(&inner, &arg, no_span(), NO_MODULE).is_ok());
    }

    #[test]
    fn unify_matching_projection_succeeds() {
        let mut tc = typeck();
        let a = projection(DefId(0), DefId(1), None);
        let b = projection(DefId(0), DefId(1), None);
        assert!(tc.unify(&a, &b, no_span(), NO_MODULE).is_ok());
    }

    #[test]
    fn unify_projection_mismatched_assoc_id_fails() {
        let mut tc = typeck();
        let a = projection(DefId(0), DefId(1), None);
        let b = projection(DefId(0), DefId(2), None);
        assert!(tc.unify(&a, &b, no_span(), NO_MODULE).is_err());
    }

    #[test]
    fn unify_projection_generic_args_presence_mismatch_fails() {
        let mut tc = typeck();
        let a = projection(DefId(0), DefId(1), Some(thin_vec![int()]));
        let b = projection(DefId(0), DefId(1), None);
        assert!(tc.unify(&a, &b, no_span(), NO_MODULE).is_err());
    }

    #[test]
    fn unify_projection_trait_generic_args_presence_mismatch_fails() {
        let mut tc = typeck();
        let a = projection_with_trait_args(DefId(0), DefId(1), None, Some(thin_vec![int()]));
        let b = projection_with_trait_args(DefId(0), DefId(1), None, None);
        assert!(tc.unify(&a, &b, no_span(), NO_MODULE).is_err());
    }

    #[test]
    fn unify_projection_matching_trait_generic_args_succeeds() {
        let mut tc = typeck();
        let a = projection_with_trait_args(DefId(0), DefId(1), None, Some(thin_vec![int()]));
        let b = projection_with_trait_args(DefId(0), DefId(1), None, Some(thin_vec![int()]));
        assert!(tc.unify(&a, &b, no_span(), NO_MODULE).is_ok());
    }

    #[test]
    fn unify_projection_len_mismatched_trait_generic_args_fails() {
        let mut tc = typeck();
        let a = projection_with_trait_args(DefId(0), DefId(1), None, Some(thin_vec![int()]));
        let b = projection_with_trait_args(DefId(0), DefId(1), None, Some(thin_vec![int(), int()]));
        assert!(tc.unify(&a, &b, no_span(), NO_MODULE).is_err());
    }

    #[test]
    fn unify_unexpandable_alias_fails_on_either_side() {
        let mut tc = typeck();
        let alias = Ty::Alias {
            def_id: DefId(9),
            generic_args: None,
        };
        assert!(tc.unify(&alias, &int(), no_span(), NO_MODULE).is_err());
        assert!(tc.unify(&int(), &alias, no_span(), NO_MODULE).is_err());
    }

    #[test]
    fn unify_alias_with_scheme_expands_to_concrete() {
        let mut tc = typeck();
        tc.item_schemes.insert(DefId(9), Scheme::monomorphic(int()));
        let alias = Ty::Alias {
            def_id: DefId(9),
            generic_args: None,
        };
        assert!(tc.unify(&alias, &int(), no_span(), NO_MODULE).is_ok());
        assert!(tc.unify(&int(), &alias, no_span(), NO_MODULE).is_ok());
    }

    #[test]
    fn unify_projection_normalizes_alias_on_other_side_before_mismatch() {
        let mut tc = typeck();
        // The alias expands to `i32`; the projection stays unexpanded (its self
        // type is a primitive here, so no impl applies), so both directions
        // remain mismatches, but the alias operand is reported in expanded form.
        tc.item_schemes.insert(DefId(9), Scheme::monomorphic(int()));
        let alias = Ty::Alias {
            def_id: DefId(9),
            generic_args: None,
        };
        let proj = projection(DefId(0), DefId(1), None);
        let err = tc
            .unify(&alias, &proj, no_span(), NO_MODULE)
            .expect_err("alias vs projection must mismatch");
        assert!(
            matches!(err, UnifyError::Mismatch { expected, found, .. } if expected == int() && matches!(found, Ty::Projection { .. }))
        );
        let err = tc
            .unify(&proj, &alias, no_span(), NO_MODULE)
            .expect_err("projection vs alias must mismatch");
        assert!(
            matches!(err, UnifyError::Mismatch { expected, found, .. } if matches!(expected, Ty::Projection { .. }) && found == int())
        );
    }
}
