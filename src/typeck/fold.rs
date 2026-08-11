use thin_vec::ThinVec;

use crate::hir::{DefId, HirId};
use crate::resolve::Res;
use crate::typeck::Ty;
use crate::typeck::infctx::TyVarId;
use crate::typeck::types::Scheme;
use fxhash::{FxHashMap, FxHashSet};

pub fn res_to_def_id(res: Res<HirId>) -> Option<DefId> {
    match res {
        Res::Def(def_id) | Res::SelfTyAlias { alias_to: def_id } => Some(def_id),
        _ => None,
    }
}

pub fn fold_ty<F>(ty: &Ty, f: &mut F) -> Ty
where
    F: FnMut(Ty) -> Ty,
{
    try_fold_ty(ty, &mut |ty| Ok::<_, std::convert::Infallible>(f(ty)))
        .unwrap_or_else(|infallible| match infallible {})
}

pub fn try_fold_ty<F, E>(ty: &Ty, f: &mut F) -> Result<Ty, E>
where
    F: FnMut(Ty) -> Result<Ty, E>,
{
    let ty = match ty {
        Ty::Var(_) | Ty::Prim(_) | Ty::Never | Ty::MethodCallee | Ty::Error => ty.clone(),
        Ty::Adt(d, generics) => Ty::Adt(*d, try_fold_generics(generics, f)?),
        Ty::Alias {
            def_id,
            generic_args,
        } => Ty::Alias {
            def_id: *def_id,
            generic_args: try_fold_generics(generic_args, f)?,
        },
        Ty::Ptr(inner, m) => Ty::Ptr(try_fold_ty(inner, f)?.into_box(), *m),
        Ty::Slice(inner) => Ty::Slice(try_fold_ty(inner, f)?.into_box()),
        Ty::Array(inner, n) => Ty::Array(try_fold_ty(inner, f)?.into_box(), *n),
        Ty::Fn { params, ret } => Ty::Fn {
            params: params
                .iter()
                .map(|ty| try_fold_ty(ty, f))
                .collect::<Result<ThinVec<_>, _>>()?,
            ret: try_fold_ty(ret, f)?.into_box(),
        },
        Ty::Tuple(elements) => Ty::Tuple(
            elements
                .iter()
                .map(|ty| try_fold_ty(ty, f))
                .collect::<Result<ThinVec<_>, _>>()?,
        ),
        Ty::Projection {
            trait_def_id,
            assoc_def_id,
            self_ty,
            generic_args,
            trait_generic_args,
        } => Ty::Projection {
            self_ty: try_fold_ty(self_ty, f)?.into_box(),
            generic_args: try_fold_generics(generic_args, f)?,
            trait_generic_args: try_fold_generics(trait_generic_args, f)?,
            trait_def_id: *trait_def_id,
            assoc_def_id: *assoc_def_id,
        },
    };

    f(ty)
}

fn try_fold_generics<F, E>(
    generic_args: &Option<ThinVec<Ty>>,
    f: &mut F,
) -> Result<Option<ThinVec<Ty>>, E>
where
    F: FnMut(Ty) -> Result<Ty, E>,
{
    generic_args
        .as_ref()
        .map(|args| {
            args.iter()
                .map(|ty| try_fold_ty(ty, f))
                .collect::<Result<ThinVec<_>, _>>()
        })
        .transpose()
}

pub fn substitute_ty_vars(ty: &Ty, mapping: &FxHashMap<TyVarId, Ty>) -> Ty {
    fold_ty(ty, &mut |ty| match ty {
        Ty::Var(v) => mapping.get(&v).cloned().unwrap_or(Ty::Var(v)),
        ty => ty,
    })
}

pub fn resolve_scheme_with_args(scheme: &Scheme, generic_args: &Option<ThinVec<Ty>>) -> Option<Ty> {
    let resolved = match generic_args {
        Some(args) if args.len() == scheme.vars.len() => {
            let mapping: FxHashMap<TyVarId, Ty> = scheme
                .vars
                .iter()
                .copied()
                .zip(args.iter().cloned())
                .collect();
            substitute_ty_vars(&scheme.body, &mapping)
        }
        _ if scheme.vars.is_empty() => scheme.body.clone(),
        _ => return None,
    };
    Some(resolved)
}

pub fn expand_type_alias(
    def_id: DefId,
    generic_args: &Option<ThinVec<Ty>>,
    in_progress: &mut FxHashSet<DefId>,
    expanded: impl FnOnce(&mut FxHashSet<DefId>, DefId, &Option<ThinVec<Ty>>) -> Ty,
) -> Ty {
    if !in_progress.insert(def_id) {
        return Ty::Error;
    }
    let result = expanded(in_progress, def_id, generic_args);
    in_progress.remove(&def_id);
    result
}

pub fn try_expand_type_alias<E>(
    def_id: DefId,
    generic_args: &Option<ThinVec<Ty>>,
    in_progress: &mut FxHashSet<DefId>,
    expanded: impl FnOnce(&mut FxHashSet<DefId>, DefId, &Option<ThinVec<Ty>>) -> Result<Ty, E>,
) -> Result<Ty, E> {
    if !in_progress.insert(def_id) {
        return Ok(Ty::Error);
    }
    let result = expanded(in_progress, def_id, generic_args);
    in_progress.remove(&def_id);
    result
}
