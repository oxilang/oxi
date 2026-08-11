use thin_vec::ThinVec;

use crate::hir::{HirId, ModuleId};
use crate::span::Span;
use crate::typeck::fold::fold_ty;
use crate::typeck::types::{Scheme, Ty};
use crate::typeck::unify::UnifyError;
use fxhash::{FxHashMap, FxHashSet};

#[derive(Debug)]
pub struct Snapshot {
    vars_len: usize,
    errors_len: usize,
    roots: FxHashMap<TyVarId, Option<Ty>>,
    levels: FxHashMap<TyVarId, u32>,
}

crate::newtype_ids!(TyVarId);

#[derive(Debug, PartialEq, Eq)]
pub enum TyVarSource {
    Generic,
    IntLit,
    FloatLit,
    EmptyArray,
}

#[derive(Debug)]
pub struct TyVar {
    pub(super) level: u32,
    /// Some() if this var has been bound
    root: Option<Ty>,
    source: TyVarSource,
    span: Option<Span>,
    module_id: Option<ModuleId>,
}

#[derive(Debug, Default)]
pub struct InferCtx {
    vars: Vec<TyVar>,
    levels: Vec<u32>,
    pub(super) errors: Vec<UnifyError>,
    pub(super) hir_id_to_ty_var: FxHashMap<HirId, TyVarId>,
    pub(super) generic_defaults: Vec<(TyVarId, Ty)>,
}

impl InferCtx {
    pub fn push_level(&mut self) {
        self.levels.push(self.levels.len() as u32);
    }

    pub fn pop_level(&mut self) {
        self.levels.pop();
    }

    pub fn current_level(&self) -> u32 {
        *self.levels.last().expect("level exists")
    }

    pub fn next_ty_var(&mut self) -> TyVarId {
        self.next_ty_var_at(self.current_level(), TyVarSource::Generic, None, None)
    }

    pub fn next_ty_var_at_span(&mut self, span: Span) -> TyVarId {
        self.next_ty_var_at(self.current_level(), TyVarSource::Generic, Some(span), None)
    }

    pub fn next_int_var(&mut self, span: Span, module_id: ModuleId) -> TyVarId {
        self.next_ty_var_at(
            self.current_level(),
            TyVarSource::IntLit,
            Some(span),
            Some(module_id),
        )
    }

    pub fn next_float_var(&mut self, span: Span, module_id: ModuleId) -> TyVarId {
        self.next_ty_var_at(
            self.current_level(),
            TyVarSource::FloatLit,
            Some(span),
            Some(module_id),
        )
    }

    pub fn next_ty_var_at(
        &mut self,
        level: u32,
        source: TyVarSource,
        span: Option<Span>,
        module_id: Option<ModuleId>,
    ) -> TyVarId {
        let id = TyVarId(self.vars.len() as u32);
        self.vars.push(TyVar {
            level,
            root: None,
            source,
            span,
            module_id,
        });
        id
    }

    pub fn ty_var(&self, ty_var: TyVarId) -> &TyVar {
        &self.vars[ty_var.0 as usize]
    }

    pub fn ty_var_mut(&mut self, ty_var: TyVarId) -> &mut TyVar {
        &mut self.vars[ty_var.0 as usize]
    }

    pub fn ty_var_span(&self, ty_var: TyVarId) -> Option<Span> {
        self.ty_var(ty_var).span
    }

    pub fn ty_var_module(&self, ty_var: TyVarId) -> ModuleId {
        self.ty_var(ty_var).module_id.unwrap_or(ModuleId(0))
    }

    pub fn set_root(&mut self, ty_var: TyVarId, ty: Ty) {
        self.ty_var_mut(ty_var).root = Some(ty);
    }

    pub fn is_bound(&self, ty_var: TyVarId) -> bool {
        self.ty_var(ty_var).root.is_some()
    }

    pub fn root_of(&self, ty_var: TyVarId) -> Option<&Ty> {
        self.ty_var(ty_var).root.as_ref()
    }

    pub fn ty_var_source(&self, ty_var: TyVarId) -> &TyVarSource {
        &self.ty_var(ty_var).source
    }

    pub fn take_errors(&mut self) -> Vec<UnifyError> {
        std::mem::take(&mut self.errors)
    }

    pub fn alloc_ty_var(&mut self) -> Ty {
        Ty::Var(self.next_ty_var())
    }

    pub fn adjust(&mut self, ty: &Ty, bound: u32) -> Ty {
        fold_ty(ty, &mut |ty| match ty {
            Ty::Var(var) => {
                let level = self.ty_var(var).level;
                if level > bound {
                    self.ty_var_mut(var).level = bound;
                }
                ty
            }
            ty => ty,
        })
    }

    pub fn resolve(&self, ty: &Ty) -> Ty {
        fold_ty(ty, &mut |ty| match ty {
            Ty::Var(var) => match &self.ty_var(var).root {
                Some(bound) => self.resolve(bound),
                None => ty,
            },
            ty => ty,
        })
    }

    pub fn vars_in(&self, ty: &Ty, out: &mut ThinVec<TyVarId>) {
        match self.resolve(ty) {
            Ty::Var(var) => {
                if !out.contains(&var) {
                    out.push(var);
                }
            }
            Ty::Ptr(inner, _) | Ty::Slice(inner) | Ty::Array(inner, _) => {
                self.vars_in(&inner, out);
            }
            Ty::Fn { params, ret } => {
                for param in &params {
                    self.vars_in(param, out);
                }
                self.vars_in(&ret, out);
            }
            Ty::Tuple(elements) => {
                for element in &elements {
                    self.vars_in(element, out);
                }
            }
            Ty::Adt(_, generics) => {
                if let Some(generics) = generics {
                    for ty in generics {
                        self.vars_in(&ty, out);
                    }
                }
            }
            Ty::Alias { generic_args, .. } => {
                if let Some(generics) = generic_args {
                    for ty in generics {
                        self.vars_in(&ty, out);
                    }
                }
            }
            Ty::Projection {
                self_ty,
                generic_args,
                ..
            } => {
                self.vars_in(&self_ty, out);
                if let Some(generic_args) = generic_args {
                    for ty in generic_args {
                        self.vars_in(&ty, out);
                    }
                }
            }
            Ty::Prim(_) | Ty::Never | Ty::MethodCallee | Ty::Error => {}
        }
    }

    pub fn generalize(&self, ty: &Ty, scope: u32) -> ThinVec<TyVarId> {
        let mut all = ThinVec::new();
        self.vars_in(ty, &mut all);

        let mut seen = FxHashSet::default();
        all.into_iter()
            .filter(|&ty_var| self.ty_var(ty_var).level > scope && seen.insert(ty_var))
            .collect()
    }

    pub fn instantiate(&mut self, scheme: &Scheme) -> Ty {
        let mut mapping: FxHashMap<TyVarId, TyVarId> = FxHashMap::default();
        for &v in &scheme.vars {
            mapping.insert(v, self.next_ty_var());
        }
        self.instantiate_with(&scheme.body, &mapping)
    }

    pub fn instantiate_with(&self, ty: &Ty, mapping: &FxHashMap<TyVarId, TyVarId>) -> Ty {
        fold_ty(ty, &mut |ty| match ty {
            Ty::Var(v) => mapping
                .get(&v)
                .map(|&fresh| Ty::Var(fresh))
                .unwrap_or(Ty::Var(v)),
            ty => ty,
        })
    }

    pub fn snapshot(&self) -> Snapshot {
        let roots: FxHashMap<TyVarId, Option<Ty>> = self
            .vars
            .iter()
            .enumerate()
            .map(|(i, var)| (TyVarId(i as u32), var.root.clone()))
            .collect();
        let levels: FxHashMap<TyVarId, u32> = self
            .vars
            .iter()
            .enumerate()
            .map(|(i, var)| (TyVarId(i as u32), var.level))
            .collect();
        Snapshot {
            vars_len: self.vars.len(),
            errors_len: self.errors.len(),
            roots,
            levels,
        }
    }

    pub fn rollback(&mut self, snapshot: Snapshot) {
        for (id, root) in snapshot.roots {
            if let Some(var) = self.vars.get_mut(id.0 as usize) {
                var.root = root;
            }
        }
        for (id, level) in snapshot.levels {
            if let Some(var) = self.vars.get_mut(id.0 as usize) {
                var.level = level;
            }
        }
        self.vars.truncate(snapshot.vars_len);
        self.errors.truncate(snapshot.errors_len);
    }

    pub fn add_generic_default(&mut self, var: TyVarId, default: Ty) {
        self.generic_defaults.push((var, default));
    }

    pub fn vars_with_source(&self, source: TyVarSource) -> Vec<TyVarId> {
        self.vars
            .iter()
            .enumerate()
            .filter_map(|(i, var)| {
                if var.source == source {
                    Some(TyVarId(i as u32))
                } else {
                    None
                }
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_var_unbound() {
        let mut icx = InferCtx::default();
        icx.push_level();
        let v = icx.next_ty_var();
        assert!(!icx.ty_var(v).root.is_some());
    }

    #[test]
    fn fresh_vars_have_unique_ids() {
        let mut icx = InferCtx::default();
        icx.push_level();
        let a = icx.next_ty_var();
        let b = icx.next_ty_var();
        assert_ne!(a, b);
    }

    #[test]
    fn level_stack_push_pop() {
        let mut icx = InferCtx::default();
        icx.push_level();
        let l1 = icx.current_level();
        icx.push_level();
        let l2 = icx.current_level();
        assert!(l2 > l1);
        icx.pop_level();
        assert_eq!(icx.current_level(), l1);
    }

    #[test]
    fn generalize_collects_vars_above_scope() {
        let mut icx = InferCtx::default();
        icx.push_level();
        // Outer level
        icx.next_ty_var();
        // Inner scope
        icx.push_level();
        let b = icx.next_ty_var();
        let ty = Ty::Fn {
            params: ThinVec::new(),
            ret: Box::new(Ty::Var(b)),
        };
        let outer = 0;
        let scheme_vars = icx.generalize(&ty, outer);
        // b is at level 1, outer scope is level 0 -> generalised
        assert_eq!(scheme_vars.len(), 1);
        assert_eq!(scheme_vars[0], b);
    }

    #[test]
    fn instantiate_creates_fresh_vars() {
        let mut icx = InferCtx::default();
        icx.push_level();
        let v = icx.next_ty_var();
        let scheme = Scheme {
            vars: thin_vec::thin_vec![v],
            body: Ty::Var(v),
        };
        let ty = icx.instantiate(&scheme);
        match ty {
            Ty::Var(new) => assert_ne!(new, v),
            _ => panic!("expected Var"),
        }
    }

    #[test]
    fn resolve_chases_unbound_chain() {
        // No unify yet, so resolve on a fresh var returns Var.
        let mut icx = InferCtx::default();
        icx.push_level();
        let v = icx.next_ty_var();
        let ty = Ty::Var(v);
        let r = icx.resolve(&ty);
        assert!(matches!(r, Ty::Var(_)));
    }
}
