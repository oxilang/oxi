use fxhash::{FxHashMap, FxHashSet};
use thin_vec::ThinVec;

use crate::ast::Mutability;
use crate::diag_params;
use crate::errors::builders;
use crate::hir::{self, DefId, DefKind, ModuleId, Path, PrimTy, QPath, TyKind};
use crate::interner::Symbol;
use crate::resolve::Res;
use crate::span::Span;
use crate::typeck::fold::{fold_ty, resolve_scheme_with_args, substitute_ty_vars};
use crate::typeck::infctx::{InferCtx, TyVarId, TyVarSource};
use crate::typeck::{Typeck, diag};

#[derive(Debug, Clone)]
pub enum TyFromHirError {
    /// The qself path in a projection did not resolve to a trait
    ExpectedPathToTrait {
        span: Span,
        module_id: ModuleId,
        path: Path,
    },
    /// An associated type could not be resolved
    UnresolvedAssocType { span: Span, module_id: ModuleId },
    /// The wrong number of generic arguments were provided to a generic type
    UnexpectedGenericArgs {
        span: Span,
        module_id: ModuleId,
        expected: usize,
        found: usize,
    },
}

pub type TyFromHirResult<T> = Result<T, TyFromHirError>;

enum TraitAssocTypeLookup {
    Found(DefId, DefId),
    Ambiguous,
    NotFound,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Var(TyVarId),
    Prim(PrimTy),
    Ptr(Box<Ty>, Mutability),
    Slice(Box<Ty>),
    Array(Box<Ty>, usize),
    Fn {
        params: ThinVec<Ty>,
        ret: Box<Ty>,
    },
    Tuple(ThinVec<Ty>),
    Adt(DefId, Option<ThinVec<Ty>>),
    Alias {
        def_id: DefId,
        generic_args: Option<ThinVec<Ty>>,
    },
    Projection {
        trait_def_id: DefId,
        assoc_def_id: DefId,
        self_ty: Box<Ty>,
        generic_args: Option<ThinVec<Ty>>,
        trait_generic_args: Option<ThinVec<Ty>>,
    },
    Never,
    /// Dummy type for the synthetic `Path` callee created during THIR lowering
    /// of method calls. This callee `Path` expression is never type-checked, it
    /// unifies with everything. Downstream consumers (IR emission, etc.) resolve
    /// the actual method `DefId` via `TypeckOutputs::member_res`.
    MethodCallee,
    Error,
}

impl<'ctx, 'hir, 'res> Typeck<'ctx, 'hir, 'res> {
    pub fn ty_from_hir(&mut self, hir_ty: &hir::Ty, module_id: ModuleId) -> TyFromHirResult<Ty> {
        match &hir_ty.kind {
            TyKind::Error => Ok(Ty::Error),
            TyKind::Never => Ok(Ty::Never),
            TyKind::Infer => Ok(self.icx.alloc_ty_var()),
            TyKind::PrimTy(prim) => Ok(Ty::Prim(*prim)),
            TyKind::Ptr(inner, m) => {
                Ok(Ty::Ptr(self.ty_from_hir(inner, module_id)?.into_box(), *m))
            }
            TyKind::Slice(inner) => Ok(Ty::Slice(self.ty_from_hir(inner, module_id)?.into_box())),
            TyKind::Array(inner, size) => Ok(Ty::Array(
                self.ty_from_hir(inner, module_id)?.into_box(),
                *size,
            )),
            TyKind::Fn { params, ret } => Ok(Ty::Fn {
                params: params
                    .iter()
                    .map(|hir_ty| self.ty_from_hir(hir_ty, module_id))
                    .collect::<TyFromHirResult<ThinVec<_>>>()?,
                ret: self.ty_from_hir(ret, module_id)?.into_box(),
            }),
            TyKind::Tuple(elements) => Ok(Ty::Tuple(
                elements
                    .iter()
                    .map(|hir_ty| self.ty_from_hir(hir_ty, module_id))
                    .collect::<TyFromHirResult<ThinVec<_>>>()?,
            )),
            TyKind::Path(qpath) => match qpath {
                QPath::Resolved(_, path) => match path.res {
                    Res::Def(def_id) => {
                        let mut generic_args = self.ty_hir_generic_args(path, module_id)?;
                        self.check_generic_arity(def_id, &generic_args, path.span, module_id)?;
                        self.fill_generic_defaults(def_id, &mut generic_args, module_id);
                        match self.resolver.def(def_id).kind {
                            DefKind::TypeAlias => Ok(Ty::Alias {
                                def_id,
                                generic_args,
                            }),
                            DefKind::Struct => Ok(Ty::Adt(def_id, generic_args)),
                            DefKind::AssocType => Err(TyFromHirError::UnresolvedAssocType {
                                span: path.span,
                                module_id,
                            }),
                            _ => Ok(Ty::Error),
                        }
                    }
                    Res::SelfTyAlias { alias_to } => {
                        self.resolve_self_ty(alias_to, true, path, module_id)
                    }
                    Res::PrimTy(prim) => Ok(Ty::Prim(prim)),
                    Res::GenericParam(hir_id) => {
                        let Some(ty_var) = self.icx.hir_id_to_ty_var.get(&hir_id) else {
                            return Ok(Ty::Error);
                        };
                        Ok(Ty::Var(*ty_var))
                    }
                    Res::Local(_) | Res::Err => Ok(Ty::Error),
                },
                QPath::TypeRelative { qself, segment } => {
                    self.resolve_type_relative_projection(qself, segment, module_id)
                }
            },
            TyKind::GenericParam(hir_id, _) => {
                let Some(ty_var) = self.icx.hir_id_to_ty_var.get(hir_id) else {
                    return Ok(Ty::Error);
                };
                Ok(Ty::Var(*ty_var))
            }
        }
    }

    fn check_generic_arity(
        &self,
        def_id: DefId,
        generic_args: &Option<ThinVec<Ty>>,
        span: Span,
        module_id: ModuleId,
    ) -> TyFromHirResult<()> {
        // For `struct A<T, U = i32>`
        // Accept `A::<i32>` and `A::<i32, i32>`
        // Reject `A` and `A::<i32, i32, i32>`
        let Some(info) = self.coherence.generic_params.get(&def_id) else {
            return Ok(());
        };
        let expected = info.hir_ids.len();
        let found = generic_args.as_ref().map(|args| args.len()).unwrap_or(0);
        if found > expected {
            return Err(TyFromHirError::UnexpectedGenericArgs {
                span,
                module_id,
                expected,
                found,
            });
        }
        let required = info
            .defaults
            .iter()
            .position(|d| d.is_some())
            .unwrap_or(expected);
        if found >= required {
            return Ok(());
        }
        Err(TyFromHirError::UnexpectedGenericArgs {
            span,
            module_id,
            expected,
            found,
        })
    }

    fn fill_generic_defaults(
        &mut self,
        def_id: DefId,
        generic_args: &mut Option<ThinVec<Ty>>,
        module_id: ModuleId,
    ) {
        let Some(info) = self.coherence.generic_params.get(&def_id).cloned() else {
            return;
        };
        let Some(args) = generic_args.take() else {
            return;
        };
        let expected = info.hir_ids.len();
        if args.len() >= expected {
            *generic_args = Some(args);
            return;
        }
        let mut args = args;
        let mut subst: FxHashMap<TyVarId, Ty> = FxHashMap::default();
        for (i, arg) in args.iter().enumerate() {
            if let Some(&var) = self.icx.hir_id_to_ty_var.get(&info.hir_ids[i]) {
                subst.insert(var, arg.clone());
            }
        }
        for i in args.len()..expected {
            let Some(default_ty) = info.defaults.get(i).and_then(|d| d.as_ref()) else {
                break;
            };
            let ty = self.resolve_default_generic_arg(default_ty, module_id, &subst, None);
            if let Some(&var) = self.icx.hir_id_to_ty_var.get(&info.hir_ids[i]) {
                subst.insert(var, ty.clone());
            }
            args.push(ty);
        }
        *generic_args = Some(args);
    }

    fn resolve_self_ty(
        &mut self,
        alias_to: DefId,
        is_self_alias: bool,
        path: &hir::Path,
        module_id: ModuleId,
    ) -> TyFromHirResult<Ty> {
        if is_self_alias
            && let Some(Ty::Adt(id, args)) = &self.current_self_ty
            && *id == alias_to
        {
            Ok(Ty::Adt(alias_to, args.clone()))
        } else {
            let mut generic_args = self.ty_hir_generic_args(path, module_id)?;
            self.check_generic_arity(alias_to, &generic_args, path.span, module_id)?;
            self.fill_generic_defaults(alias_to, &mut generic_args, module_id);
            Ok(Ty::Adt(alias_to, generic_args))
        }
    }

    /// Resolve `QPath::TypeRelative` to a `Ty::Projection`
    fn resolve_type_relative_projection(
        &mut self,
        qself: &QPath,
        segment: &hir::PathSegment,
        module_id: ModuleId,
    ) -> TyFromHirResult<Ty> {
        let assoc_name = segment.ident.value;

        let segment_args = segment
            .generic_args
            .as_ref()
            .map(|args| {
                args.iter()
                    .map(|ty| self.ty_from_hir(ty, module_id))
                    .collect::<TyFromHirResult<ThinVec<_>>>()
            })
            .transpose()?;

        let (trait_def_id, assoc_def_id, self_ty, trait_path_args) = match qself {
            // <Struct as Trait>::AssocType: explicit trait ref
            QPath::Resolved(Some(self_ty), path) => {
                let Res::Def(trait_def_id) = path.res else {
                    return Err(TyFromHirError::ExpectedPathToTrait {
                        span: path.span,
                        module_id,
                        path: path.clone(),
                    });
                };
                if self.resolver.def(trait_def_id).kind != DefKind::Trait {
                    return Err(TyFromHirError::ExpectedPathToTrait {
                        span: path.span,
                        module_id,
                        path: path.clone(),
                    });
                }
                let assoc_def_id = match self.find_assoc_type(trait_def_id, assoc_name) {
                    Some(id) => id,
                    None => {
                        return Err(TyFromHirError::UnresolvedAssocType {
                            span: segment.ident.span,
                            module_id,
                        });
                    }
                };
                let mut trait_path_args = self.ty_hir_generic_args(path, module_id)?;
                self.check_generic_arity(trait_def_id, &trait_path_args, path.span, module_id)?;
                self.fill_generic_defaults(trait_def_id, &mut trait_path_args, module_id);
                (
                    trait_def_id,
                    assoc_def_id,
                    self.ty_from_hir(self_ty, module_id)?,
                    trait_path_args,
                )
            }
            // `Struct::AssocType`: struct in impl body context
            QPath::Resolved(None, path) => match path.res {
                Res::Def(def_id) | Res::SelfTyAlias { alias_to: def_id } => {
                    let is_self_alias = matches!(path.res, Res::SelfTyAlias { .. });
                    let self_ty = self.resolve_self_ty(def_id, is_self_alias, path, module_id)?;
                    let generic_args = match &self_ty {
                        Ty::Adt(_, args) => args.clone(),
                        _ => unreachable!("resolve_self_ty always yields Ty::Adt"),
                    };
                    match self.resolver.def(def_id).kind {
                        DefKind::Trait => match self.find_assoc_type(def_id, assoc_name) {
                            Some(assoc_def_id) => (
                                def_id,
                                assoc_def_id,
                                self_ty,
                                self.shorthand_trait_args(def_id, module_id),
                            ),
                            None => {
                                return Err(TyFromHirError::UnresolvedAssocType {
                                    span: segment.ident.span,
                                    module_id,
                                });
                            }
                        },
                        DefKind::Struct => {
                            if let Some(resolved) = self.resolve_inherent_assoc_type(
                                def_id,
                                assoc_name,
                                &generic_args,
                                &segment_args,
                                path.span,
                                module_id,
                            )? {
                                return Ok(resolved);
                            }
                            match self.find_trait_assoc_type_for_struct(def_id, assoc_name) {
                                TraitAssocTypeLookup::Found(trait_id, assoc_id) => (
                                    trait_id,
                                    assoc_id,
                                    self_ty,
                                    self.shorthand_trait_args(trait_id, module_id),
                                ),
                                TraitAssocTypeLookup::Ambiguous
                                | TraitAssocTypeLookup::NotFound => {
                                    return Err(TyFromHirError::UnresolvedAssocType {
                                        span: segment.ident.span,
                                        module_id,
                                    });
                                }
                            }
                        }
                        _ => return Ok(Ty::Error),
                    }
                }
                Res::GenericParam(hir_id) => {
                    if !self.icx.hir_id_to_ty_var.contains_key(&hir_id) {
                        return Ok(Ty::Error);
                    }
                    return Err(TyFromHirError::UnresolvedAssocType {
                        span: segment.ident.span,
                        module_id,
                    });
                }
                _ => return Ok(Ty::Error),
            },
            QPath::TypeRelative { .. } => return Ok(Ty::Error),
        };

        Ok(Ty::Projection {
            trait_def_id,
            assoc_def_id,
            self_ty: Box::new(self_ty),
            generic_args: segment_args,
            trait_generic_args: trait_path_args,
        })
    }

    fn shorthand_trait_args(
        &mut self,
        trait_def_id: DefId,
        module_id: ModuleId,
    ) -> Option<ThinVec<Ty>> {
        let info = self.coherence.generic_params.get(&trait_def_id)?;
        if info.hir_ids.is_empty()
            || info.hir_ids.len() != info.defaults.len()
            || !info.defaults.iter().all(|d| d.is_some())
        {
            return None;
        }
        let mut args = Some(ThinVec::new());
        self.fill_generic_defaults(trait_def_id, &mut args, module_id);
        args
    }

    fn find_trait_assoc_type_for_struct(
        &self,
        struct_def_id: DefId,
        assoc_name: Symbol,
    ) -> TraitAssocTypeLookup {
        let mut found: Option<(DefId, DefId)> = None;
        let mut seen_traits: FxHashSet<DefId> = FxHashSet::default();
        for &trait_id in self
            .coherence
            .struct_to_traits
            .get(&struct_def_id)
            .into_iter()
            .flatten()
        {
            if !seen_traits.insert(trait_id) {
                continue;
            }
            if let Some(&assoc_def_id) =
                self.coherence.assoc_type_index.get(&(trait_id, assoc_name))
            {
                if found.is_some() {
                    return TraitAssocTypeLookup::Ambiguous;
                }
                found = Some((trait_id, assoc_def_id));
            }
        }
        match found {
            Some(found) => TraitAssocTypeLookup::Found(found.0, found.1),
            None => TraitAssocTypeLookup::NotFound,
        }
    }

    fn find_assoc_type(&self, parent: DefId, name: Symbol) -> Option<DefId> {
        self.coherence
            .assoc_type_index
            .get(&(parent, name))
            .copied()
    }

    fn resolve_inherent_assoc_type(
        &mut self,
        def_id: DefId,
        assoc_name: Symbol,
        generic_args: &Option<ThinVec<Ty>>,
        assoc_generic_args: &Option<ThinVec<Ty>>,
        span: Span,
        module_id: ModuleId,
    ) -> TyFromHirResult<Option<Ty>> {
        let Some(assoc_def_id) = self.find_assoc_type(def_id, assoc_name) else {
            return Ok(None);
        };
        let Some(scheme) = self.item_schemes.get(&assoc_def_id) else {
            return Ok(Some(Ty::Error));
        };
        // Associated types have no generic parameters yet, so any generic args on
        // the projection segment (e.g. `Foo::Bar::<u32>`) are invalid
        let assoc_arity = 0;
        if let Some(args) = assoc_generic_args
            && args.len() != assoc_arity
        {
            return Err(TyFromHirError::UnexpectedGenericArgs {
                span,
                module_id,
                expected: assoc_arity,
                found: args.len(),
            });
        }
        if let Some(args) = &generic_args {
            if let Some(resolved) = resolve_scheme_with_args(scheme, generic_args) {
                return Ok(Some(resolved));
            }
            return Err(TyFromHirError::UnexpectedGenericArgs {
                span,
                module_id,
                expected: scheme.vars.len(),
                found: args.len(),
            });
        }
        let scheme_body = scheme.body.clone();
        let scheme_vars = scheme.vars.clone();
        if scheme_vars.is_empty() {
            return Ok(Some(scheme_body));
        }
        if let Some(info) = self.coherence.generic_params.get(&def_id).cloned()
            && info.defaults.iter().all(|d| d.is_some())
        {
            if !self.default_resolution_in_progress.insert(def_id) {
                builders::emit_at(
                    self.ctx,
                    span,
                    module_id,
                    diag::RecursiveType,
                    diag_params! {},
                );
                return Ok(Some(Ty::Error));
            }
            for &hir_id in &info.hir_ids {
                if !self.icx.hir_id_to_ty_var.contains_key(&hir_id) {
                    let var = self.icx.next_ty_var();
                    self.icx.hir_id_to_ty_var.insert(hir_id, var);
                }
            }
            let args: TyFromHirResult<ThinVec<Ty>> = (|| {
                let mut param_args: FxHashMap<TyVarId, Ty> = FxHashMap::default();
                let mut args: ThinVec<Ty> = ThinVec::new();
                for (i, default) in info.defaults.iter().enumerate() {
                    let default = default.as_ref().expect("default exists");
                    let mut ty = self.ty_from_hir(default, module_id)?;
                    if !param_args.is_empty() {
                        ty = substitute_ty_vars(&ty, &param_args);
                    }
                    ty = self.normalize_type_alias(&ty);
                    if let Some(&var) = self.icx.hir_id_to_ty_var.get(&info.hir_ids[i]) {
                        param_args.insert(var, ty.clone());
                    }
                    args.push(ty);
                }
                Ok(args)
            })();
            self.default_resolution_in_progress.remove(&def_id);
            let args = args?;
            if args.len() == scheme_vars.len() {
                let mapping: FxHashMap<TyVarId, Ty> = scheme_vars.into_iter().zip(args).collect();
                return Ok(Some(substitute_ty_vars(&scheme_body, &mapping)));
            }
        }
        Err(TyFromHirError::UnexpectedGenericArgs {
            span,
            module_id,
            expected: scheme_vars.len(),
            found: 0,
        })
    }

    pub(super) fn ty_hir_generic_args(
        &mut self,
        path: &hir::Path,
        module_id: ModuleId,
    ) -> TyFromHirResult<Option<ThinVec<Ty>>> {
        // TODO: Handle generic args in spots other than the last segment.
        // Needed for code like:
        // struct Foo<T> {
        //     type Bar<U> = (T, U);
        //             ^^^ currently not supported
        // }
        // fn foo() void {
        //     let x: Foo::<u8>::Bar::<u16> = (1, 2);
        //                       ^^^^^^^^^^ only this segment gets processed
        //            ^^^^^^^^^ this segment's generic args are ignored
        // }
        path.segments
            .last()
            .expect("path has segments")
            .generic_args
            .as_ref()
            .map(|args| {
                args.iter()
                    .map(|ty| self.ty_from_hir(ty, module_id))
                    .collect::<TyFromHirResult<ThinVec<_>>>()
            })
            .transpose()
    }
}

impl Ty {
    pub fn is_numeric(&self, icx: &InferCtx) -> bool {
        match self {
            Ty::Prim(PrimTy::Int(_) | PrimTy::Uint(_) | PrimTy::Float(_)) => true,
            Ty::Var(id) => match icx.root_of(*id) {
                Some(resolved) => resolved.is_numeric(icx),
                None => matches!(
                    icx.ty_var_source(*id),
                    TyVarSource::IntLit | TyVarSource::FloatLit
                ),
            },
            _ => false,
        }
    }

    pub fn into_box(self) -> Box<Self> {
        Box::new(self)
    }

    pub fn reject_vars(self) -> Self {
        fold_ty(&self, &mut |ty| match ty {
            Ty::Var(_) => Ty::Error,
            ty => ty,
        })
    }

    pub fn is_error(&self) -> bool {
        matches!(self, Ty::Error)
    }
}

#[derive(Debug, Clone)]
pub struct Scheme {
    pub vars: ThinVec<TyVarId>,
    pub body: Ty,
}

impl Scheme {
    #[inline]
    pub fn monomorphic(body: Ty) -> Self {
        Self {
            vars: ThinVec::new(),
            body,
        }
    }
}
