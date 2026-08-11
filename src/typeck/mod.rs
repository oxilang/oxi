mod env;
mod fold;
mod infctx;
mod passes;
mod types;
mod unify;
mod visitor;

pub(super) use infctx::TyVarId;
pub use types::*;
pub use visitor::*;

use fxhash::{FxHashMap, FxHashSet};
use oxic_diag::include_diagnostics;
use thin_vec::ThinVec;

use crate::ast::Mutability;
use crate::context::Ctx;
use crate::hir::{
    self, AssocItemKind, Crate, DefId, HirId, ItemKind, MaybeOwner, ModuleId, OwnerNode, Path,
};
use crate::interner::Symbol;
use crate::resolve::ResolverOutputs;

use infctx::InferCtx;

include_diagnostics!("diagnostics.toml");

pub fn typeck_crate(
    ctx: &mut Ctx,
    hir_crate: &mut Crate,
    resolver: &ResolverOutputs,
) -> TypeckOutputs {
    let mut typeck = Typeck::new(ctx, hir_crate, resolver);
    typeck.run();
    typeck.into_outputs()
}

#[derive(Debug, Clone)]
pub enum Adjustment {
    AutoRef(Mutability),
    AutoDeref,
}

/// Option<T> that is always expected to be Some
struct Maybe<T> {
    value: Option<T>,
}

impl<T> Maybe<T> {
    pub fn new(value: T) -> Self {
        Maybe { value: Some(value) }
    }

    pub fn replace(&mut self, value: T) {
        assert!(self.value.is_none());
        self.value = Some(value);
    }

    pub fn take(&mut self) -> T {
        self.value.take().expect("value is Some")
    }

    pub fn get(&self) -> &T {
        self.value.as_ref().expect("value is Some")
    }

    pub fn get_mut(&mut self) -> &mut T {
        self.value.as_mut().expect("value is Some")
    }
}

struct Typeck<'ctx, 'hir, 'res> {
    ctx: &'ctx mut Ctx,
    krate: Maybe<&'hir mut Crate>,
    resolver: &'res ResolverOutputs,

    icx: InferCtx,
    /// maps (typed node hir id) -> (ty)
    node_types: FxHashMap<HirId, Ty>,
    /// maps (member access expr hir id) -> (res chosen)
    member_res: FxHashMap<HirId, MemberRes>,
    /// tables describing structs, traits, impls, and their methods
    coherence: CoherenceTable,
    /// maps (item def id) -> (scheme)
    item_schemes: FxHashMap<DefId, Scheme>,
    /// maps (expr hir id) -> (adjustments)
    adjustments: FxHashMap<HirId, Vec<Adjustment>>,
    /// the current `Self` type being typechecked, if any
    current_self_ty: Option<Ty>,
    /// def ids whose generic defaults are currently being resolved, to guard
    /// against recursive associated-type default resolution
    /// e.g. `struct Foo<T = Foo::Bar> { type Bar = T; }`
    default_resolution_in_progress: FxHashSet<DefId>,
}

impl<'ctx, 'hir, 'res> Typeck<'ctx, 'hir, 'res> {
    fn new(ctx: &'ctx mut Ctx, krate: &'hir mut Crate, resolver: &'res ResolverOutputs) -> Self {
        let mut icx = InferCtx::default();
        icx.push_level();

        Self {
            ctx,
            krate: Maybe::new(krate),
            resolver,
            icx,
            node_types: FxHashMap::default(),
            member_res: FxHashMap::default(),
            coherence: CoherenceTable::default(),
            item_schemes: FxHashMap::default(),
            adjustments: FxHashMap::default(),
            current_self_ty: None,
            default_resolution_in_progress: FxHashSet::default(),
        }
    }

    fn run(&mut self) {
        self.build_generic_params();
        self.collect_signatures();
        self.check_type_aliases();
        if self.ctx.errors.has_errors() {
            return;
        }
        self.check_coherence();
        self.build_method_tables();
        self.check_bodies();
        self.rewrite_member_access();
    }

    fn into_outputs(self) -> TypeckOutputs {
        TypeckOutputs {
            node_types: self.node_types,
            member_res: self.member_res,
            coherence: self.coherence,
            item_schemes: self.item_schemes,
            adjustments: self.adjustments,
            hir_id_to_ty_var: self.icx.hir_id_to_ty_var,
        }
    }

    fn owner_module(&self, def_id: DefId) -> ModuleId {
        self.resolver
            .def_to_module
            .get(&def_id)
            .copied()
            .unwrap_or_default()
    }

    fn build_generic_params(&mut self) {
        for (i, owner) in self.krate.get().owners.iter().enumerate() {
            let Some(info) = owner.as_owner() else {
                continue;
            };
            let params = match info.nodes.node() {
                OwnerNode::Item(item) => match &item.kind {
                    ItemKind::Fn(fun) => &fun.generic_params,
                    ItemKind::Struct { generic_params, .. }
                    | ItemKind::TypeAlias { generic_params, .. }
                    | ItemKind::Trait { generic_params, .. } => generic_params,
                    ItemKind::Impl { .. } => &None,
                    _ => continue,
                },
                OwnerNode::AssocItem(assoc) => match &assoc.kind {
                    AssocItemKind::Fn(fun) => &fun.generic_params,
                    _ => continue,
                },
                OwnerNode::Crate => continue,
            };
            let generic_params = params
                .as_ref()
                .map(|params| GenericParamInfo {
                    hir_ids: params.iter().map(|param| param.hir_id).collect(),
                    defaults: params.iter().map(|param| param.default.clone()).collect(),
                })
                .unwrap_or_default();
            self.coherence
                .generic_params
                .insert(DefId(i as u32), generic_params);
        }
    }

    fn iter_owners(&mut self, f: &mut impl FnMut(&mut Typeck, DefId, ModuleId, &MaybeOwner)) {
        let krate = self.krate.take();
        krate.owners.iter().enumerate().for_each(|(i, owner)| {
            let def_id = DefId(i as u32);
            let module_id = self.owner_module(def_id);
            f(self, def_id, module_id, owner)
        });
        self.krate.replace(krate);
    }

    fn with_owners(&mut self, f: impl FnOnce(&mut Typeck, Vec<MaybeOwner>) -> Vec<MaybeOwner>) {
        let krate = self.krate.take();
        let owners = std::mem::take(&mut krate.owners);
        let owners = f(self, owners);
        krate.owners = owners;
        self.krate.replace(krate);
    }
}

#[derive(Debug)]
pub struct TypeckOutputs {
    /// maps (typed node hir id) -> (ty)
    pub node_types: FxHashMap<HirId, Ty>,
    /// maps (member access expr hir id) -> (res chosen)
    pub member_res: FxHashMap<HirId, MemberRes>,
    pub coherence: CoherenceTable,
    /// maps (item def id) -> (scheme)
    pub item_schemes: FxHashMap<DefId, Scheme>,
    /// maps (expr hir id) -> (adjustments)
    pub adjustments: FxHashMap<HirId, Vec<Adjustment>>,
    /// maps (generic param hir id) -> (type variable id)
    pub hir_id_to_ty_var: FxHashMap<HirId, TyVarId>,
}

impl TypeckOutputs {
    /// Assert there are no errors, if errors were correctly reported this won't be reached
    pub fn assert_no_errors(&self) {
        for ty in self.node_types.values() {
            assert!(!matches!(ty, Ty::Error));
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum MemberRes {
    Field { index: usize },
    Method { def_id: DefId, kind: MethodKind },
}

#[derive(Debug, Clone, Copy)]
pub enum MethodKind {
    Inherent,
    Trait { trait_: DefId, impl_def: DefId },
}

/// maps (trait def id, assoc type name) -> resolved type
pub type AssocTypesMap = FxHashMap<(DefId, Symbol), Ty>;

#[derive(Debug, Default)]
pub struct CoherenceTable {
    /// maps (trait def id, struct def id) -> [impl def id]
    pub impls: FxHashMap<(DefId, DefId), Vec<DefId>>,
    /// maps (impl def id) -> (trait def id)
    pub impl_to_trait: FxHashMap<DefId, DefId>,
    /// maps (trait def id) -> (maps (method name) -> (method def id))
    pub trait_methods: FxHashMap<DefId, FxHashMap<Symbol, DefId>>,
    /// maps (method def id) -> (owning trait def id)
    pub method_to_trait: FxHashMap<DefId, DefId>,
    /// maps (struct def id) -> (maps (field name) -> (HIR type, index))
    pub struct_fields: FxHashMap<DefId, FxHashMap<Symbol, (hir::Ty, usize)>>,
    /// maps (def id) -> (generic param info)
    pub generic_params: FxHashMap<DefId, GenericParamInfo>,
    /// maps (impl def id) -> resolved trait generic args
    pub impl_resolved_generic_args: FxHashMap<DefId, Option<ThinVec<Ty>>>,
    /// maps (assoc item def id) -> (parent struct/trait def id)
    pub assoc_to_parent: FxHashMap<DefId, DefId>,
    /// maps (parent def id) -> (assoc item def ids)
    pub parent_to_assoc: FxHashMap<DefId, Vec<DefId>>,
    /// maps (parent def id, assoc type name) -> (assoc type def id)
    pub assoc_type_index: FxHashMap<(DefId, Symbol), DefId>,
    /// maps (struct def id) -> implemented trait def ids
    pub struct_to_traits: FxHashMap<DefId, Vec<DefId>>,
    /// maps (struct def id) -> (maps (method name) -> (method def id))
    pub inherent_methods: FxHashMap<DefId, FxHashMap<Symbol, DefId>>,
    /// maps (struct def id) -> (maps (method name) -> [(trait def id, method def id)])
    pub struct_trait_methods: FxHashMap<DefId, FxHashMap<Symbol, Vec<(DefId, DefId)>>>,
    /// maps (struct/trait/impl def id) -> (declared self type)
    pub impl_self_types: FxHashMap<DefId, Ty>,
    /// maps (impl def id) -> (self type HIR path)
    pub impl_self_ty_hir: FxHashMap<DefId, Path>,
    /// maps (impl def id) -> ((trait def id, assoc type name) -> resolved type)
    pub assoc_types_cache: FxHashMap<DefId, AssocTypesMap>,
}

#[derive(Debug, Clone, Default)]
pub struct GenericParamInfo {
    pub hir_ids: Vec<HirId>,
    pub defaults: ThinVec<Option<hir::Ty>>,
}

impl CoherenceTable {
    pub fn has_conflicting_impl(
        &self,
        existing: &[DefId],
        new_args: &Option<ThinVec<Ty>>,
        new_self_ty: &Ty,
    ) -> bool {
        existing.iter().any(|&existing_def_id| {
            self.impl_resolved_generic_args
                .get(&existing_def_id)
                .is_some_and(|existing_args| existing_args == new_args)
                && self
                    .impl_self_types
                    .get(&existing_def_id)
                    .is_some_and(|existing_self_ty| existing_self_ty == new_self_ty)
        })
    }

    pub fn impls_matching_self(&self, impl_def_ids: &[DefId], target_self_ty: &Ty) -> Vec<DefId> {
        let mut matching: Vec<DefId> = Vec::new();
        for &def_id in impl_def_ids {
            if self.impl_self_types.get(&def_id) != Some(target_self_ty) {
                continue;
            }
            let args = self.impl_resolved_generic_args.get(&def_id).cloned();
            let already = matching
                .iter()
                .any(|&seen| self.impl_resolved_generic_args.get(&seen).cloned() == args);
            if !already {
                matching.push(def_id);
            }
        }
        matching
    }

    pub(super) fn register_trait(&mut self, trait_: DefId, methods: Vec<(Symbol, DefId)>) {
        // or_default() will always be called
        let entry = self.trait_methods.entry(trait_).or_default();
        for (name, method) in methods {
            entry.insert(name, method);
            self.method_to_trait.insert(method, trait_);
        }
    }
}
