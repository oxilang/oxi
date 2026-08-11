mod early;
mod late;
mod path;
mod prepass;

mod mod_tree;
pub use mod_tree::{ModuleTree, build_module_tree};

use std::ops::{Index, IndexMut};

use oxic_diag::include_diagnostics;
use thin_vec::{ThinVec, thin_vec};

use crate::ast::{Ast, ImportTree, NodeId, NodeMap, Visibility};
use crate::context::Ctx;
use crate::hir::{Def, DefId, DefKind, ModuleId, PrimTy};
use crate::interner::Symbol;
use fxhash::FxHashMap;

include_diagnostics!("diagnostics.toml");

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PartialRes {
    base_res: Res,
    unresolved_segments: usize,
}

impl PartialRes {
    pub fn new(base_res: Res) -> Self {
        Self {
            base_res,
            unresolved_segments: 0,
        }
    }

    pub fn with_unresolved_segments(base_res: Res, mut unresolved_segments: usize) -> Self {
        if base_res == Res::Err {
            unresolved_segments = 0;
        }
        Self {
            base_res,
            unresolved_segments,
        }
    }

    pub fn base_res(&self) -> Res {
        self.base_res
    }

    pub fn unresolved_segments(&self) -> usize {
        self.unresolved_segments
    }

    pub fn full_res(&self) -> Option<Res> {
        (self.unresolved_segments == 0).then_some(self.base_res)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Res<Id = NodeId> {
    /// Module-level def
    Def(DefId),
    /// Local definition in function body
    Local(Id),
    /// Generic type parameter
    GenericParam(Id),
    /// Primitive type, like `i32`
    PrimTy(PrimTy),
    /// Self type in struct or impl
    SelfTyAlias { alias_to: DefId },
    /// Error in name resolution
    Err,
}

impl Res {
    fn is_type_ns(&self, resolver: &Resolver) -> bool {
        match self {
            Res::Def(def) => resolver.is_type_def(*def),
            Res::SelfTyAlias { .. } => true,
            Res::GenericParam(_) => true,
            Res::PrimTy(_) => true,
            _ => false,
        }
    }
}

#[derive(Debug)]
pub struct PendingImport {
    pub module: ModuleId,
    pub import_item: ImportTree,
    pub visibility: Visibility,
}

#[derive(Debug)]
pub struct PerModule<T: Clone + Default>(ThinVec<T>);

impl<T: Clone + Default> PerModule<T> {
    pub fn new(len: usize) -> Self {
        Self(thin_vec![Default::default(); len])
    }

    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.0.iter()
    }
}

impl<T: Clone + Default> PerModule<T> {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<T: Clone + Default> Index<usize> for PerModule<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl<T: Clone + Default> IndexMut<usize> for PerModule<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

#[derive(Debug, Clone, Copy)]
pub struct NameBinding {
    pub def_id: DefId,
    pub visibility: Visibility,
}

// Non glob imports can shadow glob imports, so this cannot be an enum
#[derive(Debug, Clone, Copy)]
pub struct NameResolution {
    /// Name coming from a local definition or single import. e.g.
    /// ```ignore
    /// import some_module::SomeStruct;
    /// // or
    /// struct MyStruct {}
    /// ````
    pub non_glob_import: Option<NameBinding>,
    /// Name coming from a glob import. e.g.
    /// ```ignore
    /// import my_module::*;
    /// ````
    pub glob_import: Option<NameBinding>,
}

impl NameResolution {
    pub fn best_binding(&self) -> NameBinding {
        self.non_glob_import
            .or(self.glob_import)
            .expect("If a resolution exists, it must be a non glob import or a glob import")
    }

    pub fn non_glob_import(binding: NameBinding) -> Self {
        Self {
            non_glob_import: Some(binding),
            glob_import: None,
        }
    }

    pub fn glob_import(binding: NameBinding) -> Self {
        Self {
            non_glob_import: None,
            glob_import: Some(binding),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct ModuleData {
    pub resolutions: FxHashMap<Symbol, NameResolution>,
    pub parent: Option<usize>,
    pub children: Vec<usize>,
    pub qualified_name: String,
}

#[derive(Debug)]
pub struct ResolverOutputs {
    /// maps (path node id) -> (partial res)
    pub res_map: NodeMap<PartialRes>,
    /// maps (def node id) -> (def id)
    pub def_map: NodeMap<DefId>,
    /// Arena\[DefId] -> Def
    pub defs: ThinVec<Def>,
    pub modules: PerModule<ModuleData>,
    pub def_to_module: FxHashMap<DefId, ModuleId>,
}

impl ResolverOutputs {
    pub fn def(&self, def_id: DefId) -> &Def {
        &self.defs[def_id.0 as usize]
    }

    pub fn def_mut(&mut self, def_id: DefId) -> &mut Def {
        &mut self.defs[def_id.0 as usize]
    }
}

#[derive(Debug)]
pub struct Resolver<'a, 'ctx> {
    ctx: &'ctx mut Ctx,

    asts: &'a ThinVec<Ast>,
    module_tree: &'a ModuleTree,
    module_idx: usize,

    // Early res
    pending_imports: ThinVec<PendingImport>,
    modules: PerModule<ModuleData>,
    def_map: NodeMap<DefId>,
    /// Arena\[DefId] -> Def
    defs: ThinVec<Def>,
    def_to_module: FxHashMap<DefId, ModuleId>,

    // Late res
    /// maps (path node id) -> (res)
    res_map: NodeMap<PartialRes>,
}

impl<'a, 'ctx> Resolver<'a, 'ctx> {
    pub fn new(asts: &'a ThinVec<Ast>, module_tree: &'a ModuleTree, ctx: &'ctx mut Ctx) -> Self {
        let node_count = module_tree.nodes.len();
        let mut modules: PerModule<ModuleData> = PerModule::new(node_count);

        for (i, node) in module_tree.nodes.iter().enumerate() {
            modules[i].parent = node.parent;
            modules[i].qualified_name = node.qualified_name.clone();
            for &child in &node.children {
                modules[i].children.push(child);
            }
        }

        Self {
            ctx,
            asts,
            module_idx: 0,
            module_tree,
            pending_imports: ThinVec::new(),
            modules,
            def_map: NodeMap::default(),
            defs: ThinVec::new(),
            def_to_module: FxHashMap::default(),
            res_map: NodeMap::default(),
        }
    }

    pub fn resolve(&mut self) {
        self.collect_definitions();
        self.build_graph();
        self.resolve_imports();
        self.late_resolve();
    }

    pub fn into_resolver_outputs(self) -> ResolverOutputs {
        ResolverOutputs {
            res_map: self.res_map,
            def_map: self.def_map,
            defs: self.defs,
            modules: self.modules,
            def_to_module: self.def_to_module,
        }
    }

    fn current_module(&self) -> &ModuleData {
        &self.modules[self.module_idx]
    }

    fn current_module_mut(&mut self) -> &mut ModuleData {
        &mut self.modules[self.module_idx]
    }

    fn def_id_for_node(&self, node_id: NodeId) -> Option<DefId> {
        self.def_map.get(&node_id).copied()
    }

    /// Returns the `ModuleId` of the actual source file backing the current module.
    /// For file-backed modules this is `ModuleId(ast_idx)`. For inline modules
    /// it walks up to the nearest file-backed ancestor.
    fn source_module_id(&self) -> ModuleId {
        let mut idx = self.module_idx;
        loop {
            let node = &self.module_tree.nodes[idx];
            if let Some(ast_idx) = node.ast_idx {
                return ModuleId(ast_idx as u32);
            }
            match node.parent {
                Some(parent) => idx = parent,
                None => unreachable!(),
            }
        }
    }

    fn is_type_def(&self, def_id: DefId) -> bool {
        matches!(
            self.defs.get(def_id.0 as usize).map(|d| d.kind),
            Some(DefKind::Struct | DefKind::Trait | DefKind::TypeAlias | DefKind::AssocType)
        )
    }

    fn register_def_to_module(&mut self, def_id: DefId) {
        self.def_to_module
            .insert(def_id, ModuleId(self.module_idx as u32));
    }
}
