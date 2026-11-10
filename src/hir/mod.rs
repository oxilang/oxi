mod def;
mod index;
mod lower;
mod owner;
mod types;

use std::ffi::OsString;
use std::path;

use oxic_diag::include_diagnostics;
use thin_vec::ThinVec;

use crate::ast::{Ast, NodeId, NodeMap};
use crate::context::Ctx;
use crate::interner::{Symbol, sym};
use crate::resolve::{ModuleTree, ResolverOutputs};
use fxhash::FxHashMap;

pub use def::*;
pub use owner::{Crate, HirId, MaybeOwner, OwnerInfo};
pub use types::*;

include_diagnostics!("diagnostics.toml");

crate::newtype_ids!(ModuleId, DefId, OwnerId, ItemLocalId);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BodyId(pub ItemLocalId);

impl std::fmt::Display for BodyId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl OwnerId {
    pub const INVALID: OwnerId = OwnerId(u32::MAX);

    pub fn to_def_id(self) -> DefId {
        DefId(self.0)
    }
}

impl ItemLocalId {
    pub const ZERO: ItemLocalId = ItemLocalId(0);
    pub const INVALID: ItemLocalId = ItemLocalId(u32::MAX);

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloatTy {
    F16,
    F32,
    F64,
    F128,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimTy {
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    Bool,
    Unit,
}

impl PrimTy {
    pub fn from_name(s: Symbol) -> Option<Self> {
        Some(match s {
            sym::i8 => Self::Int(IntTy::I8),
            sym::i16 => Self::Int(IntTy::I16),
            sym::i32 => Self::Int(IntTy::I32),
            sym::i64 => Self::Int(IntTy::I64),
            sym::i128 => Self::Int(IntTy::I128),
            sym::isize => Self::Int(IntTy::Isize),
            sym::u8 => Self::Uint(UintTy::U8),
            sym::u16 => Self::Uint(UintTy::U16),
            sym::u32 => Self::Uint(UintTy::U32),
            sym::u64 => Self::Uint(UintTy::U64),
            sym::u128 => Self::Uint(UintTy::U128),
            sym::usize => Self::Uint(UintTy::Usize),
            sym::f16 => Self::Float(FloatTy::F16),
            sym::f32 => Self::Float(FloatTy::F32),
            sym::f64 => Self::Float(FloatTy::F64),
            sym::f128 => Self::Float(FloatTy::F128),
            sym::bool => Self::Bool,
            sym::void => Self::Unit,
            _ => return None,
        })
    }

    pub fn name(self) -> Symbol {
        match self {
            PrimTy::Int(IntTy::I8) => sym::i8,
            PrimTy::Int(IntTy::I16) => sym::i16,
            PrimTy::Int(IntTy::I32) => sym::i32,
            PrimTy::Int(IntTy::I64) => sym::i64,
            PrimTy::Int(IntTy::I128) => sym::i128,
            PrimTy::Int(IntTy::Isize) => sym::isize,
            PrimTy::Uint(UintTy::U8) => sym::u8,
            PrimTy::Uint(UintTy::U16) => sym::u16,
            PrimTy::Uint(UintTy::U32) => sym::u32,
            PrimTy::Uint(UintTy::U64) => sym::u64,
            PrimTy::Uint(UintTy::U128) => sym::u128,
            PrimTy::Uint(UintTy::Usize) => sym::usize,
            PrimTy::Float(FloatTy::F16) => sym::f16,
            PrimTy::Float(FloatTy::F32) => sym::f32,
            PrimTy::Float(FloatTy::F64) => sym::f64,
            PrimTy::Float(FloatTy::F128) => sym::f128,
            PrimTy::Bool => sym::bool,
            PrimTy::Unit => sym::void,
        }
    }

    pub fn name_str(self) -> &'static str {
        match self {
            PrimTy::Int(IntTy::I8) => "i8",
            PrimTy::Int(IntTy::I16) => "i16",
            PrimTy::Int(IntTy::I32) => "i32",
            PrimTy::Int(IntTy::I64) => "i64",
            PrimTy::Int(IntTy::I128) => "i128",
            PrimTy::Int(IntTy::Isize) => "isize",
            PrimTy::Uint(UintTy::U8) => "u8",
            PrimTy::Uint(UintTy::U16) => "u16",
            PrimTy::Uint(UintTy::U32) => "u32",
            PrimTy::Uint(UintTy::U64) => "u64",
            PrimTy::Uint(UintTy::U128) => "u128",
            PrimTy::Uint(UintTy::Usize) => "usize",
            PrimTy::Float(FloatTy::F16) => "f16",
            PrimTy::Float(FloatTy::F32) => "f32",
            PrimTy::Float(FloatTy::F64) => "f64",
            PrimTy::Float(FloatTy::F128) => "f128",
            PrimTy::Bool => "bool",
            PrimTy::Unit => "void",
        }
    }
}

#[derive(Debug)]
pub struct AstLoweringContext<'a, 'ctx> {
    ctx: &'ctx mut Ctx,
    asts: &'a ThinVec<Ast>,
    module_tree: &'a ModuleTree,
    resolver: &'a ResolverOutputs,

    current_owner: Option<OwnerId>,
    next_local_id: u32,
    /// maps (node id) -> (hir id)
    node_to_hir_id: NodeMap<HirId>,
    /// maps (def id) -> (module id)
    def_to_module: FxHashMap<DefId, ModuleId>,
}

impl<'a, 'ctx> AstLoweringContext<'a, 'ctx> {
    pub fn new(
        ctx: &'ctx mut Ctx,
        asts: &'a ThinVec<Ast>,
        module_tree: &'a ModuleTree,
        resolver: &'a ResolverOutputs,
    ) -> Self {
        let mut def_to_module = FxHashMap::default();
        for (i, module) in resolver.modules.iter().enumerate() {
            for res in module.resolutions.values() {
                def_to_module.insert(res.best_binding().def_id, ModuleId(i as u32));
            }
            for methods in module.struct_methods.values() {
                for binding in methods.values() {
                    def_to_module.insert(binding.def_id, ModuleId(i as u32));
                }
            }
            for &impl_def_id in &module.impls {
                def_to_module.insert(impl_def_id, ModuleId(i as u32));
            }
            for &method_def_id in &module.methods {
                def_to_module.insert(method_def_id, ModuleId(i as u32));
            }
        }
        Self {
            ctx,
            asts,
            module_tree,
            resolver,
            current_owner: None,
            next_local_id: 0,
            node_to_hir_id: NodeMap::default(),
            def_to_module,
        }
    }

    pub fn lower_crate(&mut self) -> Crate {
        let index = index::index_crate(
            self.asts,
            self.module_tree,
            &self.resolver.def_map,
            self.resolver.defs.len(),
        );

        let mut hir_crate = Crate::with_capacity(self.resolver.defs.len());

        for def_id in index.indices() {
            self.lower_node(def_id, &index, &mut hir_crate);
        }

        hir_crate
    }

    fn next_local_id(&mut self) -> ItemLocalId {
        let id = ItemLocalId(self.next_local_id);
        self.next_local_id += 1;
        id
    }

    fn next_hir_id(&mut self) -> HirId {
        let owner = self.current_owner.expect("current owner set");
        HirId {
            owner,
            local_id: self.next_local_id(),
        }
    }

    /// Register a local binding's HirId for the given AST NodeId
    pub(super) fn register_local(&mut self, node_id: NodeId, hir_id: HirId) {
        self.node_to_hir_id.insert(node_id, hir_id);
    }

    /// Look up the HirId for a local binding by its AST NodeId
    pub(super) fn lookup_local(&self, node_id: NodeId) -> Option<HirId> {
        self.node_to_hir_id.get(&node_id).copied()
    }
}

/// Convert a path like `a/b.oxi` into `a::b`.
pub fn path_to_mod<P: AsRef<path::Path>>(p: P) -> String {
    let path = p.as_ref();

    let mut normals: Vec<OsString> = path
        .components()
        .filter_map(|c| match c {
            path::Component::Normal(os) => Some(os.to_os_string()),
            _ => None,
        })
        .collect();

    if normals.is_empty() {
        return String::new();
    }

    let last = normals.pop().expect("normals isn't empty");
    let last_stem = path::Path::new(&last)
        .file_stem()
        .map(|s| s.to_string_lossy().into_owned())
        .unwrap_or_default();

    let mut parts: Vec<String> = normals
        .into_iter()
        .map(|os| os.to_string_lossy().into_owned())
        .collect();

    if !last_stem.is_empty() {
        parts.push(last_stem);
    }

    parts.join("::")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple() {
        assert_eq!(path_to_mod("a/b.oxi"), "a::b");
        assert_eq!(path_to_mod("a/b.test.oxi"), "a::b.test");
        assert_eq!(path_to_mod("single.oxi"), "single");
        assert_eq!(path_to_mod("single"), "single");
        assert_eq!(path_to_mod("/usr/local/pkg.oxi"), "usr::local::pkg");
    }
}
