use crate::hir::types::{Body, Node, OwnerNode};
use crate::hir::{BodyId, DefId, ItemLocalId, OwnerId};
use fxhash::FxHashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HirId {
    pub owner: OwnerId,
    pub local_id: ItemLocalId,
}

impl HirId {
    pub const INVALID: HirId = HirId {
        owner: OwnerId::INVALID,
        local_id: ItemLocalId::INVALID,
    };

    pub fn make_owner(owner: DefId) -> Self {
        HirId {
            owner: OwnerId(owner.0),
            local_id: ItemLocalId::ZERO,
        }
    }

    pub fn is_owner(self) -> bool {
        self.local_id.0 == 0
    }

    pub fn as_owner(self) -> Option<OwnerId> {
        if self.is_owner() {
            Some(self.owner)
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct OwnerInfo {
    pub nodes: OwnerNodes,
}

/// The HIR tree for a single owner.
/// `nodes[0]` is the owner node.
#[derive(Debug)]
pub struct OwnerNodes {
    pub nodes: Vec<ParentedNode>,
    pub bodies: FxHashMap<BodyId, Body>,
}

impl OwnerNodes {
    pub fn node(&self) -> OwnerNode<'_> {
        OwnerNode::from_node(&self.nodes[0].node).expect("node 0 must be an owner node")
    }

    pub fn body(&self, id: BodyId) -> Option<&Body> {
        self.bodies.get(&id)
    }

    pub fn body_mut(&mut self, id: BodyId) -> Option<&mut Body> {
        self.bodies.get_mut(&id)
    }
}

#[derive(Debug)]
pub struct ParentedNode {
    pub parent: ItemLocalId,
    pub node: Node,
}

/// Represents whether a given DefId has a full HIR owner or just a reference.
#[derive(Debug)]
pub enum MaybeOwner {
    /// This DefId has full HIR information.
    Owner(Box<OwnerInfo>),
    /// This DefId is from another crate or hasn't been lowered yet.
    NonOwner(HirId),
    Placeholder,
}

impl MaybeOwner {
    pub fn as_owner(&self) -> Option<&OwnerInfo> {
        match self {
            MaybeOwner::Owner(info) => Some(info),
            MaybeOwner::NonOwner(_) | MaybeOwner::Placeholder => None,
        }
    }

    pub fn as_owner_mut(&mut self) -> Option<&mut OwnerInfo> {
        match self {
            MaybeOwner::Owner(info) => Some(info),
            MaybeOwner::NonOwner(_) | MaybeOwner::Placeholder => None,
        }
    }
}

#[derive(Debug, Default)]
pub struct Crate {
    pub owners: Vec<MaybeOwner>,
}

impl Crate {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_capacity(cap: usize) -> Self {
        Crate {
            owners: Vec::with_capacity(cap),
        }
    }

    pub fn ensure_owner(&mut self, def_id: DefId) {
        let idx = def_id.0 as usize;
        if idx >= self.owners.len() {
            self.owners.resize_with(idx + 1, || MaybeOwner::Placeholder);
        }
    }

    pub fn owner(&self, def_id: DefId) -> Option<&MaybeOwner> {
        self.owners.get(def_id.0 as usize)
    }

    pub fn owner_mut(&mut self, def_id: DefId) -> Option<&mut MaybeOwner> {
        self.owners.get_mut(def_id.0 as usize)
    }
}
