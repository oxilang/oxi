use fxhash::FxHashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeId(pub u32);

impl NodeId {
    pub const DEFAULT: NodeId = NodeId(u32::MAX);
}

impl Default for NodeId {
    #[inline]
    fn default() -> Self {
        Self(u32::MAX)
    }
}

pub type NodeMap<T> = FxHashMap<NodeId, T>;
