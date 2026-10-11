#[cfg(test)]
mod tests;

mod builder;

use crate::hir::{DefId, HirId, ItemLocalId};
use fxhash::FxHashMap;

pub use builder::build_scope_trees;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Scope {
    local_id: ItemLocalId,
    kind: ScopeKind,
}

impl Scope {
    pub fn new(local_id: ItemLocalId, kind: ScopeKind) -> Self {
        Self { local_id, kind }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ScopeKind {
    Node,
    /// Params must outlive body
    CallSite,
    Parameters,
    Destruction,
    /// Scope between let declaration and end of scope
    Remainder {
        index: u32,
    },
    IfThen,
    LoopBody,
}

#[derive(Debug, Clone, Default)]
pub struct ScopeTrees {
    per_body: FxHashMap<DefId, ScopeTree>,
}

impl ScopeTrees {
    pub fn per_body(&self, def_id: DefId) -> Option<&ScopeTree> {
        self.per_body.get(&def_id)
    }
}

#[derive(Debug, Clone, Default)]
pub struct ScopeTree {
    /// Hir of the body this covers
    pub root: Option<HirId>,
    /// maps (child scope) -> (parent scope)
    parent_map: FxHashMap<Scope, Scope>,
    /// maps (let local id) -> (declared scope)
    var_map: FxHashMap<ItemLocalId, Scope>,
    extended_temp_scopes: FxHashMap<ItemLocalId, Option<Scope>>,
}

impl ScopeTree {
    pub fn record_parent(&mut self, child: Scope, parent: Scope) {
        self.parent_map.insert(child, parent);
    }

    pub fn record_var_scope(&mut self, var: ItemLocalId, scope: Scope) {
        self.var_map.insert(var, scope);
    }

    pub fn record_extended_temp_scope(&mut self, var: ItemLocalId, scope: Option<Scope>) {
        self.extended_temp_scopes.insert(var, scope);
    }

    pub fn encl_scope(&self, s: Scope) -> Option<Scope> {
        self.parent_map.get(&s).copied()
    }

    pub fn var_scope(&self, var_id: ItemLocalId) -> Option<Scope> {
        self.var_map.get(&var_id).copied()
    }

    pub fn is_subscope_of(&self, subscope: Scope, superscope: Scope) -> bool {
        let mut s = subscope;
        while superscope != s {
            match self.encl_scope(s) {
                Some(scope) => s = scope,
                None => return false,
            }
        }

        true
    }
}
