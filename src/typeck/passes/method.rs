use crate::hir::{DefId, DefKind, ItemKind, OwnerNode};
use crate::typeck::Typeck;

impl<'ctx, 'hir, 'res> Typeck<'ctx, 'hir, 'res> {
    pub(crate) fn build_method_tables(&mut self) {
        self.collect_inherent_methods();
        self.collect_trait_methods();
    }

    fn collect_inherent_methods(&mut self) {
        for (i, owner) in self.krate.get().owners.iter().enumerate() {
            let Some(ItemKind::Struct { items, .. }) = owner
                .as_owner()
                .map(|info| info.nodes.node())
                .and_then(|node| match node {
                    OwnerNode::Item(item) => Some(&item.kind),
                    _ => None,
                })
            else {
                continue;
            };
            let def_id = DefId(i as u32);
            let entry = self.coherence.inherent_methods.entry(def_id).or_default();
            for &item in items {
                if self.resolver.def(item).kind != DefKind::AssocFn {
                    continue;
                }
                entry.insert(self.resolver.def(item).name.expect("item has name"), item);
            }
        }
    }

    fn collect_trait_methods(&mut self) {
        for ((trait_def_id, struct_def_id), impl_def_ids) in self.coherence.impls.iter() {
            for &impl_def_id in impl_def_ids {
                let Some(ItemKind::Impl { items, .. }) =
                    self.krate.get().owner(impl_def_id).and_then(|owner| {
                        owner
                            .as_owner()
                            .map(|info| info.nodes.node())
                            .and_then(|node| match node {
                                OwnerNode::Item(item) => Some(&item.kind),
                                _ => None,
                            })
                    })
                else {
                    continue;
                };
                let entry = self
                    .coherence
                    .struct_trait_methods
                    .entry(*struct_def_id)
                    .or_default();
                for &item in items {
                    if self.resolver.def(item).kind != DefKind::AssocFn {
                        continue;
                    }
                    entry
                        .entry(self.resolver.def(item).name.expect("item has name"))
                        .or_default()
                        .push((*trait_def_id, item));
                }
            }
        }
    }
}
