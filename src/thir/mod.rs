mod lower;
pub mod scope;

mod types;
pub use types::*;

use thin_vec::thin_vec;

use crate::hir::{self, AssocItemKind, DefId, ItemKind, MaybeOwner, Node};
use crate::thir::lower::lower_body;
use crate::thir::scope::ScopeTrees;
use crate::typeck::TypeckOutputs;

pub fn lower_thir(
    krate: &hir::Crate,
    typeck: &TypeckOutputs,
    scope_trees: &ScopeTrees,
) -> ThirCrate {
    let mut thir = ThirCrate {
        bodies: Default::default(),
    };

    for (i, owner) in krate.owners.iter().enumerate() {
        let def_id = DefId(i as u32);

        let MaybeOwner::Owner(info) = owner else {
            continue;
        };

        let scope_tree = scope_trees.per_body(def_id);

        match &info.nodes.nodes[0].node {
            Node::Item(item) => match &item.kind {
                ItemKind::Fn(fun) => {
                    if let Some(body_id) = fun.body_id {
                        let body = info.nodes.body(body_id).expect("body exists");
                        let thir_body = lower_body(&fun.decl.params, body, typeck, scope_tree);
                        thir.bodies.insert(def_id, thir_body);
                    }
                }
                ItemKind::Const {
                    body_id: Some(body_id),
                    ..
                } => {
                    let body = info.nodes.body(*body_id).expect("body exists");
                    let thir_body = lower_body(&thin_vec![], body, typeck, scope_tree);
                    thir.bodies.insert(def_id, thir_body);
                }
                _ => {}
            },
            Node::AssocItem(assoc) => {
                let AssocItemKind::Fn(fun) = &assoc.kind else {
                    continue;
                };
                if let Some(body_id) = fun.body_id {
                    let body = info.nodes.body(body_id).expect("body exists");
                    let thir_body = lower_body(&fun.decl.params, body, typeck, scope_tree);
                    thir.bodies.insert(def_id, thir_body);
                }
            }
            _ => {}
        }
    }

    thir
}
