use thin_vec::ThinVec;

use crate::ast::{self, Ident, NodeId, Visibility};
use crate::diag_params;
use crate::errors::builders;
use crate::hir::owner::{HirId, MaybeOwner, OwnerInfo, OwnerNodes, ParentedNode};
use crate::hir::{AstLoweringContext, BodyId, Crate, DefId, ItemLocalId, OwnerId};
use crate::hir::{diag, types::*};
use crate::span::Span;
use fxhash::FxHashMap;

impl<'a, 'ctx> AstLoweringContext<'a, 'ctx> {
    pub(super) fn lower_item(&mut self, def_id: DefId, item: &'a ast::Item, hir_crate: &mut Crate) {
        self.with_owner(def_id, hir_crate, |this, def_id| {
            Some(match &item.kind {
                ast::ItemKind::Const { name, ty, value } => {
                    this.lower_const(def_id, name, ty, value, item.span, item.visibility)
                }
                ast::ItemKind::Struct {
                    name,
                    fields,
                    items,
                    generic_params,
                } => this.lower_struct(
                    def_id,
                    name,
                    fields,
                    items,
                    generic_params.as_ref(),
                    item.span,
                    item.visibility,
                ),
                ast::ItemKind::Type {
                    name,
                    generic_params,
                    type_,
                } => this.lower_type_alias(
                    def_id,
                    name,
                    type_,
                    generic_params.as_ref(),
                    item.span,
                    item.visibility,
                ),
                ast::ItemKind::Fn(f) => this.lower_fn(def_id, f, item.span, item.visibility, None),
                ast::ItemKind::Trait {
                    name,
                    items,
                    generic_params,
                } => this.lower_trait(
                    def_id,
                    name,
                    items,
                    generic_params.as_ref(),
                    item.span,
                    item.visibility,
                ),
                ast::ItemKind::Impl {
                    self_ty,
                    trait_,
                    items,
                } => this.lower_impl(def_id, self_ty, trait_, items, item.span, item.visibility),
                ast::ItemKind::Import(_) | ast::ItemKind::Module { .. } => return None,
            })
        })
    }

    pub(super) fn lower_assoc_item(
        &mut self,
        def_id: DefId,
        item: &'a ast::AssocItem,
        hir_crate: &mut Crate,
    ) {
        self.with_owner(def_id, hir_crate, |this, def_id| {
            Some(match &item.kind {
                ast::AssocItemKind::Fn(f) => {
                    this.lower_fn(def_id, f, item.span, item.visibility, Some(def_id))
                }
                ast::AssocItemKind::Type { name, type_ } => {
                    let hir_id = HirId::make_owner(def_id);
                    let owner_id = OwnerId(def_id.0);
                    let type_ = type_.as_ref().map(|t| this.lower_type(t));
                    OwnerInfo {
                        nodes: OwnerNodes {
                            nodes: vec![ParentedNode {
                                parent: ItemLocalId::ZERO,
                                node: Node::AssocItem(Box::new(AssocItem {
                                    hir_id,
                                    owner_id,
                                    kind: AssocItemKind::Type {
                                        name: name.value,
                                        type_,
                                    },
                                    span: item.span,
                                })),
                            }],
                            bodies: FxHashMap::default(),
                        },
                    }
                }
            })
        })
    }

    fn lower_impl(
        &mut self,
        def_id: DefId,
        self_ty: &(ast::Path, NodeId),
        trait_: &(ast::Path, NodeId),
        items: &'a ThinVec<ast::AssocItem>,
        span: Span,
        visibility: Visibility,
    ) -> OwnerInfo {
        let owner_id = OwnerId(def_id.0);
        let hir_id = HirId::make_owner(def_id);

        let items: ThinVec<DefId> = items
            .iter()
            .map(|item| {
                *self
                    .resolver
                    .def_map
                    .get(&item.node_id)
                    .expect("assoc item has DefId")
            })
            .collect();

        let module_id = *self
            .resolver
            .def_to_module
            .get(&def_id)
            .expect("module id exists");

        let self_res = self
            .resolver
            .res_map
            .get(&self_ty.1)
            .expect("resolution exists")
            .full_res();
        let Some(self_res) = self_res else {
            builders::emit_at(
                self.ctx,
                self_ty.0.span,
                module_id,
                diag::ExpectedPathToStruct,
                diag_params! { path = self_ty.0.display(self.ctx) },
            );
            return OwnerInfo {
                nodes: OwnerNodes {
                    nodes: Vec::new(),
                    bodies: FxHashMap::default(),
                },
            };
        };

        let self_ty = self.lower_resolved_path(&self_ty.0, self_res);

        let trait_res = self
            .resolver
            .res_map
            .get(&trait_.1)
            .expect("resolution exists")
            .full_res();
        let Some(trait_res) = trait_res else {
            builders::emit_at(
                self.ctx,
                trait_.0.span,
                module_id,
                diag::ExpectedPathToTrait,
                diag_params! { path = trait_.0.display(self.ctx) },
            );
            return OwnerInfo {
                nodes: OwnerNodes {
                    nodes: Vec::new(),
                    bodies: FxHashMap::default(),
                },
            };
        };

        let trait_ty = self.lower_resolved_path(&trait_.0, trait_res);

        OwnerInfo {
            nodes: OwnerNodes {
                nodes: vec![ParentedNode {
                    parent: ItemLocalId::ZERO,
                    node: Node::Item(Box::new(Item {
                        hir_id,
                        owner_id,
                        kind: ItemKind::Impl {
                            self_ty,
                            trait_ty,
                            items,
                        },
                        span,
                        visibility,
                    })),
                }],
                bodies: FxHashMap::default(),
            },
        }
    }

    fn lower_trait(
        &mut self,
        def_id: DefId,
        name: &'a Ident,
        items: &'a ThinVec<ast::AssocItem>,
        generic_params: Option<&ast::GenericParams>,
        span: Span,
        visibility: Visibility,
    ) -> OwnerInfo {
        let owner_id = OwnerId(def_id.0);
        let hir_id = HirId::make_owner(def_id);

        let generic_params = self.lower_generic_params(generic_params);

        let items: ThinVec<DefId> = items
            .iter()
            .map(|item| {
                *self
                    .resolver
                    .def_map
                    .get(&item.node_id)
                    .expect("assoc item has DefId")
            })
            .collect();

        OwnerInfo {
            nodes: OwnerNodes {
                nodes: vec![ParentedNode {
                    parent: ItemLocalId::ZERO,
                    node: Node::Item(Box::new(Item {
                        hir_id,
                        owner_id,
                        kind: ItemKind::Trait {
                            name: name.value,
                            generic_params,
                            items,
                        },
                        span,
                        visibility,
                    })),
                }],
                bodies: FxHashMap::default(),
            },
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_struct(
        &mut self,
        def_id: DefId,
        name: &'a Ident,
        fields: &'a ThinVec<(Ident, ast::Type, Visibility)>,
        items: &'a ThinVec<ast::AssocItem>,
        generic_params: Option<&ast::GenericParams>,
        span: Span,
        visibility: Visibility,
    ) -> OwnerInfo {
        let owner_id = OwnerId(def_id.0);
        let hir_id = HirId::make_owner(def_id);

        let generic_params = self.lower_generic_params(generic_params);

        let fields: ThinVec<StructField> = fields
            .iter()
            .map(|(name, ty, vis)| StructField {
                name: name.value,
                visibility: *vis,
                ty: self.lower_type(ty),
            })
            .collect();

        let items: ThinVec<DefId> = items
            .iter()
            .map(|item| {
                *self
                    .resolver
                    .def_map
                    .get(&item.node_id)
                    .expect("assoc item has DefId")
            })
            .collect();

        OwnerInfo {
            nodes: OwnerNodes {
                nodes: vec![ParentedNode {
                    parent: ItemLocalId::ZERO,
                    node: Node::Item(Box::new(Item {
                        hir_id,
                        owner_id,
                        kind: ItemKind::Struct {
                            name: name.value,
                            generic_params,
                            fields,
                            items,
                        },
                        span,
                        visibility,
                    })),
                }],
                bodies: FxHashMap::default(),
            },
        }
    }

    fn lower_type_alias(
        &mut self,
        def_id: DefId,
        name: &'a Ident,
        type_: &'a ast::Type,
        generic_params: Option<&ast::GenericParams>,
        span: Span,
        visibility: Visibility,
    ) -> OwnerInfo {
        let owner_id = OwnerId(def_id.0);
        let hir_id = HirId::make_owner(def_id);

        let generic_params = self.lower_generic_params(generic_params);

        OwnerInfo {
            nodes: OwnerNodes {
                nodes: vec![ParentedNode {
                    parent: ItemLocalId::ZERO,
                    node: Node::Item(Box::new(Item {
                        hir_id,
                        owner_id,
                        kind: ItemKind::TypeAlias {
                            name: name.value,
                            type_: self.lower_type(type_),
                            generic_params,
                        },
                        span,
                        visibility,
                    })),
                }],
                bodies: FxHashMap::default(),
            },
        }
    }

    fn lower_const(
        &mut self,
        def_id: DefId,
        name: &'a Ident,
        ty: &'a ast::Type,
        value: &'a ast::Expr,
        span: Span,
        visibility: Visibility,
    ) -> OwnerInfo {
        let owner_id = OwnerId(def_id.0);
        let hir_id = HirId::make_owner(def_id);

        let ty = self.lower_type(ty);
        let init = self.lower_expr(value);

        let local_id = self.next_local_id();
        let body_id = BodyId(local_id);
        let bodies = {
            let mut bodies = FxHashMap::default();
            bodies.insert(body_id, Body { value: init });
            bodies
        };

        OwnerInfo {
            nodes: OwnerNodes {
                nodes: vec![ParentedNode {
                    parent: ItemLocalId::ZERO,
                    node: Node::Item(Box::new(Item {
                        hir_id,
                        owner_id,
                        kind: ItemKind::Const {
                            name: name.value,
                            ty,
                            body_id: Some(body_id),
                        },
                        span,
                        visibility,
                    })),
                }],
                bodies,
            },
        }
    }

    fn lower_fn(
        &mut self,
        def_id: DefId,
        f: &'a ast::Fn,
        span: Span,
        visibility: Visibility,
        associated: Option<DefId>,
    ) -> OwnerInfo {
        let owner_id = OwnerId(def_id.0);
        let hir_id = HirId::make_owner(def_id);

        let generic_params = self.lower_generic_params(f.generic_params.as_ref());

        let params: ThinVec<Param> = f
            .parameters
            .iter()
            .map(|(name, ty, node_id)| {
                let param_hir_id = self.next_hir_id();
                self.register_local(*node_id, param_hir_id);
                Param {
                    hir_id: param_hir_id,
                    name: name.value,
                    ty: self.lower_type(ty),
                    span: name.span,
                }
            })
            .collect();

        let ret = self.lower_type(&f.return_type);

        let mut bodies = FxHashMap::default();
        let body_id = f.body.as_ref().map(|block| {
            let (body_id, body) = self.lower_block_body(block);
            bodies.insert(body_id, body);
            body_id
        });

        let fun = Fn {
            sig: FnSig {
                is_extern: f.is_extern,
            },
            decl: FnDecl { params, ret },
            generic_params,
            body_id,
        };

        let node = if associated.is_some() {
            Node::AssocItem(Box::new(AssocItem {
                kind: AssocItemKind::Fn(fun),
                hir_id,
                owner_id,
                span,
            }))
        } else {
            Node::Item(Box::new(Item {
                kind: ItemKind::Fn(fun),
                hir_id,
                owner_id,
                span,
                visibility,
            }))
        };

        OwnerInfo {
            nodes: OwnerNodes {
                nodes: vec![ParentedNode {
                    parent: ItemLocalId::ZERO,
                    node,
                }],
                bodies,
            },
        }
    }

    fn lower_block_body(&mut self, block: &ast::Block) -> (BodyId, Body) {
        let stmts = block
            .stmts
            .iter()
            .map(|stmt| self.lower_stmt(stmt))
            .collect();
        let block_expr = Expr {
            hir_id: self.next_hir_id(),
            kind: ExprKind::Block(Block {
                stmts,
                span: block.span,
                hir_id: self.next_hir_id(),
            }),
            span: block.span,
        };
        let local_id = self.next_local_id();
        (BodyId(local_id), Body { value: block_expr })
    }

    fn lower_generic_params(
        &mut self,
        generic_params: Option<&ast::GenericParams>,
    ) -> Option<ThinVec<GenericParam>> {
        generic_params.map(|ast::GenericParams { params, .. }| {
            params
                .iter()
                .map(
                    |ast::GenericParam {
                         name,
                         node_id,
                         default,
                     }| {
                        let param_hir_id = self.next_hir_id();
                        self.register_local(*node_id, param_hir_id);
                        GenericParam {
                            hir_id: param_hir_id,
                            name: name.value,
                            span: name.span,
                            default: default.as_ref().map(|ty| self.lower_type(ty)),
                        }
                    },
                )
                .collect()
        })
    }

    fn with_owner(
        &mut self,
        def_id: DefId,
        hir_crate: &mut Crate,
        f: impl FnOnce(&mut Self, DefId) -> Option<OwnerInfo>,
    ) {
        self.current_owner = Some(OwnerId(def_id.0));
        self.next_local_id = 1;
        let opt = f(self, def_id);
        self.current_owner = None;

        if let Some(info) = opt {
            hir_crate.ensure_owner(def_id);
            let owner = hir_crate.owner_mut(def_id).expect("owner exists");
            *owner = MaybeOwner::Owner(Box::new(info));
        }
    }
}
