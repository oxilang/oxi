mod expr;
mod item;
mod stmt;

use thin_vec::ThinVec;

use crate::ast::{self, NodeId};
use crate::diag_params;
use crate::errors::builders;
use crate::hir::index::{AstIndex, AstOwner};
use crate::hir::owner::HirId;
use crate::hir::{AstLoweringContext, Crate, DefId, DefKind};
use crate::hir::{diag, types::*};
use crate::resolve::{PartialRes, Res};

impl<'a, 'ctx> AstLoweringContext<'a, 'ctx> {
    pub(super) fn lower_node(
        &mut self,
        def_id: DefId,
        index: &AstIndex<'a>,
        hir_crate: &mut Crate,
    ) {
        match index.get(def_id) {
            AstOwner::NonOwner => {}
            AstOwner::Item(item) => self.lower_item(def_id, item, hir_crate),
            AstOwner::AssocItem(item) => self.lower_assoc_item(def_id, item, hir_crate),
        }
    }

    pub(super) fn lower_qpath(&mut self, path: &ast::Path, node_id: NodeId) -> QPath {
        let partial = self
            .resolver
            .res_map
            .get(&node_id)
            .copied()
            .unwrap_or(PartialRes::new(Res::Err));
        let unresolved = partial.unresolved_segments();

        if unresolved == 0 {
            return QPath::Resolved(None, self.lower_resolved_path(path, partial.base_res()));
        }

        let start = path.segments.len() - unresolved;
        let prefix = ast::Path {
            segments: path.segments[..start].into(),
            span: path.span,
        };
        let resolved = self.lower_resolved_path(&prefix, partial.base_res());

        let tail = &path.segments[start..];
        tail.iter()
            .fold(QPath::Resolved(None, resolved), |qself, segment| {
                QPath::TypeRelative {
                    qself: Box::new(qself),
                    segment: self.lower_path_segment(segment),
                }
            })
    }

    fn lower_resolved_path(&mut self, path: &ast::Path, res: Res) -> Path {
        Path {
            res: self.lower_res(res),
            segments: path
                .segments
                .iter()
                .map(|s| self.lower_path_segment(s))
                .collect(),
            span: path.span,
        }
    }

    fn lower_path_segment(&mut self, segment: &ast::PathSegment) -> PathSegment {
        PathSegment {
            ident: segment.ident,
            generic_args: segment
                .generic_args
                .as_ref()
                .map(|args| args.iter().map(|ty| self.lower_type(ty)).collect()),
        }
    }

    fn lower_res(&self, res: Res) -> Res<HirId> {
        match res {
            Res::Def(def_id) => Res::Def(def_id),
            Res::PrimTy(prim) => Res::PrimTy(prim),
            Res::Local(local_node_id) => match self.lookup_local(local_node_id) {
                Some(hir_id) => Res::Local(hir_id),
                None => Res::Err,
            },
            Res::GenericParam(param_node_id) => match self.lookup_local(param_node_id) {
                Some(hir_id) => Res::GenericParam(hir_id),
                None => Res::Err,
            },
            Res::SelfTyAlias { alias_to } => Res::SelfTyAlias { alias_to },
            Res::Err => Res::Err,
        }
    }

    pub(super) fn lower_type(&mut self, ty: &ast::Type) -> Ty {
        let hir_id = self.next_hir_id();
        let kind = match &ty.kind {
            ast::TypeKind::Symbol(path) => {
                let res = self
                    .resolver
                    .res_map
                    .get(&ty.node_id)
                    .expect("path resolved");
                match res.full_res() {
                    Some(Res::GenericParam(id)) => TyKind::GenericParam(
                        self.lookup_local(id).expect("local exists"),
                        path.segments[0].ident.value,
                    ),
                    _ => {
                        let qpath = self.lower_qpath(path, ty.node_id);
                        if let QPath::Resolved(_, resolved) = &qpath
                            && let Res::Def(def_id) = resolved.res
                            && self.resolver.defs[def_id.0 as usize].kind == DefKind::Trait
                            && let Some(module_id) = self
                                .current_owner
                                .and_then(|owner| {
                                    self.resolver.def_to_module.get(&owner.to_def_id())
                                })
                                .copied()
                        {
                            let trait_name = self
                                .ctx
                                .interner
                                .lookup(
                                    self.resolver.defs[def_id.0 as usize]
                                        .name
                                        .expect("trait def should have a name"),
                                )
                                .to_string();
                            builders::emit_at(
                                self.ctx,
                                ty.span,
                                module_id,
                                diag::ExpectedTypeFoundTrait,
                                diag_params! { trait = trait_name },
                            );
                        }
                        TyKind::Path(qpath)
                    }
                }
            }
            ast::TypeKind::Pointer(inner, mutability) => {
                TyKind::Ptr(Box::new(self.lower_type(inner)), *mutability)
            }
            ast::TypeKind::Slice(inner) => TyKind::Slice(Box::new(self.lower_type(inner))),
            ast::TypeKind::FixedArray(inner, size) => {
                TyKind::Array(Box::new(self.lower_type(inner)), *size)
            }
            ast::TypeKind::Function { params, ret } => {
                let params = params.iter().map(|p| self.lower_type(p)).collect();
                TyKind::Fn {
                    params,
                    ret: Box::new(self.lower_type(ret)),
                }
            }
            ast::TypeKind::Tuple(elements) => {
                TyKind::Tuple(elements.iter().map(|e| self.lower_type(e)).collect())
            }
            ast::TypeKind::Projection {
                base,
                trait_,
                assoc,
                generic_args,
            } => {
                let generic_args = generic_args.as_ref().map(|args| {
                    args.iter()
                        .map(|t| self.lower_type(t))
                        .collect::<ThinVec<_>>()
                });
                let base_qpath = self.lower_qpath(&base.0, base.1);
                let trait_qpath = self.lower_qpath(&trait_.0, trait_.1);
                let base_ty = Ty {
                    hir_id: self.next_hir_id(),
                    kind: TyKind::Path(base_qpath),
                    span: ty.span,
                };
                let QPath::Resolved(_, trait_path) = trait_qpath else {
                    unreachable!()
                };
                let qself = QPath::Resolved(Some(Box::new(base_ty)), trait_path);
                let segment = PathSegment {
                    ident: *assoc,
                    generic_args,
                };
                TyKind::Path(QPath::TypeRelative {
                    qself: Box::new(qself),
                    segment,
                })
            }
            ast::TypeKind::Infer => TyKind::Infer,
            ast::TypeKind::Never => TyKind::Never,
        };

        Ty {
            hir_id,
            kind,
            span: ty.span,
        }
    }
}
