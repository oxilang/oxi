use thin_vec::ThinVec;

use crate::ast::visit::VisitAction;
use crate::typeck::Ty;

pub trait TyVisitor {
    fn visit_ty(&mut self, ty: &Ty) -> VisitAction;
}

pub trait TyVisitable {
    fn visit(&self, visitor: &mut impl TyVisitor);
}

impl TyVisitable for Ty {
    fn visit(&self, visitor: &mut impl TyVisitor) {
        match visitor.visit_ty(self) {
            VisitAction::Continue => match self {
                Ty::Var(_) | Ty::Prim(_) | Ty::Never | Ty::Error | Ty::MethodCallee => {}
                Ty::Ptr(inner, _) | Ty::Slice(inner) | Ty::Array(inner, _) => inner.visit(visitor),
                Ty::Fn { params, ret } => {
                    params.visit(visitor);
                    ret.visit(visitor);
                }
                Ty::Tuple(elements) => elements.visit(visitor),
                Ty::Adt(_, generics) => generics.visit(visitor),
                Ty::Alias { generic_args, .. } => generic_args.visit(visitor),
                Ty::Projection {
                    self_ty,
                    generic_args,
                    ..
                } => {
                    self_ty.visit(visitor);
                    generic_args.visit(visitor);
                }
            },
            VisitAction::SkipChildren => {}
        }
    }
}

impl<T: TyVisitable> TyVisitable for ThinVec<T> {
    fn visit(&self, visitor: &mut impl TyVisitor) {
        for inner in self {
            inner.visit(visitor);
        }
    }
}

impl<T: TyVisitable> TyVisitable for Option<T> {
    fn visit(&self, visitor: &mut impl TyVisitor) {
        if let Some(inner) = self {
            inner.visit(visitor);
        }
    }
}
