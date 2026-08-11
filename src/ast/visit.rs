use std::hash::Hash;

use thin_vec::ThinVec;

use crate::ast::*;
use fxhash::FxHashMap;

pub enum VisitAction {
    /// Descend into children
    Continue,
    /// Don't descend into children
    SkipChildren,
}

pub trait Visitor {
    fn visit_item(&mut self, item: &Item) -> VisitAction {
        _ = item;
        VisitAction::Continue
    }
    fn visit_assoc_item(&mut self, item: &AssocItem) -> VisitAction {
        _ = item;
        VisitAction::Continue
    }
    fn visit_stmt(&mut self, stmt: &Stmt) -> VisitAction {
        _ = stmt;
        VisitAction::Continue
    }
    fn visit_expr(&mut self, expr: &Expr) -> VisitAction {
        _ = expr;
        VisitAction::Continue
    }
    fn visit_type(&mut self, ty: &Type) -> VisitAction {
        _ = ty;
        VisitAction::Continue
    }
}

pub trait VisitorMut {
    fn visit_item(&mut self, item: &mut Item) -> VisitAction {
        _ = item;
        VisitAction::Continue
    }
    fn visit_assoc_item(&mut self, item: &mut AssocItem) -> VisitAction {
        _ = item;
        VisitAction::Continue
    }
    fn visit_stmt(&mut self, stmt: &mut Stmt) -> VisitAction {
        _ = stmt;
        VisitAction::Continue
    }
    fn visit_expr(&mut self, expr: &mut Expr) -> VisitAction {
        _ = expr;
        VisitAction::Continue
    }
    fn visit_type(&mut self, ty: &mut Type) -> VisitAction {
        _ = ty;
        VisitAction::Continue
    }
}

pub trait Visitable {
    fn visit(&self, visitor: &mut impl Visitor);
    fn visit_mut(&mut self, visitor: &mut impl VisitorMut);
}

impl<T: Visitable> Visitable for Box<T> {
    fn visit(&self, visitor: &mut impl Visitor) {
        self.as_ref().visit(visitor);
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        self.as_mut().visit_mut(visitor);
    }
}

impl<T: Visitable> Visitable for Option<T> {
    fn visit(&self, visitor: &mut impl Visitor) {
        if let Some(inner) = self {
            inner.visit(visitor);
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        if let Some(inner) = self {
            inner.visit_mut(visitor);
        }
    }
}

impl<T: Visitable> Visitable for ThinVec<T> {
    fn visit(&self, visitor: &mut impl Visitor) {
        for inner in self {
            inner.visit(visitor);
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        for inner in self {
            inner.visit_mut(visitor);
        }
    }
}

impl<T: Visitable> Visitable for Vec<T> {
    fn visit(&self, visitor: &mut impl Visitor) {
        for inner in self {
            inner.visit(visitor);
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        for inner in self {
            inner.visit_mut(visitor);
        }
    }
}

impl<T: Visitable> Visitable for Box<[T]> {
    fn visit(&self, visitor: &mut impl Visitor) {
        for inner in self.iter() {
            inner.visit(visitor);
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        for inner in self.iter_mut() {
            inner.visit_mut(visitor);
        }
    }
}

impl<K: Eq + Hash, V: Visitable> Visitable for FxHashMap<K, V> {
    fn visit(&self, visitor: &mut impl Visitor) {
        for value in self.values() {
            value.visit(visitor);
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        for value in self.values_mut() {
            value.visit_mut(visitor);
        }
    }
}

impl Visitable for Path {
    fn visit(&self, visitor: &mut impl Visitor) {
        self.segments.visit(visitor);
    }
    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        self.segments.visit_mut(visitor);
    }
}

impl Visitable for PathSegment {
    fn visit(&self, visitor: &mut impl Visitor) {
        self.generic_args.visit(visitor);
    }
    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        self.generic_args.visit_mut(visitor);
    }
}

impl Visitable for Ast {
    fn visit(&self, visitor: &mut impl Visitor) {
        self.items.visit(visitor);
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        self.items.visit_mut(visitor);
    }
}

impl Visitable for Item {
    fn visit(&self, visitor: &mut impl Visitor) {
        match visitor.visit_item(self) {
            VisitAction::Continue => match &self.kind {
                ItemKind::Const { value, ty, .. } => {
                    value.visit(visitor);
                    ty.visit(visitor);
                }
                ItemKind::Struct {
                    fields,
                    items,
                    generic_params,
                    ..
                } => {
                    generic_params.visit(visitor);
                    for field in fields {
                        field.1.visit(visitor);
                    }
                    items.visit(visitor);
                }
                ItemKind::Type {
                    generic_params,
                    type_,
                    ..
                } => {
                    generic_params.visit(visitor);
                    type_.visit(visitor);
                }
                ItemKind::Trait {
                    items,
                    generic_params,
                    ..
                } => {
                    generic_params.visit(visitor);
                    items.visit(visitor);
                }
                ItemKind::Impl {
                    self_ty,
                    trait_,
                    items,
                } => {
                    self_ty.0.visit(visitor);
                    trait_.0.visit(visitor);
                    items.visit(visitor);
                }
                ItemKind::Fn(f) => f.visit(visitor),
                ItemKind::Module { body, .. } => {
                    body.visit(visitor);
                }
                ItemKind::Import(_) => {}
            },
            VisitAction::SkipChildren => {}
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        match visitor.visit_item(self) {
            VisitAction::Continue => match &mut self.kind {
                ItemKind::Const { value, ty, .. } => {
                    value.visit_mut(visitor);
                    ty.visit_mut(visitor);
                }
                ItemKind::Struct {
                    fields,
                    items,
                    generic_params,
                    ..
                } => {
                    generic_params.visit_mut(visitor);
                    for field in fields {
                        field.1.visit_mut(visitor);
                    }
                    items.visit_mut(visitor);
                }
                ItemKind::Type {
                    generic_params,
                    type_,
                    ..
                } => {
                    generic_params.visit_mut(visitor);
                    type_.visit_mut(visitor);
                }
                ItemKind::Trait {
                    items,
                    generic_params,
                    ..
                } => {
                    generic_params.visit_mut(visitor);
                    items.visit_mut(visitor);
                }
                ItemKind::Impl {
                    self_ty,
                    trait_,
                    items,
                } => {
                    self_ty.0.visit_mut(visitor);
                    trait_.0.visit_mut(visitor);
                    items.visit_mut(visitor);
                }
                ItemKind::Fn(f) => f.visit_mut(visitor),
                ItemKind::Module { body, .. } => {
                    body.visit_mut(visitor);
                }
                ItemKind::Import(_) => {}
            },
            VisitAction::SkipChildren => {}
        }
    }
}

impl Visitable for AssocItem {
    fn visit(&self, visitor: &mut impl Visitor) {
        match visitor.visit_assoc_item(self) {
            VisitAction::Continue => self.kind.visit(visitor),
            VisitAction::SkipChildren => {}
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        match visitor.visit_assoc_item(self) {
            VisitAction::Continue => self.kind.visit_mut(visitor),
            VisitAction::SkipChildren => {}
        }
    }
}

impl Visitable for AssocItemKind {
    fn visit(&self, visitor: &mut impl Visitor) {
        match self {
            AssocItemKind::Fn(f) => f.visit(visitor),
            AssocItemKind::Type { type_, .. } => {
                type_.visit(visitor);
            }
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        match self {
            AssocItemKind::Fn(f) => f.visit_mut(visitor),
            AssocItemKind::Type { type_, .. } => {
                type_.visit_mut(visitor);
            }
        }
    }
}

impl Visitable for Fn {
    fn visit(&self, visitor: &mut impl Visitor) {
        self.generic_params.visit(visitor);
        for arg in &self.parameters {
            arg.1.visit(visitor);
        }
        self.body.visit(visitor);
        self.return_type.visit(visitor);
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        self.generic_params.visit_mut(visitor);
        for arg in &mut self.parameters {
            arg.1.visit_mut(visitor);
        }
        self.body.visit_mut(visitor);
        self.return_type.visit_mut(visitor);
    }
}

impl Visitable for Block {
    fn visit(&self, visitor: &mut impl Visitor) {
        self.stmts.visit(visitor);
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        self.stmts.visit_mut(visitor);
    }
}

impl Visitable for GenericParams {
    fn visit(&self, visitor: &mut impl Visitor) {
        self.params.visit(visitor);
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        self.params.visit_mut(visitor);
    }
}

impl Visitable for GenericParam {
    fn visit(&self, visitor: &mut impl Visitor) {
        self.default.visit(visitor);
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        self.default.visit_mut(visitor);
    }
}

impl Visitable for Stmt {
    fn visit(&self, visitor: &mut impl Visitor) {
        match visitor.visit_stmt(self) {
            VisitAction::Continue => match &self.kind {
                StmtKind::Expr(expr) | StmtKind::Semi(expr) => expr.visit(visitor),
                StmtKind::Let { ty, value, .. } => {
                    value.visit(visitor);
                    ty.visit(visitor);
                }
            },
            VisitAction::SkipChildren => {}
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        match visitor.visit_stmt(self) {
            VisitAction::Continue => match &mut self.kind {
                StmtKind::Expr(expr) | StmtKind::Semi(expr) => expr.visit_mut(visitor),
                StmtKind::Let { ty, value, .. } => {
                    value.visit_mut(visitor);
                    ty.visit_mut(visitor);
                }
            },
            VisitAction::SkipChildren => {}
        }
    }
}

impl Visitable for Expr {
    fn visit(&self, visitor: &mut impl Visitor) {
        match visitor.visit_expr(self) {
            VisitAction::Continue => match &self.kind {
                ExprKind::Literal(_) => {}
                ExprKind::Block(b) => b.visit(visitor),
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    condition.visit(visitor);
                    then_branch.visit(visitor);
                    else_branch.visit(visitor);
                }
                ExprKind::While { condition, body } => {
                    condition.visit(visitor);
                    body.visit(visitor);
                }
                ExprKind::Loop(b) => b.visit(visitor),
                ExprKind::Path(path) => path.visit(visitor),
                ExprKind::Binary { left, right, .. } => {
                    left.visit(visitor);
                    right.visit(visitor);
                }
                ExprKind::Dereference { expr } => expr.visit(visitor),
                ExprKind::Reference { expr, .. } => expr.visit(visitor),
                ExprKind::Unary { right, .. } => right.visit(visitor),
                ExprKind::Range { start, end, .. } => {
                    start.visit(visitor);
                    end.visit(visitor);
                }
                ExprKind::Assignment {
                    assignee, value, ..
                } => {
                    assignee.visit(visitor);
                    value.visit(visitor);
                }
                ExprKind::StructInstantiation { path, fields } => {
                    path.visit(visitor);
                    for field in fields {
                        field.1.visit(visitor);
                    }
                }
                ExprKind::Array { contents } => contents.visit(visitor),
                ExprKind::FunctionCall { callee, arguments } => {
                    callee.visit(visitor);
                    arguments.visit(visitor);
                }
                ExprKind::MemberAccess { base, .. } => base.visit(visitor),
                ExprKind::Index { base, index } => {
                    base.visit(visitor);
                    index.visit(visitor);
                }
                ExprKind::As { expr, ty } => {
                    expr.visit(visitor);
                    ty.visit(visitor);
                }
                ExprKind::Tuple { elements } => elements.visit(visitor),
                ExprKind::Break(b) => b.visit(visitor),
                ExprKind::Return(r) => r.visit(visitor),
            },
            VisitAction::SkipChildren => {}
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        match visitor.visit_expr(self) {
            VisitAction::Continue => match &mut self.kind {
                ExprKind::Literal(_) => {}
                ExprKind::Block(b) => b.visit_mut(visitor),
                ExprKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    condition.visit_mut(visitor);
                    then_branch.visit_mut(visitor);
                    else_branch.visit_mut(visitor);
                }
                ExprKind::While { condition, body } => {
                    condition.visit_mut(visitor);
                    body.visit_mut(visitor);
                }
                ExprKind::Loop(b) => b.visit_mut(visitor),
                ExprKind::Path(path) => path.visit_mut(visitor),
                ExprKind::Binary { left, right, .. } => {
                    left.visit_mut(visitor);
                    right.visit_mut(visitor);
                }
                ExprKind::Dereference { expr } => {
                    expr.visit_mut(visitor);
                }
                ExprKind::Reference { expr, .. } => {
                    expr.visit_mut(visitor);
                }
                ExprKind::Unary { right, .. } => {
                    right.visit_mut(visitor);
                }
                ExprKind::Range { start, end, .. } => {
                    start.visit_mut(visitor);
                    end.visit_mut(visitor);
                }
                ExprKind::Assignment {
                    assignee, value, ..
                } => {
                    assignee.visit_mut(visitor);
                    value.visit_mut(visitor);
                }
                ExprKind::StructInstantiation { path, fields } => {
                    path.visit_mut(visitor);
                    for field in fields {
                        field.1.visit_mut(visitor);
                    }
                }
                ExprKind::Array { contents } => contents.visit_mut(visitor),
                ExprKind::FunctionCall { callee, arguments } => {
                    callee.visit_mut(visitor);
                    arguments.visit_mut(visitor);
                }
                ExprKind::MemberAccess { base, .. } => base.visit_mut(visitor),
                ExprKind::Index { base, index } => {
                    base.visit_mut(visitor);
                    index.visit_mut(visitor);
                }
                ExprKind::As { expr, ty } => {
                    expr.visit_mut(visitor);
                    ty.visit_mut(visitor);
                }
                ExprKind::Tuple { elements } => elements.visit_mut(visitor),
                ExprKind::Break(b) => b.visit_mut(visitor),
                ExprKind::Return(r) => r.visit_mut(visitor),
            },
            VisitAction::SkipChildren => {}
        }
    }
}

impl Visitable for Type {
    fn visit(&self, visitor: &mut impl Visitor) {
        match visitor.visit_type(self) {
            VisitAction::Continue => match &self.kind {
                TypeKind::Symbol(path) => path.visit(visitor),
                TypeKind::Pointer(ty, _) => ty.visit(visitor),
                TypeKind::Slice(ty) => ty.visit(visitor),
                TypeKind::FixedArray(ty, _) => ty.visit(visitor),
                TypeKind::Function { params, ret } => {
                    params.visit(visitor);
                    ret.visit(visitor);
                }
                TypeKind::Tuple(elements) => elements.visit(visitor),
                TypeKind::Projection {
                    base,
                    trait_,
                    generic_args,
                    ..
                } => {
                    base.0.visit(visitor);
                    trait_.0.visit(visitor);
                    generic_args.visit(visitor);
                }
                TypeKind::Infer => {}
                TypeKind::Never => {}
            },
            VisitAction::SkipChildren => {}
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        match visitor.visit_type(self) {
            VisitAction::Continue => match &mut self.kind {
                TypeKind::Symbol(path) => path.visit_mut(visitor),
                TypeKind::Pointer(ty, _) => ty.visit_mut(visitor),
                TypeKind::Slice(ty) => ty.visit_mut(visitor),
                TypeKind::FixedArray(ty, _) => ty.visit_mut(visitor),
                TypeKind::Function { params, ret } => {
                    params.visit_mut(visitor);
                    ret.visit_mut(visitor);
                }
                TypeKind::Tuple(elements) => elements.visit_mut(visitor),
                TypeKind::Projection {
                    base,
                    trait_,
                    generic_args,
                    ..
                } => {
                    base.0.visit_mut(visitor);
                    trait_.0.visit_mut(visitor);
                    generic_args.visit_mut(visitor);
                }
                TypeKind::Infer => {}
                TypeKind::Never => {}
            },
            VisitAction::SkipChildren => {}
        }
    }
}
