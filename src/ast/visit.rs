use std::hash::Hash;

use thin_vec::ThinVec;

use crate::ast::*;
use fxhash::FxHashMap;

pub enum VisitAction {
    /// Descend into children
    Continue,
    /// Don't descend
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

impl Visitable for Ast {
    fn visit(&self, visitor: &mut impl Visitor) {
        for item in &self.items {
            item.visit(visitor);
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        for item in &mut self.items {
            item.visit_mut(visitor);
        }
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
                    if let Some(params) = generic_params {
                        params.visit(visitor);
                    }
                    for field in fields {
                        field.1.visit(visitor);
                    }
                    items.visit(visitor);
                }
                ItemKind::Trait {
                    items,
                    generic_params,
                    ..
                } => {
                    if let Some(params) = generic_params {
                        params.visit(visitor);
                    }
                    items.visit(visitor);
                }
                ItemKind::Impl {
                    self_ty,
                    trait_,
                    items,
                } => {
                    for segment in &self_ty.0.segments {
                        segment.generic_args.visit(visitor);
                    }
                    for segment in &trait_.0.segments {
                        segment.generic_args.visit(visitor);
                    }
                    items.visit(visitor);
                }
                ItemKind::Fn(f) => f.visit(visitor),
                ItemKind::Import(_) => {
                    // Leaf
                }
                ItemKind::Module { body, .. } => {
                    if let Some(items) = body {
                        items.visit(visitor);
                    }
                }
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
                    if let Some(params) = generic_params {
                        params.visit_mut(visitor);
                    }
                    for field in fields {
                        field.1.visit_mut(visitor);
                    }
                    items.visit_mut(visitor);
                }
                ItemKind::Trait {
                    items,
                    generic_params,
                    ..
                } => {
                    if let Some(params) = generic_params {
                        params.visit_mut(visitor);
                    }
                    items.visit_mut(visitor);
                }
                ItemKind::Impl {
                    self_ty,
                    trait_,
                    items,
                } => {
                    for segment in &mut self_ty.0.segments {
                        segment.generic_args.visit_mut(visitor);
                    }
                    for segment in &mut trait_.0.segments {
                        segment.generic_args.visit_mut(visitor);
                    }
                    items.visit_mut(visitor);
                }
                ItemKind::Fn(f) => f.visit_mut(visitor),
                ItemKind::Import(_) => {
                    // Leaf
                }
                ItemKind::Module { body, .. } => {
                    if let Some(items) = body {
                        items.visit_mut(visitor);
                    }
                }
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
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        match self {
            AssocItemKind::Fn(f) => f.visit_mut(visitor),
        }
    }
}

impl Visitable for Fn {
    fn visit(&self, visitor: &mut impl Visitor) {
        if let Some(params) = &self.generic_params {
            params.visit(visitor);
        }
        for arg in &self.parameters {
            arg.1.visit(visitor);
        }
        if let Some(body) = &self.body {
            body.visit(visitor);
        }
        self.return_type.visit(visitor);
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        if let Some(params) = &mut self.generic_params {
            params.visit_mut(visitor);
        }
        for arg in &mut self.parameters {
            arg.1.visit_mut(visitor);
        }
        if let Some(body) = &mut self.body {
            body.visit_mut(visitor);
        }
        self.return_type.visit_mut(visitor);
    }
}

impl Visitable for Block {
    fn visit(&self, visitor: &mut impl Visitor) {
        self.stmts.visit(visitor);
        self.tail.visit(visitor);
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        self.stmts.visit_mut(visitor);
        self.tail.visit_mut(visitor);
    }
}

impl Visitable for GenericParams {
    fn visit(&self, visitor: &mut impl Visitor) {
        for param in &self.params {
            param.visit(visitor);
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        for param in &mut self.params {
            param.visit_mut(visitor);
        }
    }
}

impl Visitable for GenericParam {
    fn visit(&self, visitor: &mut impl Visitor) {
        if let Some(ty) = &self.default {
            ty.visit(visitor);
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        if let Some(ty) = &mut self.default {
            ty.visit_mut(visitor);
        }
    }
}

impl Visitable for Stmt {
    fn visit(&self, visitor: &mut impl Visitor) {
        match visitor.visit_stmt(self) {
            VisitAction::Continue => match &self.kind {
                StmtKind::Expr(expr) => expr.visit(visitor),
                StmtKind::Let {
                    name: _,
                    ty,
                    value,
                    mutability: _,
                } => {
                    if let Some(val) = value {
                        val.visit(visitor);
                    }
                    ty.visit(visitor);
                }
            },
            VisitAction::SkipChildren => {}
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        match visitor.visit_stmt(self) {
            VisitAction::Continue => match &mut self.kind {
                StmtKind::Expr(expr) => expr.visit_mut(visitor),
                StmtKind::Let {
                    name: _,
                    ty,
                    value,
                    mutability: _,
                } => {
                    if let Some(val) = value {
                        val.visit_mut(visitor);
                    }
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
                ExprKind::Literal(l) => l.visit(visitor),
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
                ExprKind::Path(path) => {
                    for segment in &path.segments {
                        segment.generic_args.visit(visitor);
                    }
                }
                ExprKind::Binary {
                    left,
                    operator: _,
                    right,
                } => {
                    left.visit(visitor);
                    right.visit(visitor);
                }
                ExprKind::Dereference { expr } => {
                    expr.visit(visitor);
                }
                ExprKind::Reference { expr, .. } => {
                    expr.visit(visitor);
                }
                ExprKind::Unary { operator: _, right } => {
                    right.visit(visitor);
                }
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
                    for segment in &path.segments {
                        segment.generic_args.visit(visitor);
                    }
                    for field in fields {
                        field.1.visit(visitor);
                    }
                }
                ExprKind::Array { contents } => {
                    contents.visit(visitor);
                }
                ExprKind::FunctionCall { callee, arguments } => {
                    callee.visit(visitor);
                    arguments.visit(visitor);
                }
                ExprKind::MemberAccess { base, .. } => {
                    base.visit(visitor);
                }
                ExprKind::Index { base, index } => {
                    base.visit(visitor);
                    index.visit(visitor);
                }
                ExprKind::As { expr, ty } => {
                    expr.visit(visitor);
                    ty.visit(visitor);
                }
                ExprKind::Tuple { elements } => {
                    for element in elements {
                        element.visit(visitor);
                    }
                }
                ExprKind::Break(b) => {
                    if let Some(val) = b {
                        val.visit(visitor);
                    }
                }
                ExprKind::Return(r) => {
                    if let Some(val) = r {
                        val.visit(visitor);
                    }
                }
            },
            VisitAction::SkipChildren => {}
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        match visitor.visit_expr(self) {
            VisitAction::Continue => match &mut self.kind {
                ExprKind::Literal(l) => l.visit_mut(visitor),
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
                ExprKind::Path(path) => {
                    for segment in &mut path.segments {
                        segment.generic_args.visit_mut(visitor);
                    }
                }
                ExprKind::Binary {
                    left,
                    operator: _,
                    right,
                } => {
                    left.visit_mut(visitor);
                    right.visit_mut(visitor);
                }
                ExprKind::Dereference { expr } => {
                    expr.visit_mut(visitor);
                }
                ExprKind::Reference { expr, .. } => {
                    expr.visit_mut(visitor);
                }
                ExprKind::Unary { operator: _, right } => {
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
                    for segment in &mut path.segments {
                        segment.generic_args.visit_mut(visitor);
                    }
                    for field in fields {
                        field.1.visit_mut(visitor);
                    }
                }
                ExprKind::Array { contents } => {
                    contents.visit_mut(visitor);
                }
                ExprKind::FunctionCall { callee, arguments } => {
                    callee.visit_mut(visitor);
                    arguments.visit_mut(visitor);
                }
                ExprKind::MemberAccess { base, .. } => {
                    base.visit_mut(visitor);
                }
                ExprKind::Index { base, index } => {
                    base.visit_mut(visitor);
                    index.visit_mut(visitor);
                }
                ExprKind::As { expr, ty } => {
                    expr.visit_mut(visitor);
                    ty.visit_mut(visitor);
                }
                ExprKind::Tuple { elements } => {
                    for element in elements {
                        element.visit_mut(visitor);
                    }
                }
                ExprKind::Break(b) => {
                    if let Some(val) = b {
                        val.visit_mut(visitor);
                    }
                }
                ExprKind::Return(r) => {
                    if let Some(val) = r {
                        val.visit_mut(visitor);
                    }
                }
            },
            VisitAction::SkipChildren => {}
        }
    }
}

impl Visitable for Literal {
    fn visit(&self, _visitor: &mut impl Visitor) {
        // Unit
    }

    fn visit_mut(&mut self, _visitor: &mut impl VisitorMut) {
        // Unit
    }
}

impl Visitable for Type {
    fn visit(&self, visitor: &mut impl Visitor) {
        match visitor.visit_type(self) {
            VisitAction::Continue => match &self.kind {
                TypeKind::Symbol(path) => {
                    for segment in &path.segments {
                        segment.generic_args.visit(visitor);
                    }
                }
                TypeKind::Pointer(ty, _) => ty.visit(visitor),
                TypeKind::Slice(ty) => ty.visit(visitor),
                TypeKind::FixedArray(ty, _) => {
                    ty.visit(visitor);
                }
                TypeKind::Function { params, ret } => {
                    params.visit(visitor);
                    ret.visit(visitor);
                }
                TypeKind::Tuple(elements) => {
                    elements.visit(visitor);
                }
                TypeKind::Infer => {
                    // Leaf
                }
                TypeKind::Never => {
                    // Leaf
                }
            },
            VisitAction::SkipChildren => {}
        }
    }

    fn visit_mut(&mut self, visitor: &mut impl VisitorMut) {
        match visitor.visit_type(self) {
            VisitAction::Continue => match &mut self.kind {
                TypeKind::Symbol(path) => {
                    for segment in &mut path.segments {
                        segment.generic_args.visit_mut(visitor);
                    }
                }
                TypeKind::Pointer(ty, _) => ty.visit_mut(visitor),
                TypeKind::Slice(ty) => ty.visit_mut(visitor),
                TypeKind::FixedArray(ty, _) => {
                    ty.visit_mut(visitor);
                }
                TypeKind::Function { params, ret } => {
                    params.visit_mut(visitor);
                    ret.visit_mut(visitor);
                }
                TypeKind::Tuple(elements) => {
                    elements.visit_mut(visitor);
                }
                TypeKind::Infer => {
                    // Leaf
                }
                TypeKind::Never => {
                    // Leaf
                }
            },
            VisitAction::SkipChildren => {}
        }
    }
}
