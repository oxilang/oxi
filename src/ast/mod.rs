#[cfg(test)]
mod tests;

pub mod validate;
pub mod visit;

mod node_id;
pub use node_id::*;

use std::path::PathBuf;

use anyhow::bail;
use thin_vec::{ThinVec, thin_vec};

use crate::context::Ctx;
use crate::hir::path_to_mod;
use crate::interner::{Interner, Symbol};
use crate::lexer::token::{Token, TokenKind};
use crate::span::Span;

#[derive(Debug, Clone)]
pub struct Ast {
    pub name: Box<str>,
    pub items: ThinVec<Item>,
}

impl Ast {
    pub fn new(items: ThinVec<Item>, path: &PathBuf) -> Self {
        Self {
            name: path_to_mod(path).into(),
            items,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Item {
    pub kind: ItemKind,
    pub span: Span,
    pub attributes: ThinVec<Attribute>,
    pub node_id: NodeId,
    /// Visibility modifier for this item.
    ///
    /// For most item kinds (static, struct, trait, function, import), this is the visibility
    /// as written in the source code (defaults to private if not specified).
    ///
    /// For [`ItemKind::Impl`], this field is a placeholder value since impl blocks do not have
    /// visibility modifiers in the source grammar. The value is always set to [`Visibility::Private`]
    /// for uniformity across the AST. Code that processes items should ignore this field for impls
    /// and instead check the visibility of individual associated items within the impl block.
    pub visibility: Visibility,
}

#[derive(Debug, Clone)]
pub enum ItemKind {
    Const {
        name: Ident,
        value: Expr,
        ty: Type,
    },
    Struct {
        name: Ident,
        fields: ThinVec<(Ident, Type, Visibility)>,
        items: ThinVec<AssocItem>,
        generic_params: Option<GenericParams>,
    },
    Type {
        name: Ident,
        generic_params: Option<GenericParams>,
        type_: Type,
    },
    Trait {
        name: Ident,
        items: ThinVec<AssocItem>,
        generic_params: Option<GenericParams>,
    },
    Impl {
        self_ty: (Path, NodeId),
        trait_: (Path, NodeId),
        items: ThinVec<AssocItem>,
    },
    Fn(Fn),
    Module {
        name: Ident,
        body: Option<ThinVec<Item>>,
    },
    Import(ImportTree),
}

#[derive(Debug, Clone)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
    pub node_id: NodeId,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
    /// Expression without a trailing semicolon (returns value)
    Expr(Expr),
    /// Expression with a trailing semicolon
    Semi(Expr),
    Let {
        name: Ident,
        ty: Type,
        value: Option<Expr>,
        mutability: Mutability,
    },
}

#[derive(Debug, Clone)]
pub struct AssocItem {
    pub kind: AssocItemKind,
    pub visibility: Visibility,
    pub span: Span,
    pub node_id: NodeId,
}

#[derive(Debug, Clone)]
pub enum AssocItemKind {
    Fn(Fn),
    Type { name: Ident, type_: Option<Type> },
}

#[derive(Debug, Clone)]
pub struct Fn {
    pub name: Ident,
    pub parameters: ThinVec<(Ident, Type, NodeId)>,
    pub generic_params: Option<GenericParams>,
    pub body: Option<Block>,
    pub return_type: Type,
    pub is_extern: bool,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    pub node_id: NodeId,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    /// A path expression, e.g. `foo::bar::baz`.
    Path(Path),

    /// A literal expression, e.g. `42`, `21.5', `true`, `'c'`, "hello".
    Literal(Literal),
    /// An array literal, e.g. `[1, 2, 3]`.
    Array { contents: ThinVec<Expr> },
    /// A tuple literal, e.g. `(1, 2, 3)`.
    Tuple { elements: ThinVec<Expr> },

    /// A binary expression, e.g. `1 + 2`.
    Binary {
        left: Box<Expr>,
        operator: Token,
        right: Box<Expr>,
    },
    /// A unary expression, e.g. `!true`, `-42`.
    Unary { operator: Token, right: Box<Expr> },
    /// A range expression, e.g. `1..<2`, `1..=2`.
    Range {
        start: Option<Box<Expr>>,
        end: Option<Box<Expr>>,
        kind: RangeKind,
    },

    /// A reference expression, e.g. `&foo`, `&mut bar`.
    Reference {
        expr: Box<Expr>,
        mutability: Mutability,
    },
    /// A dereference expression, e.g. `foo@`.
    Dereference { expr: Box<Expr> },

    /// A struct instantiation expression, e.g. `Foo { x: 1, y: 2 }`.
    StructInstantiation {
        path: Path,
        fields: ThinVec<(Ident, Expr)>,
    },

    /// A member access expression, e.g. `foo.bar`.
    MemberAccess { base: Box<Expr>, member: Ident },
    /// Indexing into an array or tuple, e.g. `foo[1]`, `foo[1..2]`.
    Index { base: Box<Expr>, index: Box<Expr> },

    /// An assignment expression, e.g. `foo = bar`, `foo += 1`.
    Assignment {
        assignee: Box<Expr>,
        operator: Token,
        value: Box<Expr>,
    },

    /// A function call expression, e.g. `foo(1, 2, 3)`.
    FunctionCall {
        callee: Box<Expr>,
        arguments: ThinVec<Expr>,
    },

    /// A cast expression, e.g. `foo as u32`.
    As { expr: Box<Expr>, ty: Type },

    /// A block expression, e.g. `{ ... }`.
    Block(Block),

    /// An `if` expression, e.g. `if foo { ... } else { ... }`.
    If {
        condition: Box<Expr>,
        then_branch: Block,
        else_branch: Option<Box<Expr>>,
    },
    /// A `while` expression, e.g. `while foo { ... }`.
    While { condition: Box<Expr>, body: Block },
    /// A `loop` expression, e.g. `loop { ... }`.
    Loop(Block),

    /// A `break` expression, e.g. `break foo`.
    Break(Option<Box<Expr>>),
    /// A `return` expression, e.g. `return bar`.
    Return(Option<Box<Expr>>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RangeKind {
    Inclusive,
    Exclusive,
}

#[derive(Debug, Clone, Copy)]
pub enum Literal {
    Integer(i64),
    Float(f64),
    String(Symbol),
    Char(char),
    Bool(bool),
}

#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    pub node_id: NodeId,
    pub span: Span,
}

impl Type {
    pub fn display(&self, ctx: &Ctx) -> String {
        match &self.kind {
            TypeKind::Symbol(path) => path.display(ctx),
            TypeKind::Pointer(ty, mutability) => {
                format!(
                    "&{} {}",
                    if *mutability == Mutability::Mutable {
                        "mut"
                    } else {
                        ""
                    },
                    ty.display(ctx)
                )
            }
            TypeKind::Slice(ty) => format!("[{}]", ty.display(ctx)),
            TypeKind::FixedArray(ty, size) => format!("[{}; {}]", ty.display(ctx), size),
            TypeKind::Function { params, ret } => format!(
                "({}) -> {}",
                params
                    .iter()
                    .map(|t| t.display(ctx))
                    .collect::<Vec<_>>()
                    .join(", "),
                ret.display(ctx)
            ),
            TypeKind::Tuple(types) => format!(
                "({})",
                types
                    .iter()
                    .map(|t| t.display(ctx))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            TypeKind::Projection {
                base,
                trait_,
                assoc,
                generic_args,
            } => format!(
                "<{} as {}>::{}{}",
                base.0.display(ctx),
                trait_.0.display(ctx),
                ctx.interner.lookup(assoc.value),
                if let Some(args) = generic_args {
                    format!(
                        "::<{}>",
                        args.iter()
                            .map(|t| t.display(ctx))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                } else {
                    String::new()
                }
            ),
            TypeKind::Infer => "_".to_string(),
            TypeKind::Never => "!".to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum TypeKind {
    Symbol(Path),
    Pointer(Box<Type>, Mutability),
    Slice(Box<Type>),
    FixedArray(Box<Type>, usize),
    Function {
        params: ThinVec<Type>,
        ret: Box<Type>,
    },
    Tuple(ThinVec<Type>),
    Projection {
        base: (Path, NodeId),
        trait_: (Path, NodeId),
        assoc: Ident,
        generic_args: Option<ThinVec<Type>>,
    },
    Infer,
    Never,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ident {
    pub value: Symbol,
    pub span: Span,
}

impl Ident {
    pub fn from_token(ctx: &mut Ctx, token: Token) -> Result<Self, anyhow::Error> {
        if token.kind != TokenKind::Identifier {
            bail!("Expected identifier token, but got {} instead", token.kind);
        }
        Ok(Self {
            value: ctx.interner.intern(token.value),
            span: token.span,
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Private,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Mutability {
    Constant,
    Mutable,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: ThinVec<Stmt>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Path {
    pub span: Span,
    pub segments: ThinVec<PathSegment>,
}

impl Path {
    pub fn from_ident(id: Ident) -> Self {
        Path {
            span: id.span,
            segments: thin_vec![PathSegment {
                ident: id,
                span: id.span,
                generic_args: None
            }],
        }
    }

    pub fn last(&self) -> Option<&PathSegment> {
        self.segments.last()
    }

    pub fn is_single(&self) -> bool {
        self.segments.len() == 1
    }

    pub fn display(&self, ctx: &Ctx) -> String {
        path_segments_to_string(&self.segments, ctx)
    }
}

#[derive(Debug, Clone)]
pub struct PathSegment {
    pub ident: Ident,
    pub generic_args: Option<ThinVec<Type>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct GenericParams {
    pub params: ThinVec<GenericParam>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct GenericParam {
    pub name: Ident,
    pub node_id: NodeId,
    pub default: Option<Type>,
}

pub fn path_segments_to_string(segments: &[PathSegment], ctx: &Ctx) -> String {
    segments
        .iter()
        .map(|s| {
            if let Some(args) = &s.generic_args {
                format!(
                    "{}::<{}>",
                    ctx.interner.lookup(s.ident.value),
                    args.iter()
                        .map(|t| t.display(ctx))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            } else {
                ctx.interner.lookup(s.ident.value).to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("::")
}

pub fn idents_to_string(idents: &[Ident], interner: &Interner) -> String {
    idents
        .iter()
        .map(|s| interner.lookup(s.value))
        .collect::<Vec<_>>()
        .join("::")
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attribute {
    pub name: Ident,
    pub arguments: Option<ThinVec<Box<str>>>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum ImportTreeKind {
    /// `import prefix` or `import prefix as rename`
    ///
    /// The inner value represents the rename if it exists.
    Simple(Option<Ident>),
    /// `import prefix::{...}`
    ///
    /// The span represents the braces of the nested group and all elements within:
    ///
    /// ```text
    /// import foo::{bar, baz};
    ///             ^^^^^^^^^^
    /// ```
    Nested {
        items: ThinVec<ImportTree>,
        span: Span,
    },
    /// `import prefix::*`
    Glob,
}

#[derive(Debug, Clone)]
pub struct ImportTree {
    pub prefix: Path,
    pub kind: ImportTreeKind,
    pub span: Span,
}

impl ImportTree {
    pub fn ident(&self) -> Option<Ident> {
        match &self.kind {
            ImportTreeKind::Simple(Some(rename)) => Some(*rename),
            ImportTreeKind::Simple(None) => self.prefix.segments.last().map(|seg| seg.ident),
            _ => None,
        }
    }
}
