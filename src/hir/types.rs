use std::fmt::{self, Display, Formatter};

use thin_vec::ThinVec;

use crate::ast::{Ident, Literal, Mutability, Visibility};
use crate::context::Ctx;
use crate::hir::owner::HirId;
use crate::hir::{BodyId, DefId, OwnerId, PrimTy};
use crate::interner::Symbol;
use crate::lexer::token::{Token, TokenKind};
use crate::resolve::Res;
use crate::span::Span;

#[derive(Debug, Clone)]
pub enum OwnerNode<'a> {
    Item(&'a Item),
    AssocItem(&'a AssocItem),
    Crate,
}

impl<'a> OwnerNode<'a> {
    pub fn from_node(node: &'a Node) -> Option<Self> {
        match node {
            Node::Item(item) => Some(OwnerNode::Item(item)),
            Node::AssocItem(item) => Some(OwnerNode::AssocItem(item)),
            Node::Crate => Some(OwnerNode::Crate),
            _ => None,
        }
    }

    pub fn span(&self) -> Span {
        match self {
            OwnerNode::Item(item) => item.span,
            OwnerNode::AssocItem(item) => item.span,
            OwnerNode::Crate => Span::new(0, 0),
        }
    }

    pub fn hir_id(&self) -> HirId {
        match self {
            OwnerNode::Item(item) => item.hir_id,
            OwnerNode::AssocItem(item) => item.hir_id,
            OwnerNode::Crate => HirId::INVALID,
        }
    }

    pub fn owner_id(&self) -> OwnerId {
        match self {
            OwnerNode::Item(item) => item.owner_id,
            OwnerNode::AssocItem(item) => item.owner_id,
            OwnerNode::Crate => OwnerId(0),
        }
    }

    pub fn def_id(&self) -> DefId {
        DefId(self.owner_id().0)
    }
}

#[derive(Debug, Clone)]
pub enum Node {
    /// A top-level item
    Item(Box<Item>),
    /// An associated item
    AssocItem(Box<AssocItem>),
    /// An expression
    Expr(Box<Expr>),
    /// A statement
    Stmt(Box<Stmt>),
    /// A type
    Ty(Box<Ty>),
    /// A block expression
    Block(Box<Block>),
    /// A function parameter
    Param(Box<Param>),
    /// A local variable binding
    Local(Box<Local>),
    /// A generic type parameter
    GenericParam(Box<GenericParam>),
    /// The crate root
    Crate,
    Err(Span),
}

impl Node {
    pub fn span(&self) -> Option<Span> {
        match self {
            Node::Item(item) => Some(item.span),
            Node::AssocItem(item) => Some(item.span),
            Node::Expr(expr) => Some(expr.span),
            Node::Stmt(stmt) => Some(stmt.span),
            Node::Ty(ty) => Some(ty.span),
            Node::Block(block) => Some(block.span),
            Node::Param(param) => Some(param.span),
            Node::Local(local) => Some(local.span),
            Node::GenericParam(param) => Some(param.span),
            Node::Crate => None,
            Node::Err(span) => Some(*span),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Item {
    pub hir_id: HirId,
    pub owner_id: OwnerId,
    pub kind: ItemKind,
    pub span: Span,
    pub visibility: Visibility,
}

impl Item {
    pub fn hir_id(&self) -> HirId {
        self.hir_id
    }

    pub fn item_id(&self) -> ItemId {
        ItemId {
            owner_id: self.owner_id,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ItemId {
    pub owner_id: OwnerId,
}

impl ItemId {
    pub fn hir_id(&self) -> HirId {
        HirId::make_owner(self.owner_id.to_def_id())
    }
}

#[derive(Debug, Clone)]
pub enum ItemKind {
    Fn(Fn),
    Struct {
        name: Symbol,
        fields: ThinVec<StructField>,
        items: ThinVec<DefId>,
        generic_params: Option<ThinVec<GenericParam>>,
    },
    TypeAlias {
        name: Symbol,
        type_: Ty,
        generic_params: Option<ThinVec<GenericParam>>,
    },
    Trait {
        name: Symbol,
        items: ThinVec<DefId>,
        generic_params: Option<ThinVec<GenericParam>>,
    },
    Impl {
        self_ty: Path,
        trait_ty: Path,
        items: ThinVec<DefId>,
    },
    Const {
        name: Symbol,
        ty: Ty,
        body_id: Option<BodyId>,
    },
}

#[derive(Debug, Clone)]
pub struct AssocItem {
    pub hir_id: HirId,
    pub owner_id: OwnerId,
    pub kind: AssocItemKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum AssocItemKind {
    Fn(Fn),
    // TODO: Maybe add generic params to type?
    Type { name: Symbol, type_: Option<Ty> },
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub name: Symbol,
    pub ty: Ty,
    pub visibility: Visibility,
}

#[derive(Debug, Clone)]
pub struct FnDecl {
    pub params: ThinVec<Param>,
    pub ret: Ty,
}

#[derive(Debug, Clone)]
pub struct FnSig {
    pub is_extern: bool,
}

#[derive(Debug, Clone)]
pub struct Fn {
    pub sig: FnSig,
    pub decl: FnDecl,
    pub generic_params: Option<ThinVec<GenericParam>>,
    pub body_id: Option<BodyId>,
}

#[derive(Debug, Clone)]
pub struct Param {
    pub hir_id: HirId,
    pub name: Symbol,
    pub ty: Ty,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct GenericParam {
    pub hir_id: HirId,
    pub name: Symbol,
    pub span: Span,
    pub default: Option<Ty>,
}

#[derive(Debug, Clone)]
pub struct Body {
    pub value: Expr,
}

#[derive(Debug, Clone)]
pub struct Local {
    pub hir_id: HirId,
    pub name: Symbol,
    pub ty: Ty,
    pub init: Option<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub hir_id: HirId,
    pub kind: ExprKind,
    pub span: Span,
}

impl Expr {
    pub fn into_box(self) -> Box<Self> {
        Box::new(self)
    }
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    /// A literal value
    Literal(Literal),
    /// A path
    Path(QPath),
    /// Binary operation: left op right
    Binary {
        left: Box<Expr>,
        op: BinOp,
        right: Box<Expr>,
    },
    /// Function call: callee(args...)
    Call {
        callee: Box<Expr>,
        args: ThinVec<Expr>,
    },
    /// Method call: receiver.method(args...)
    MethodCall {
        receiver: Box<Expr>,
        method: Symbol,
        args: ThinVec<Expr>,
        def_id: DefId,
    },
    /// Field access: base.field
    Field {
        base: Box<Expr>,
        field: Symbol,
        index: usize,
    },
    /// Struct literal: Struct { field: value, ... }
    StructInit {
        def: DefId,
        generic_args: Option<ThinVec<Ty>>,
        fields: ThinVec<(Ident, Expr)>,
    },
    /// Array literal: [value1, value2, ... ]
    ArrayInit {
        contents: ThinVec<Expr>,
    },
    /// Tuple literal: (value1, value2, ...)
    TupleInit(ThinVec<Expr>),
    /// Block: { stmts }
    Block(Block),
    /// If expression: if cond { then } else { else }
    If {
        cond: Box<Expr>,
        then_branch: Block,
        else_branch: Option<Box<Expr>>,
    },
    /// Infinite loop: loop { body }
    Loop(Block),
    /// Break from a block
    Break(Option<Box<Expr>>),
    /// Return from a function
    Return(Option<Box<Expr>>),
    /// Assignment: target = value
    Assign {
        target: Box<Expr>,
        value: Box<Expr>,
    },
    /// Unary operation: op right
    Unary {
        op: UnOp,
        right: Box<Expr>,
    },
    /// Dereference expression: expr@
    Dereference {
        expr: Box<Expr>,
    },
    /// Reference expression: &expr
    Reference {
        expr: Box<Expr>,
        mutability: Mutability,
    },
    /// Member access expression (unresolved)
    MemberAccess {
        base: Box<Expr>,
        member: Symbol,
    },
    /// Index expression: base[index]
    Index {
        base: Box<Expr>,
        index: Box<Expr>,
    },
    /// Type cast: expr as Type
    As {
        expr: Box<Expr>,
        ty: Ty,
    },
    Error,
}

#[derive(Debug, Clone)]
pub struct Stmt {
    pub hir_id: HirId,
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub enum StmtKind {
    /// Expression without trailing semicolon (tail position)
    Expr(Expr),
    /// Expression with trailing semicolon
    Semi(Expr),
    /// let-binding
    Let {
        name: Symbol,
        ty: Ty,
        init: Option<Expr>,
        local: HirId,
        mutability: Mutability,
    },
}

#[derive(Debug, Clone)]
pub struct Block {
    pub hir_id: HirId,
    pub stmts: ThinVec<Stmt>,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct Ty {
    pub hir_id: HirId,
    pub kind: TyKind,
    pub span: Span,
}

impl Ty {
    pub fn display(&self, ctx: &Ctx) -> String {
        match &self.kind {
            TyKind::Error => String::new(),
            TyKind::PrimTy(prim_ty) => prim_ty.name_str().to_string(),
            TyKind::Path(path) => path.display(ctx),
            TyKind::GenericParam(_, name) => ctx.interner.lookup(*name).to_string(),
            TyKind::Ptr(ty, mutability) => {
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
            TyKind::Slice(ty) => format!("[{}]", ty.display(ctx)),
            TyKind::Array(ty, size) => format!("[{}; {}]", ty.display(ctx), size),
            TyKind::Fn { params, ret } => format!(
                "({}) -> {}",
                params
                    .iter()
                    .map(|t| t.display(ctx))
                    .collect::<Vec<_>>()
                    .join(", "),
                ret.display(ctx)
            ),
            TyKind::Tuple(types) => format!(
                "({})",
                types
                    .iter()
                    .map(|t| t.display(ctx))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            TyKind::Infer => "_".to_string(),
            TyKind::Never => "!".to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum TyKind {
    Error,
    PrimTy(PrimTy),
    /// A named type
    Path(QPath),
    /// A generic type parameter
    GenericParam(HirId, Symbol),
    /// Pointer type: &T or &mut T
    Ptr(Box<Ty>, Mutability),
    /// Slice type: [T]
    Slice(Box<Ty>),
    /// Fixed-size array: [T; N]
    Array(Box<Ty>, usize),
    /// Function pointer type: (T, T) -> T
    Fn {
        params: ThinVec<Ty>,
        ret: Box<Ty>,
    },
    /// Tuple type: (T, T, ...)
    Tuple(ThinVec<Ty>),
    /// Inferred type
    Infer,
    /// Never type: !
    Never,
}

#[derive(Debug, Clone)]
pub struct Path {
    pub res: Res<HirId>,
    pub segments: ThinVec<PathSegment>,
    pub span: Span,
}

impl Path {
    pub fn display(&self, ctx: &Ctx) -> String {
        self.segments
            .iter()
            .map(|s| s.display(ctx))
            .collect::<Vec<_>>()
            .join("::")
    }
}

#[derive(Debug, Clone)]
pub struct PathSegment {
    pub ident: Ident,
    pub generic_args: Option<ThinVec<Ty>>,
}

impl PathSegment {
    pub fn display(&self, ctx: &Ctx) -> String {
        let ident = ctx.interner.lookup(self.ident.value);
        if let Some(args) = &self.generic_args {
            let args_str = args
                .iter()
                .map(|t| t.display(ctx))
                .collect::<Vec<_>>()
                .join(", ");
            format!("{}::<{}>", ident, args_str)
        } else {
            ident.to_string()
        }
    }
}

/// A path that may still have associated-item suffixes to resolve during type checking.
#[derive(Debug, Clone)]
pub enum QPath {
    /// Fully resolved path, optionally with a Self type for `<Self as Trait>` qselfs
    Resolved(Option<Box<Ty>>, Path),
    /// Type-relative path: `T::Assoc`
    TypeRelative {
        qself: Box<QPath>,
        segment: PathSegment,
    },
}

impl QPath {
    pub fn display(&self, ctx: &Ctx) -> String {
        match self {
            QPath::Resolved(self_ty, path) => {
                if let Some(self_ty) = self_ty {
                    format!("<{} as {}>", self_ty.display(ctx), path.display(ctx))
                } else {
                    path.display(ctx)
                }
            }
            QPath::TypeRelative { qself, segment } => {
                format!("{}::{}", qself.display(ctx), segment.display(ctx))
            }
        }
    }
}

pub trait FromToken<T> {
    fn from_token(tk: &Token) -> Option<T>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Shl,
    Shr,
    BitAnd,
    BitOr,
    BitXor,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

impl FromToken<BinOp> for BinOp {
    fn from_token(tk: &Token) -> Option<Self> {
        Some(match tk.kind {
            TokenKind::Plus => BinOp::Add,
            TokenKind::Dash => BinOp::Sub,
            TokenKind::Star => BinOp::Mul,
            TokenKind::Slash => BinOp::Div,
            TokenKind::Perc => BinOp::Rem,
            TokenKind::ShiftLeft => BinOp::Shl,
            TokenKind::ShiftRight => BinOp::Shr,
            TokenKind::Amp => BinOp::BitAnd,
            TokenKind::Bar => BinOp::BitOr,
            TokenKind::Caret => BinOp::BitXor,
            TokenKind::EqualsEquals => BinOp::Eq,
            TokenKind::NotEquals => BinOp::Ne,
            TokenKind::Less => BinOp::Lt,
            TokenKind::LessEquals => BinOp::Le,
            TokenKind::More => BinOp::Gt,
            TokenKind::MoreEquals => BinOp::Ge,
            TokenKind::AmpAmp => BinOp::And,
            TokenKind::BarBar => BinOp::Or,
            TokenKind::DotDotExcl => todo!("..< not yet implemented"),
            TokenKind::DotDotIncl => todo!("..= not yet implemented"),
            _ => return None,
        })
    }
}

impl Display for BinOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Eq => write!(f, "=="),
            BinOp::Ne => write!(f, "!="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Le => write!(f, "<="),
            BinOp::Gt => write!(f, ">"),
            BinOp::Ge => write!(f, ">="),
            BinOp::And => write!(f, "&&"),
            BinOp::Or => write!(f, "||"),
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Rem => write!(f, "%"),
            BinOp::Shl => write!(f, "<<"),
            BinOp::Shr => write!(f, ">>"),
            BinOp::BitAnd => write!(f, "&"),
            BinOp::BitOr => write!(f, "|"),
            BinOp::BitXor => write!(f, "^"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
}

impl FromToken<UnOp> for UnOp {
    fn from_token(tk: &Token) -> Option<Self> {
        Some(match tk.kind {
            TokenKind::Dash => Self::Neg,
            TokenKind::Bang => Self::Not,
            _ => return None,
        })
    }
}

impl Display for UnOp {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            UnOp::Not => write!(f, "!"),
            UnOp::Neg => write!(f, "-"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssOp {
    Ass,
    AssSub,
    AssAdd,
    AssMul,
    AssDiv,
    AssRem,
    AssBitAnd,
    AssBitOr,
    AssBitXor,
    AssShl,
    AssShr,
}

impl FromToken<AssOp> for AssOp {
    fn from_token(tk: &Token) -> Option<Self> {
        Some(match tk.kind {
            TokenKind::Equals => Self::Ass,
            TokenKind::MinusEquals => Self::AssSub,
            TokenKind::PlusEquals => Self::AssAdd,
            TokenKind::StarEquals => Self::AssMul,
            TokenKind::SlashEquals => Self::AssDiv,
            TokenKind::PercentEquals => Self::AssRem,
            TokenKind::BitAndEquals => Self::AssBitAnd,
            TokenKind::BitOrEquals => Self::AssBitOr,
            TokenKind::BitXorEquals => Self::AssBitXor,
            TokenKind::ShiftLeftEquals => Self::AssShl,
            TokenKind::ShiftRightEquals => Self::AssShr,
            _ => return None,
        })
    }
}
