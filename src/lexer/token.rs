use std::fmt::Display;

use thin_vec::ThinVec;

use crate::hir::ModuleId;
use crate::span::Span;

#[derive(Debug, Clone)]
pub struct TokenStream(pub ThinVec<Token>);

#[derive(Debug, Clone, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    pub module_id: ModuleId,
    pub value: Box<str>,
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl PartialEq for Token {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

macro_rules! define_tokens {
    (
        reserved: [$( $reserved:ident ),* $(,)?],
        symbols: [$( $symbol:ident => $symbol_str:literal ),* $(,)?],
        literals: [$( $literal:ident => $literal_str:literal ),* $(,)?],
        special: [$( $special:ident => $special_str:literal ),* $(,)?]
    ) => {
        #[derive(Debug, Clone, PartialOrd, Ord, Hash, Eq, PartialEq, Copy)]
        pub enum TokenKind {
            $( $reserved ),*,
            $( $symbol ),*,
            $( $literal ),*,
            $( $special ),*
        }

        pub fn lookup_reserved(ident: &str) -> Option<TokenKind> {
            use TokenKind as T;
            static RESERVED_KEYWORDS: std::sync::OnceLock<fxhash::FxHashMap<Box<str>, TokenKind>> = std::sync::OnceLock::new();
            let lu = RESERVED_KEYWORDS.get_or_init(|| {
                let mut m = fxhash::FxHashMap::default();
                $(
                    m.insert(stringify!($reserved).to_lowercase().into_boxed_str(), T::$reserved);
                )*
                m
            });
            lu.get(ident).cloned()
        }

        impl std::fmt::Display for TokenKind {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                use TokenKind as T;
                match self {
                    $( T::$reserved => write!(f, "{}", stringify!($reserved).to_lowercase()), )*
                    $( T::$symbol => write!(f, "{}", $symbol_str), )*
                    $( T::$literal => write!(f, "{}", $literal_str), )*
                    $( T::$special => write!(f, "{}", $special_str), )*
                }
            }
        }
    };
}

define_tokens! {
    reserved: [Let, True, False, Struct, Fn, Return, Pub, Const, Mut, Extern, Trait, Macro, If, Else, While, For, Break, Continue, As, Import, Impl, Loop, Mod, Type],
    symbols: [
        // Arithmetic
        Plus => "+",
        Dash => "-",
        Star => "*",
        Slash => "/",
        Perc => "%",
        // Bitwise
        Amp => "&",
        Bar => "|",
        Caret => "^",
        ShiftLeft => "<<",
        ShiftRight => ">>",
        // Logical
        AmpAmp => "&&",
        BarBar => "||",
        // Relative
        EqualsEquals => "==",
        NotEquals => "!=",
        LessEquals => "<=",
        MoreEquals => ">=",
        Less => "<",
        More => ">",
        // Range
        DotDotExcl => "..<",
        DotDotIncl => "..=",
        // Assignment
        Equals => "=",
        PlusEquals => "+=",
        MinusEquals => "-=",
        StarEquals => "*=",
        SlashEquals => "/=",
        PercentEquals => "%=",
        BitAndEquals => "&=",
        BitOrEquals => "|=",
        BitXorEquals => "^=",
        ShiftLeftEquals => "<<=",
        ShiftRightEquals => ">>=",
        // Symbols
        Question => "?",
        Bang => "!",
        Dollar => "$",
        At => "@",
        Hash => "#",
        Pipe => "|>",
        Arrow => "->",
        // Grouping
        OpenParen => "(",
        CloseParen => ")",
        OpenBracket => "[",
        CloseBracket => "]",
        OpenCurly => "{",
        CloseCurly => "}",
        // Separators
        Dot => ".",
        Comma => ",",
        Semicolon => ";",
        Colon => ":",
        ColonColon => "::",
    ],
    literals: [Identifier => "identifier", StringLiteral => "string literal", Number => "number", CharLiteral => "character literal"],
    special: [Eof => "<eof>", Illegal => "<illegal>"]
}
