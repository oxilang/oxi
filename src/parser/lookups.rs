use std::sync::OnceLock;

use fxhash::FxHashMap;
use parking_lot::Once;
use thin_vec::ThinVec;

use crate::ast::{Attribute, Expr, Item};
use crate::lexer::token::TokenKind::{self, self as T};
use crate::parser::{Parser, expr::*, modifiers::Modifier, stmt::*};

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
pub enum BindingPower {
    DefaultBp,
    Comma,
    Assignment,
    Pipe,
    Logical,
    Relational,
    Bitwise,
    Shift,
    Additive,
    Multiplicative,
    Unary,
    Call,
    Member,
    Primary,
}
use BindingPower as BP;

type ItemHandler = fn(&mut Parser, ThinVec<Attribute>, ThinVec<Modifier>) -> anyhow::Result<Item>;
type NudHandler = fn(&mut Parser) -> anyhow::Result<Expr>;
type LedHandler = fn(&mut Parser, Expr, BindingPower) -> anyhow::Result<Expr>;

type ItemLookup = FxHashMap<TokenKind, ItemHandler>;
type NudLookup = FxHashMap<TokenKind, NudHandler>;
type LedLookup = FxHashMap<TokenKind, LedHandler>;
pub type BpLookup = FxHashMap<TokenKind, BindingPower>;

static INITIALIZE: Once = Once::new();
pub static BP_LU: OnceLock<BpLookup> = OnceLock::new();
pub static NUD_LU: OnceLock<NudLookup> = OnceLock::new();
pub static LED_LU: OnceLock<LedLookup> = OnceLock::new();
pub static ITEM_LU: OnceLock<ItemLookup> = OnceLock::new();

fn led(
    kind: TokenKind,
    bp: BindingPower,
    led_fn: LedHandler,
    bp_lu: &mut BpLookup,
    led_lu: &mut LedLookup,
) {
    bp_lu.insert(kind, bp);
    led_lu.insert(kind, led_fn);
}

fn nud(kind: TokenKind, nud_fn: NudHandler, nud_lu: &mut NudLookup) {
    nud_lu.insert(kind, nud_fn);
}

fn item(kind: TokenKind, item_fn: ItemHandler, bp_lu: &mut BpLookup, item_lu: &mut ItemLookup) {
    bp_lu.insert(kind, BindingPower::DefaultBp);
    item_lu.insert(kind, item_fn);
}

pub fn create_token_lookups() {
    INITIALIZE.call_once(|| {
        let mut bp_lu = BpLookup::default();
        let mut nud_lu = NudLookup::default();
        let mut led_lu = LedLookup::default();
        let mut item_lu = ItemLookup::default();

        // Pipe
        led(
            T::Pipe,
            BP::Pipe,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );

        // Assignment
        led(
            T::Equals,
            BP::Assignment,
            parse_assignment_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::PlusEquals,
            BP::Assignment,
            parse_assignment_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::MinusEquals,
            BP::Assignment,
            parse_assignment_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::SlashEquals,
            BP::Assignment,
            parse_assignment_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::PercentEquals,
            BP::Assignment,
            parse_assignment_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::StarEquals,
            BP::Assignment,
            parse_assignment_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::BitAndEquals,
            BP::Assignment,
            parse_assignment_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::BitOrEquals,
            BP::Assignment,
            parse_assignment_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::BitXorEquals,
            BP::Assignment,
            parse_assignment_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::ShiftLeftEquals,
            BP::Assignment,
            parse_assignment_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::ShiftRightEquals,
            BP::Assignment,
            parse_assignment_expr,
            &mut bp_lu,
            &mut led_lu,
        );

        // Bitwise
        led(
            T::Amp,
            BP::Bitwise,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::Bar,
            BP::Bitwise,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::Caret,
            BP::Bitwise,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );

        // Shift
        led(
            T::ShiftLeft,
            BP::Shift,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::ShiftRight,
            BP::Shift,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );

        // Logical
        led(
            T::AmpAmp,
            BP::Logical,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::BarBar,
            BP::Logical,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::DotDotExcl,
            BP::Logical,
            parse_range_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::DotDotIncl,
            BP::Logical,
            parse_range_expr,
            &mut bp_lu,
            &mut led_lu,
        );

        // Relational
        led(
            T::Less,
            BP::Relational,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::More,
            BP::Relational,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::LessEquals,
            BP::Relational,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::MoreEquals,
            BP::Relational,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::EqualsEquals,
            BP::Relational,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::NotEquals,
            BP::Relational,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::As,
            BP::Relational,
            parse_as_cast_expr,
            &mut bp_lu,
            &mut led_lu,
        );

        // Additive
        led(
            T::Plus,
            BP::Additive,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::Dash,
            BP::Additive,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );

        // Multiplicative
        led(
            T::Slash,
            BP::Multiplicative,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::Perc,
            BP::Multiplicative,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::Star,
            BP::Multiplicative,
            parse_binary_expr,
            &mut bp_lu,
            &mut led_lu,
        );

        // Literals & Symbols
        nud(T::Number, parse_primary_expr, &mut nud_lu);
        nud(T::StringLiteral, parse_primary_expr, &mut nud_lu);
        nud(T::Identifier, parse_primary_expr, &mut nud_lu);
        nud(T::True, parse_primary_expr, &mut nud_lu);
        nud(T::False, parse_primary_expr, &mut nud_lu);
        nud(T::CharLiteral, parse_primary_expr, &mut nud_lu);
        nud(T::OpenParen, parse_parenthesis_expr, &mut nud_lu);
        nud(T::OpenCurly, parse_block_expr, &mut nud_lu);
        nud(T::Dash, parse_unary_expr, &mut nud_lu);
        nud(T::At, parse_unary_expr, &mut nud_lu);
        nud(T::Bang, parse_unary_expr, &mut nud_lu);
        nud(T::Amp, parse_reference_expr, &mut nud_lu);

        // Call & Member
        led(
            T::OpenBracket,
            BP::Call,
            parse_index_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::OpenCurly,
            BP::Call,
            parse_struct_instantiation_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::OpenParen,
            BP::Call,
            parse_function_call_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::At,
            BP::Call,
            parse_dereference_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        led(
            T::Dot,
            BP::Member,
            parse_member_access_expr,
            &mut bp_lu,
            &mut led_lu,
        );
        nud(T::OpenBracket, parse_array_literal_expr, &mut nud_lu);

        nud(T::If, parse_if_expr, &mut nud_lu);
        nud(T::While, parse_while_expr, &mut nud_lu);
        nud(T::Loop, parse_loop_expr, &mut nud_lu);
        nud(T::Break, parse_break_expr, &mut nud_lu);
        nud(T::Return, parse_return_expr, &mut nud_lu);

        // Items (top-level definitions)
        item(T::Const, parse_const_item, &mut bp_lu, &mut item_lu);
        item(T::Struct, parse_struct_decl_item, &mut bp_lu, &mut item_lu);
        item(T::Type, parse_type_decl_item, &mut bp_lu, &mut item_lu);
        item(T::Trait, parse_trait_decl_item, &mut bp_lu, &mut item_lu);
        item(T::Impl, parse_impl_item, &mut bp_lu, &mut item_lu);
        item(T::Fn, parse_fn_decl_item, &mut bp_lu, &mut item_lu);
        item(T::Mod, parse_module_item, &mut bp_lu, &mut item_lu);
        item(T::Import, parse_import_item, &mut bp_lu, &mut item_lu);

        let _ = BP_LU.set(bp_lu);
        let _ = NUD_LU.set(nud_lu);
        let _ = LED_LU.set(led_lu);
        let _ = ITEM_LU.set(item_lu);
    });
}
