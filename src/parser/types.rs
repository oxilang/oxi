use anyhow::{Result, anyhow, bail};
use fxhash::FxHashMap;
use parking_lot::Once;
use std::sync::OnceLock;
use thin_vec::ThinVec;

use colored::Colorize;

use crate::ast::{ExprKind, Mutability, NodeId, Type, TypeKind};
use crate::diag_params;
use crate::errors::builders;
use crate::lexer::token::TokenKind::{self, self as T};
use crate::parser::expr::parse_expr;
use crate::parser::lookups::{
    BindingPower::{self, self as BP},
    BpLookup,
};
use crate::parser::utils::{parse_generic_args, parse_path};
use crate::parser::{Parser, diag};
use crate::span::Span;

type TypeNudHandler = fn(&mut Parser) -> Result<Type>;
type TypeLedHandler = fn(&mut Parser, Type, BindingPower) -> Result<Type>;

type TypeNudLookup = FxHashMap<TokenKind, TypeNudHandler>;
type TypeLedLookup = FxHashMap<TokenKind, TypeLedHandler>;

static INITIALIZE: Once = Once::new();
pub static TYPE_BP_LU: OnceLock<BpLookup> = OnceLock::new();
pub static TYPE_NUD_LU: OnceLock<TypeNudLookup> = OnceLock::new();
pub static TYPE_LED_LU: OnceLock<TypeLedLookup> = OnceLock::new();

#[allow(dead_code)]
fn type_led(
    kind: TokenKind,
    bp: BindingPower,
    led_fn: TypeLedHandler,
    bp_lu: &mut BpLookup,
    led_lu: &mut TypeLedLookup,
) {
    bp_lu.insert(kind, bp);
    led_lu.insert(kind, led_fn);
}

fn type_nud(kind: TokenKind, nud_fn: TypeNudHandler, nud_lu: &mut TypeNudLookup) {
    nud_lu.insert(kind, nud_fn);
}

pub fn create_token_type_lookups() {
    INITIALIZE.call_once(|| {
        let bp_lu = BpLookup::default();
        let mut nud_lu = TypeNudLookup::default();
        let led_lu = TypeLedLookup::default();

        type_nud(T::Identifier, parse_symbol_type, &mut nud_lu);
        type_nud(T::OpenBracket, parse_array_type, &mut nud_lu);
        type_nud(T::OpenParen, parse_parenthesis_type, &mut nud_lu);
        type_nud(T::Amp, parse_pointer_type, &mut nud_lu);
        type_nud(T::Less, parse_projection_type, &mut nud_lu);

        let _ = TYPE_BP_LU.set(bp_lu);
        let _ = TYPE_NUD_LU.set(nud_lu);
        let _ = TYPE_LED_LU.set(led_lu);
    });
}

fn parse_symbol_type(parser: &mut Parser) -> Result<Type> {
    let path = parse_path(parser)?;
    let span = path.span;

    Ok(Type {
        kind: TypeKind::Symbol(path),
        node_id: NodeId::default(),
        span,
    })
}

fn parse_pointer_type(parser: &mut Parser) -> Result<Type> {
    let start_token = parser.expect(T::Amp)?;

    let mut is_mutable = false;
    if parser.current_token().kind == TokenKind::Mut {
        parser.advance();
        is_mutable = true;
    }

    let underlying = parse_type(parser, BindingPower::DefaultBp)?;
    let end_span = underlying.span;

    let mutability = if is_mutable {
        Mutability::Mutable
    } else {
        Mutability::Constant
    };

    Ok(Type {
        kind: TypeKind::Pointer(Box::new(underlying), mutability),
        span: Span::new(start_token.span.start(), end_span.end()),
        node_id: NodeId::default(),
    })
}

fn parse_array_type(parser: &mut Parser) -> Result<Type> {
    let start_token = parser.advance();

    let underlying = parse_type(parser, BP::DefaultBp)?;

    match parser.current_token().kind {
        T::Semicolon => {
            parser.advance();
            let length = parser.expect(TokenKind::Number)?;
            let length = length.value.parse::<usize>()?;
            let end_token = parser.expect(TokenKind::CloseBracket)?;
            let span = Span::new(start_token.span.start(), end_token.span.end());

            Ok(Type {
                kind: TypeKind::FixedArray(Box::new(underlying), length),
                node_id: NodeId::default(),
                span,
            })
        }
        T::CloseBracket => {
            let end_token = parser.advance();
            let span = Span::new(start_token.span.start(), end_token.span.end());

            Ok(Type {
                kind: TypeKind::Slice(Box::new(underlying)),
                node_id: NodeId::default(),
                span,
            })
        }
        _ => Err(anyhow!(
            format!(
                "Syntax error: Expected ';' or ']' in array type, got {:?}",
                parser.current_token()
            )
            .red()
            .bold()
        )),
    }
}

fn parse_parenthesis_type(parser: &mut Parser) -> Result<Type> {
    let start_token = parser.advance();

    let mut types = ThinVec::new();

    while parser.current_token().kind != TokenKind::CloseParen {
        types.push(parse_type(parser, BindingPower::DefaultBp)?);

        if parser.current_token().kind == TokenKind::Comma {
            parser.advance();
        } else if parser.current_token().kind != TokenKind::CloseParen {
            bail!("Expected comma or closing parenthesis in type".red().bold());
        }
    }
    let close_token = parser.expect(TokenKind::CloseParen)?;

    if parser.current_token().kind == TokenKind::Arrow {
        parser.expect(TokenKind::Arrow)?;
        let return_type = parse_type(parser, BindingPower::DefaultBp)?;
        let end_span = return_type.span;

        Ok(Type {
            kind: TypeKind::Function {
                params: types,
                ret: Box::new(return_type),
            },
            span: Span::new(start_token.span.start(), end_span.end()),
            node_id: NodeId::default(),
        })
    } else {
        Ok(Type {
            kind: TypeKind::Tuple(types),
            span: Span::new(start_token.span.start(), close_token.span.end()),
            node_id: NodeId::default(),
        })
    }
}

fn parse_projection_type(parser: &mut Parser) -> Result<Type> {
    let start_token = parser.advance();

    let base = match parse_expr(parser, BindingPower::Primary)?.kind {
        ExprKind::Path(path) => path,
        _ => bail!("Expected path for projection base"),
    };
    parser.expect(T::As)?;
    let trait_ = match parse_expr(parser, BindingPower::Primary)?.kind {
        ExprKind::Path(path) => path,
        _ => bail!("Expected path for projection trait"),
    };
    parser.expect(T::More)?;
    parser.expect(T::ColonColon)?;
    let assoc = parser.expect_identifier()?;

    let mut span_end = assoc.span.end();
    let generic_args = if parser.current_token().kind == T::ColonColon {
        parser.expect(T::ColonColon)?;
        let (generic_args, end_span) = parse_generic_args(parser)?;
        span_end = end_span.end();
        Some(generic_args)
    } else {
        None
    };

    Ok(Type {
        kind: TypeKind::Projection {
            base: (base, NodeId::default()),
            trait_: (trait_, NodeId::default()),
            assoc,
            generic_args,
        },
        node_id: NodeId::default(),
        span: Span::new(start_token.span.start(), span_end),
    })
}

pub fn parse_type(parser: &mut Parser, bp: BindingPower) -> Result<Type> {
    let token = parser.current_token();

    let bp_lu = TYPE_BP_LU.get().expect("Type lookups not initialized");
    let nud_lu = TYPE_NUD_LU.get().expect("Type lookups not initialized");
    let led_lu = TYPE_LED_LU.get().expect("Type lookups not initialized");

    let nud_fn = match nud_lu.get(&token.kind).cloned() {
        Some(nud_fn) => nud_fn,
        None => {
            builders::emit_at(
                parser.ctx,
                parser.current_token().span,
                token.module_id,
                diag::UnexpectedToken,
                diag_params! { actual = token.kind },
            );
            return Err(anyhow!("Unexpected token"));
        }
    };

    let mut left = nud_fn(parser)?;

    loop {
        let current_bp = bp_lu
            .get(&parser.current_token().kind)
            .unwrap_or(&BindingPower::DefaultBp);

        if *current_bp <= bp {
            break;
        }

        let token = parser.current_token();
        let led_fn = match led_lu.get(&token.kind).cloned() {
            Some(led_fn) => led_fn,
            None => {
                builders::emit_at(
                    parser.ctx,
                    parser.current_token().span,
                    token.module_id,
                    diag::UnexpectedToken,
                    diag_params! { actual = token.kind },
                );
                return Err(anyhow!("Unexpected token"));
            }
        };

        left = led_fn(parser, left, *current_bp)?;
    }

    Ok(left)
}
