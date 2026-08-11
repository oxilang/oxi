use anyhow::Result;
use thin_vec::ThinVec;

use crate::{
    ast::{Ident, Path, PathSegment, Stmt, Type},
    context::Ctx,
    diag_params,
    errors::builders,
    lexer::token::{Token, TokenKind},
    parser::{Parser, diag, lookups::BindingPower, stmt::parse_stmt, types::parse_type},
    span::Span,
};

pub fn unexpected_token(ctx: &mut Ctx, token: Token, expected: impl std::fmt::Display) -> ! {
    builders::emit_at(
        ctx,
        token.span,
        token.module_id,
        diag::ExpectedToken,
        diag_params! { expected = expected, actual = token.kind },
    );
    unreachable!()
}

pub fn parse_path(parser: &mut Parser) -> Result<Path> {
    let start = parser.current_token().span;
    let mut segments = ThinVec::new();

    let segment = parse_path_segment(parser)?;
    let mut last = segment.span.end();
    segments.push(segment);

    while parser.current_token().kind == TokenKind::ColonColon
        && matches!(parser.peek().kind, TokenKind::Identifier | TokenKind::More)
    {
        parser.advance();
        let segment = parse_path_segment(parser)?;
        last = segment.span.end();
        segments.push(segment);
    }

    Ok(Path {
        segments,
        span: Span::new(start.start(), last),
    })
}

fn parse_path_segment(parser: &mut Parser) -> Result<PathSegment> {
    let ident = parser.expect_identifier()?;
    let span_start = ident.span.start();
    let mut span_end = ident.span.end();
    let generic_args = if parser.peek().kind == TokenKind::Less {
        parser.expect(TokenKind::ColonColon)?;
        let (args, end_span) = parse_generic_args(parser)?;
        span_end = end_span.end();
        Some(args)
    } else {
        None
    };
    let span = Span::new(span_start, span_end);
    Ok(PathSegment {
        ident,
        generic_args,
        span,
    })
}

pub fn parse_generic_args(parser: &mut Parser) -> Result<(ThinVec<Type>, Span)> {
    parser.expect(TokenKind::Less)?;
    let mut args = ThinVec::new();
    while parser.current_token().kind != TokenKind::More {
        args.push(parse_type(parser, BindingPower::DefaultBp)?);
        if parser.current_token().kind == TokenKind::Comma {
            parser.advance();
        } else if parser.current_token().kind != TokenKind::More {
            unexpected_token(parser.ctx, parser.current_token(), "',' or '>'");
        }
    }
    let end_span = parser.expect(TokenKind::More)?.span;
    Ok((args, end_span))
}

pub fn parse_rename(parser: &mut Parser) -> Result<Option<Ident>> {
    if parser.current_token().kind == TokenKind::As {
        parser.advance();
        Ok(Some(parser.expect_identifier()?))
    } else {
        Ok(None)
    }
}

pub fn parse_body(parser: &mut Parser, start_span: Span) -> Result<(ThinVec<Stmt>, Span)> {
    let mut body = ThinVec::new();
    loop {
        if parser.current_token().kind == TokenKind::CloseCurly {
            break;
        }

        body.push(parse_stmt(parser)?);
    }
    let end_token = parser.expect(TokenKind::CloseCurly)?;
    let span = Span::new(start_span.start(), end_token.span.end());

    Ok((body, span))
}
