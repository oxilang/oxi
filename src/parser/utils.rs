use anyhow::Result;
use thin_vec::ThinVec;

use crate::{
    ast::{Expr, ExprKind, Ident, NodeId, Path, PathSegment, Stmt, StmtKind, Type},
    context::Ctx,
    diag_params,
    errors::builders,
    lexer::token::{Token, TokenKind},
    parser::{
        Parser, diag, expr::parse_expr, lookups::BindingPower, stmt::parse_let_stmt,
        types::parse_type,
    },
    span::Span,
};

pub fn unexpected_token(ctx: &mut Ctx, token: Token, expected: impl std::fmt::Display) -> ! {
    builders::emit_at(
        ctx,
        token.span,
        token.module_id,
        diag::UnexpectedToken,
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
        let args = parse_generic_args(parser)?;
        span_end = args
            .last()
            .map(|arg| arg.span)
            .unwrap_or_else(|| ident.span)
            .end();
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

fn parse_generic_args(parser: &mut Parser) -> Result<ThinVec<Type>> {
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
    parser.expect(TokenKind::More)?;
    Ok(args)
}

pub fn parse_rename(parser: &mut Parser) -> Result<Option<Ident>> {
    if parser.current_token().kind == TokenKind::As {
        parser.advance();
        Ok(Some(parser.expect_identifier()?))
    } else {
        Ok(None)
    }
}

pub fn is_block_expr(kind: &ExprKind) -> bool {
    matches!(
        kind,
        ExprKind::Block(_) | ExprKind::If { .. } | ExprKind::While { .. } | ExprKind::Loop(_)
    )
}

pub fn parse_body(
    parser: &mut Parser,
    start_span: Span,
) -> Result<(ThinVec<Stmt>, Option<Box<Expr>>, Span)> {
    let mut stmts = ThinVec::new();
    let mut tail: Option<Box<Expr>> = None;
    loop {
        if parser.current_token().kind == TokenKind::CloseCurly {
            break;
        }

        if parser.current_token().kind == TokenKind::Let {
            stmts.push(parse_let_stmt(parser)?);
            continue;
        }

        let expr = parse_expr(parser, BindingPower::DefaultBp)?;

        if parser.current_token().kind == TokenKind::Semicolon {
            let semi_span = parser.current_token().span;
            parser.advance();
            let span = Span::new(expr.span.start(), semi_span.end());
            stmts.push(Stmt {
                kind: StmtKind::Expr(expr),
                span,
                node_id: NodeId::default(),
            });
            continue;
        }

        if parser.current_token().kind == TokenKind::CloseCurly {
            tail = Some(Box::new(expr));
            break;
        }

        if is_block_expr(&expr.kind) {
            let span = expr.span;
            stmts.push(Stmt {
                kind: StmtKind::Expr(expr),
                span,
                node_id: NodeId::default(),
            });
            continue;
        }

        builders::emit_at(
            parser.ctx,
            expr.span,
            parser.current_token().module_id,
            diag::TailExprNotAtTail,
            diag_params! {},
        );
        let span = expr.span;
        stmts.push(Stmt {
            kind: StmtKind::Expr(expr),
            span,
            node_id: NodeId::default(),
        });
    }
    let end_token = parser.expect(TokenKind::CloseCurly)?;
    let span = Span::new(start_span.start(), end_token.span.end());

    Ok((stmts, tail, span))
}
