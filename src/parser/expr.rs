use anyhow::{Result, bail};
use thin_vec::ThinVec;

use crate::{
    ast::{Block, Expr, ExprKind, Ident, Literal, Mutability, NodeId, Path, RangeKind},
    diag_params,
    errors::builders,
    lexer::token::TokenKind,
    parser::{
        Parser, diag,
        lookups::{BP_LU, BindingPower, LED_LU, NUD_LU},
        string::process_string,
        types::parse_type,
        utils::{parse_body, parse_path, unexpected_token},
    },
    span::Span,
};

pub fn parse_expr(parser: &mut Parser, bp: BindingPower) -> Result<Expr> {
    let token = parser.current_token();
    let start_span = token.span;

    let bp_lu = BP_LU.get().expect("Lookups not initialized");
    let nud_lu = NUD_LU.get().expect("Lookups not initialized");
    let led_lu = LED_LU.get().expect("Lookups not initialized");

    let nud_fn = nud_lu
        .get(&token.kind)
        .cloned()
        .unwrap_or_else(|| unexpected_token(parser.ctx, token.clone(), "start of expression"));

    let mut left = nud_fn(parser)?;

    let mut end_span = left.span;

    loop {
        let current_bp = *bp_lu
            .get(&parser.current_token().kind)
            .unwrap_or(&BindingPower::DefaultBp);

        if current_bp <= bp {
            break;
        }

        let token_kind = parser.current_token();
        let led_fn = led_lu
            .get(&token_kind.kind)
            .cloned()
            .unwrap_or_else(|| unexpected_token(parser.ctx, token_kind.clone(), "infix operator"));

        left = led_fn(parser, left.clone(), current_bp)?;
        end_span = left.span;
    }

    left.span = Span::new(start_span.start(), end_span.end());
    Ok(left)
}

pub fn parse_primary_expr(parser: &mut Parser) -> Result<Expr> {
    let value = parser.current_token().value.clone();
    let token = parser.advance();
    let span = token.span;

    match token.kind {
        TokenKind::Number => {
            if value.contains('.') {
                Ok(Expr {
                    kind: ExprKind::Literal(Literal::Float(value.parse::<f64>()?)),
                    node_id: NodeId::default(),
                    span,
                })
            } else {
                Ok(Expr {
                    kind: ExprKind::Literal(Literal::Integer(value.parse::<i64>()?)),
                    node_id: NodeId::default(),
                    span,
                })
            }
        }
        TokenKind::StringLiteral => Ok(Expr {
            kind: ExprKind::Literal(Literal::String(process_string(
                parser.ctx,
                &value,
                span,
                token.module_id,
            ))),
            node_id: NodeId::default(),
            span,
        }),
        TokenKind::CharLiteral => Ok(Expr {
            kind: ExprKind::Literal(Literal::Char(
                value.chars().next().expect("value has a char"),
            )),
            node_id: NodeId::default(),
            span,
        }),
        TokenKind::Identifier => {
            parser.backtrack(1);
            let path = parse_path(parser)?;
            Ok(Expr {
                kind: ExprKind::Path(path.clone()),
                node_id: NodeId::default(),
                span: path.span,
            })
        }
        TokenKind::True => Ok(Expr {
            kind: ExprKind::Literal(Literal::Bool(true)),
            node_id: NodeId::default(),
            span,
        }),
        TokenKind::False => Ok(Expr {
            kind: ExprKind::Literal(Literal::Bool(false)),
            node_id: NodeId::default(),
            span,
        }),
        _ => unreachable!(),
    }
}

pub fn parse_binary_expr(parser: &mut Parser, left: Expr, bp: BindingPower) -> Result<Expr> {
    let operator = parser.advance();
    let right = parse_expr(parser, bp)?;

    let span = Span::new(left.span.start(), right.span.end());
    Ok(Expr {
        kind: ExprKind::Binary {
            left: Box::new(left),
            operator,
            right: Box::new(right),
        },
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_range_expr(parser: &mut Parser, left: Expr, bp: BindingPower) -> Result<Expr> {
    let operator = parser.advance();
    let kind = match operator.kind {
        TokenKind::DotDotIncl => RangeKind::Inclusive,
        TokenKind::DotDotExcl => RangeKind::Exclusive,
        _ => unreachable!(),
    };
    let right = parse_expr(parser, bp)?;
    let span = Span::new(left.span.start(), right.span.end());
    Ok(Expr {
        kind: ExprKind::Range {
            start: Some(Box::new(left)),
            end: Some(Box::new(right)),
            kind,
        },
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_dereference_expr(parser: &mut Parser, left: Expr, _bp: BindingPower) -> Result<Expr> {
    let operator = parser.advance();
    let span = Span::new(left.span.start(), operator.span.end());
    Ok(Expr {
        kind: ExprKind::Dereference {
            expr: Box::new(left),
        },
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_reference_expr(parser: &mut Parser) -> Result<Expr> {
    let operator = parser.advance();
    let expr = parse_expr(parser, BindingPower::Unary)?;
    let mutability = if parser.current_token().kind == TokenKind::Mut {
        parser.advance();
        Mutability::Mutable
    } else {
        Mutability::Constant
    };
    let span = Span::new(operator.span.start(), expr.span.end());
    Ok(Expr {
        kind: ExprKind::Reference {
            expr: Box::new(expr),
            mutability,
        },
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_unary_expr(parser: &mut Parser) -> Result<Expr> {
    let operator = parser.advance();
    let right = parse_expr(parser, BindingPower::Unary)?;

    let span = Span::new(operator.span.start(), right.span.end());
    Ok(Expr {
        kind: ExprKind::Unary {
            operator,
            right: Box::new(right),
        },
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_assignment_expr(
    parser: &mut Parser,
    assignee: Expr,
    _bp: BindingPower,
) -> Result<Expr> {
    let operator = parser.advance();
    let value = parse_expr(parser, BindingPower::Assignment)?;

    let span = Span::new(assignee.span.start(), value.span.end());
    Ok(Expr {
        kind: ExprKind::Assignment {
            assignee: Box::new(assignee),
            operator,
            value: Box::new(value),
        },
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_struct_instantiation_expr(
    parser: &mut Parser,
    left: Expr,
    _bp: BindingPower,
) -> Result<Expr> {
    let struct_path = match left.kind {
        ExprKind::Path(path) => path,
        _ => bail!("Expected path for struct instantiation"),
    };

    parser.expect(TokenKind::OpenCurly)?;

    let mut properties: ThinVec<(Ident, Expr)> = ThinVec::new();

    loop {
        if parser.current_token().kind == TokenKind::CloseCurly {
            break;
        }

        let property = parser.expect_identifier()?;

        let value = if parser.current_token().kind == TokenKind::Colon {
            parser.expect(TokenKind::Colon)?;
            parse_expr(parser, BindingPower::Assignment)?
        } else {
            Expr {
                kind: ExprKind::Path(Path::from_ident(property)),
                node_id: NodeId::default(),
                span: property.span,
            }
        };

        properties.push((property, value));

        if parser.current_token().kind != TokenKind::CloseCurly {
            parser.expect(TokenKind::Comma)?;
        }
    }

    let close_token = parser.expect(TokenKind::CloseCurly)?;

    let span = Span::new(left.span.start(), close_token.span.end());
    Ok(Expr {
        kind: ExprKind::StructInstantiation {
            path: struct_path,
            fields: properties,
        },
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_index_expr(parser: &mut Parser, left: Expr, _bp: BindingPower) -> Result<Expr> {
    parser.expect(TokenKind::OpenBracket)?;
    let index = parse_expr(parser, BindingPower::Assignment)?;
    let close_span = parser.expect(TokenKind::CloseBracket)?.span;
    let span = Span::new(left.span.start(), close_span.end());
    Ok(Expr {
        kind: ExprKind::Index {
            base: Box::new(left),
            index: Box::new(index),
        },
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_array_literal_expr(parser: &mut Parser) -> Result<Expr> {
    let start_token = parser.expect(TokenKind::OpenBracket)?;

    let mut contents: ThinVec<Expr> = ThinVec::new();

    loop {
        if parser.current_token().kind == TokenKind::CloseBracket {
            break;
        }

        contents.push(parse_expr(parser, BindingPower::Assignment)?);

        if parser.current_token().kind != TokenKind::CloseBracket {
            parser.expect(TokenKind::Comma)?;
        }
    }

    let close_token = parser.expect(TokenKind::CloseBracket)?;
    let span = Span::new(start_token.span.start(), close_token.span.end());

    Ok(Expr {
        kind: ExprKind::Array { contents },
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_function_call_expr(
    parser: &mut Parser,
    left: Expr,
    _bp: BindingPower,
) -> Result<Expr> {
    parser.expect(TokenKind::OpenParen)?;

    let mut arguments: ThinVec<Expr> = ThinVec::new();
    loop {
        if parser.current_token().kind == TokenKind::CloseParen {
            break;
        }

        arguments.push(parse_expr(parser, BindingPower::Assignment)?);

        if parser.current_token().kind != TokenKind::CloseParen {
            parser.expect(TokenKind::Comma)?;
        }
    }

    let end_span = parser.expect(TokenKind::CloseParen)?.span;
    let span = Span::new(left.span.start(), end_span.end());
    Ok(Expr {
        kind: ExprKind::FunctionCall {
            callee: Box::new(left),
            arguments,
        },
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_member_access_expr(
    parser: &mut Parser,
    left: Expr,
    _bp: BindingPower,
) -> Result<Expr> {
    parser.advance();

    let member = parser.expect_identifier()?;
    let member_span = member.span;

    let span = Span::new(left.span.start(), member_span.end());
    Ok(Expr {
        kind: ExprKind::MemberAccess {
            base: Box::new(left),
            member,
        },
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_as_cast_expr(parser: &mut Parser, left: Expr, _bp: BindingPower) -> Result<Expr> {
    parser.expect(TokenKind::As)?;

    let ty = parse_type(parser, BindingPower::DefaultBp)?;

    let span = Span::new(left.span.start(), ty.span.end());
    Ok(Expr {
        kind: ExprKind::As {
            expr: Box::new(left),
            ty,
        },
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_parenthesis_expr(parser: &mut Parser) -> Result<Expr> {
    let start_token = parser.expect(TokenKind::OpenParen)?;

    let mut elements = ThinVec::new();
    let mut has_comma = false;

    while parser.current_token().kind != TokenKind::CloseParen {
        elements.push(parse_expr(parser, BindingPower::DefaultBp)?);

        let tok = parser.current_token();
        if tok.kind == TokenKind::Comma {
            has_comma = true;
            parser.advance();
        } else if tok.kind != TokenKind::CloseParen {
            builders::emit_at(
                parser.ctx,
                tok.span,
                tok.module_id,
                diag::ExpectedCommaOrClosingParen,
                diag_params! { actual = tok.kind },
            );
            unreachable!();
        }
    }
    let close_token = parser.expect(TokenKind::CloseParen)?;
    let end_span = close_token.span;

    if elements.len() == 1 && !has_comma {
        let mut expr = elements.pop().expect("expressions isn't empty");
        expr.span = Span::new(start_token.span.start(), end_span.end());
        Ok(expr)
    } else {
        Ok(Expr {
            kind: ExprKind::Tuple { elements },
            node_id: NodeId::default(),
            span: Span::new(start_token.span.start(), end_span.end()),
        })
    }
}

pub fn parse_block_expr(parser: &mut Parser) -> Result<Expr> {
    let start_span = parser.expect(TokenKind::OpenCurly)?.span;

    let (body, span) = parse_body(parser, start_span)?;

    Ok(Expr {
        kind: ExprKind::Block(Block { stmts: body, span }),
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_if_expr(parser: &mut Parser) -> Result<Expr> {
    let start_span = parser.expect(TokenKind::If)?.span;

    let condition = Box::new(parse_expr(parser, BindingPower::Call)?);

    parser.expect(TokenKind::OpenCurly)?;
    let (stmts, body_span) = parse_body(parser, start_span)?;

    let mut else_branch: Option<Box<Expr>> = None;
    if parser.current_token().kind == TokenKind::Else {
        parser.advance();
        let expr = parse_expr(parser, BindingPower::DefaultBp)?;
        else_branch = Some(Box::new(expr));
    }

    let mut span = body_span;
    if let Some(else_branch) = &else_branch {
        span = Span::new(body_span.start(), else_branch.span.end());
    }

    Ok(Expr {
        kind: ExprKind::If {
            condition,
            then_branch: Block {
                stmts,
                span: body_span,
            },
            else_branch,
        },
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_while_expr(parser: &mut Parser) -> Result<Expr> {
    let start_span = parser.expect(TokenKind::While)?.span;
    let condition = Box::new(parse_expr(parser, BindingPower::Call)?);
    parser.expect(TokenKind::OpenCurly)?;
    let (stmts, span) = parse_body(parser, start_span)?;
    Ok(Expr {
        kind: ExprKind::While {
            condition,
            body: Block { stmts, span },
        },
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_loop_expr(parser: &mut Parser) -> Result<Expr> {
    let start_span = parser.expect(TokenKind::Loop)?.span;
    parser.expect(TokenKind::OpenCurly)?;
    let (stmts, span) = parse_body(parser, start_span)?;
    Ok(Expr {
        kind: ExprKind::Loop(Block { stmts, span }),
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_break_expr(parser: &mut Parser) -> Result<Expr> {
    let start_span = parser.expect(TokenKind::Break)?.span;

    let value = if has_expr(parser) {
        Some(Box::new(parse_expr(parser, BindingPower::DefaultBp)?))
    } else {
        None
    };

    let end_span = value.as_ref().map(|v| v.span).unwrap_or(start_span);
    let span = Span::new(start_span.start(), end_span.end());

    Ok(Expr {
        kind: ExprKind::Break(value),
        node_id: NodeId::default(),
        span,
    })
}

pub fn parse_return_expr(parser: &mut Parser) -> Result<Expr> {
    let start_span = parser.expect(TokenKind::Return)?.span;

    let value = if has_expr(parser) {
        Some(Box::new(parse_expr(parser, BindingPower::DefaultBp)?))
    } else {
        None
    };

    let end_span = value.as_ref().map(|v| v.span).unwrap_or(start_span);
    let span = Span::new(start_span.start(), end_span.end());

    Ok(Expr {
        kind: ExprKind::Return(value),
        node_id: NodeId::default(),
        span,
    })
}

fn has_expr(parser: &mut Parser) -> bool {
    let current = parser.current_token().kind;
    !matches!(
        current,
        TokenKind::Semicolon | TokenKind::CloseCurly | TokenKind::Comma
    )
}
