mod attributes;
mod expr;
mod lookups;
mod modifiers;
mod stmt;
mod string;
mod types;
mod utils;

use std::path::PathBuf;

use anyhow::Result;
use oxic_diag::include_diagnostics;
use thin_vec::ThinVec;

use crate::ast::{Ast, Ident, Item};
use crate::context::Ctx;
use crate::diag_params;
use crate::errors::builders;
use crate::lexer::token::{Token, TokenKind, TokenStream};
use crate::parser::lookups::create_token_lookups;
use crate::parser::stmt::parse_item;
use crate::parser::types::create_token_type_lookups;

include_diagnostics!("diagnostics.toml");

pub struct Parser<'ctx> {
    ctx: &'ctx mut Ctx,
    tokens: ThinVec<Token>,
    pos: usize,
}

impl<'ctx> Parser<'ctx> {
    pub fn new(ctx: &'ctx mut Ctx, tokens: TokenStream) -> Self {
        Parser {
            tokens: tokens.0,
            pos: 0,
            ctx,
        }
    }

    pub fn tokens(&self) -> &[Token] {
        &self.tokens
    }

    pub fn current_token(&self) -> Token {
        if self.pos < self.tokens.len() {
            self.tokens[self.pos].clone()
        } else {
            let prev_token = self.tokens[self.tokens.len() - 1].clone();
            Token {
                kind: TokenKind::Eof,
                span: prev_token.span,
                module_id: prev_token.module_id,
                value: "".into(),
            }
        }
    }

    pub fn peek(&self) -> Token {
        if self.pos + 1 < self.tokens.len() {
            self.tokens[self.pos + 1].clone()
        } else {
            let prev_token = self.tokens[self.tokens.len() - 1].clone();
            Token {
                kind: TokenKind::Eof,
                span: prev_token.span,
                module_id: prev_token.module_id,
                value: "".into(),
            }
        }
    }

    pub fn advance(&mut self) -> Token {
        let current = self.current_token();
        self.pos += 1;
        current
    }

    pub fn backtrack(&mut self, amount: usize) {
        self.pos -= amount;
    }

    pub fn has_tokens(&self) -> bool {
        self.pos < self.tokens.len()
    }

    pub fn expect(&mut self, expected_kind: TokenKind) -> Result<Token> {
        let token = self.current_token();

        if token.kind != expected_kind {
            builders::emit_at(
                self.ctx,
                token.span,
                token.module_id,
                diag::ExpectedToken,
                diag_params! { expected = expected_kind, actual = token.kind },
            );
            unreachable!();
        }

        Ok(self.advance())
    }

    pub fn expect_identifier(&mut self) -> Result<Ident> {
        let token = self.current_token();

        if token.kind != TokenKind::Identifier {
            builders::emit_at(
                self.ctx,
                token.span,
                token.module_id,
                diag::ExpectedIdentifier,
                diag_params! { actual = token.kind },
            );
            unreachable!();
        }

        self.advance();
        Ident::from_token(self.ctx, token)
    }
}

pub fn parse(ctx: &mut Ctx, tokens: TokenStream, path: &PathBuf) -> Result<Ast> {
    create_token_lookups();
    create_token_type_lookups();

    let mut items: ThinVec<Item> = ThinVec::new();
    let mut parser = Parser::new(ctx, tokens);

    while parser.has_tokens() {
        items.push(parse_item(&mut parser)?);
    }

    Ok(Ast::new(items, path))
}
