use anyhow::Result;
use thin_vec::ThinVec;

use crate::{
    ast::{
        AssocItem, AssocItemKind, Attribute, Block, Expr, Fn, GenericParam, GenericParams, Ident,
        ImportTree, ImportTreeKind, Item, ItemKind, Mutability, NodeId, Stmt, StmtKind, Type,
        TypeKind, Visibility,
    },
    diag_params,
    errors::builders,
    get_modifiers,
    lexer::token::TokenKind,
    no_attributes, no_modifiers,
    parser::{
        Parser,
        attributes::parse_attributes,
        diag,
        expr::parse_expr,
        lookups::{BindingPower, ITEM_LU},
        modifiers::{Modifier, parse_modifiers},
        types::parse_type,
        utils::{parse_body, parse_path, parse_rename, unexpected_token},
    },
    span::Span,
};

pub fn parse_item(parser: &mut Parser) -> Result<Item> {
    let attributes = parse_attributes(parser)?;
    let modifiers = parse_modifiers(parser);
    let item_lu = ITEM_LU.get().expect("Lookups not initialized");

    let item_fn = item_lu.get(&parser.current_token().kind).cloned();

    if let Some(item_fn) = item_fn {
        item_fn(parser, attributes, modifiers)
    } else {
        let tok = parser.current_token();
        builders::emit_at(
            parser.ctx,
            tok.span,
            tok.module_id,
            diag::ExpectedTopLevel,
            diag_params! { actual = tok.kind },
        );
        unreachable!()
    }
}

pub fn parse_const_item(
    mut parser: &mut Parser,
    attributes: ThinVec<Attribute>,
    modifiers: ThinVec<Modifier>,
) -> Result<Item> {
    no_attributes!(&mut parser, &attributes);

    let static_token = parser.advance();

    let name = parser.expect_identifier()?;

    parser.expect(TokenKind::Colon)?;
    let ty = parse_type(parser, BindingPower::DefaultBp)?;

    parser.expect(TokenKind::Equals)?;
    let value = parse_expr(parser, BindingPower::Assignment)?;

    let (pub_mod,) = get_modifiers!(&mut parser, modifiers, [Pub]);

    let mut is_public = false;

    let end_span = parser.expect(TokenKind::Semicolon)?.span;
    let mut start_span = static_token.span;

    if let Some(pub_mod) = pub_mod {
        start_span = pub_mod.span;
        is_public = true;
    };

    let span = Span::new(start_span.start(), end_span.end());

    let visibility = if is_public {
        Visibility::Public
    } else {
        Visibility::Private
    };

    Ok(Item {
        kind: ItemKind::Const { name, ty, value },
        node_id: NodeId::default(),
        attributes,
        span,
        visibility,
    })
}

pub fn parse_struct_decl_item(
    mut parser: &mut Parser,
    attributes: ThinVec<Attribute>,
    modifiers: ThinVec<Modifier>,
) -> Result<Item> {
    let struct_token = parser.expect(TokenKind::Struct)?;
    let mut fields: ThinVec<(Ident, Type, Visibility)> = ThinVec::new();
    let mut items: ThinVec<AssocItem> = ThinVec::new();
    let name = parser.expect_identifier()?;

    let generic_params = parse_optional_generic_params(parser)?;

    parser.expect(TokenKind::OpenCurly)?;

    loop {
        if !parser.has_tokens() || parser.current_token().kind == TokenKind::CloseCurly {
            break;
        }

        let is_public = parser.current_token().kind == TokenKind::Pub;
        if is_public {
            parser.advance();
        }

        let visibility = if is_public {
            Visibility::Public
        } else {
            Visibility::Private
        };

        match parser.current_token().kind {
            TokenKind::Fn => {
                let stmt = parse_fn_decl_item(parser, ThinVec::new(), ThinVec::new())?;
                let ItemKind::Fn(fn_decl) = stmt.kind else {
                    unreachable!()
                };
                if fn_decl.body.is_none() {
                    builders::emit_at(
                        parser.ctx,
                        fn_decl.name.span,
                        parser.current_token().module_id,
                        diag::StructMethodMissingBody,
                        diag_params! {},
                    );
                }
                items.push(AssocItem {
                    kind: AssocItemKind::Fn(fn_decl),
                    span: stmt.span,
                    visibility,
                    node_id: NodeId::default(),
                })
            }
            TokenKind::Type => {
                let mut assoc = parse_type_assoc_item(parser)?;
                let AssocItemKind::Type { type_, .. } = &mut assoc.kind else {
                    unreachable!()
                };
                if type_.is_none() {
                    builders::emit_at(
                        parser.ctx,
                        assoc.span,
                        parser.current_token().module_id,
                        diag::StructAssocTypeMissingBody,
                        diag_params! {},
                    );
                }
                assoc.visibility = visibility;
                items.push(assoc);
            }
            TokenKind::Identifier => {
                let property_name = parser.expect_identifier()?;
                parser.expect(TokenKind::Colon)?;
                let type_ = parse_type(parser, BindingPower::DefaultBp)?;

                if parser.current_token().kind != TokenKind::CloseCurly {
                    parser.expect(TokenKind::Comma)?;
                }

                if fields.iter().any(|arg| arg.0.value == property_name.value) {
                    let field = parser.ctx.interner.lookup(property_name.value).to_string();
                    let strct = parser.ctx.interner.lookup(name.value).to_string();
                    builders::emit_at(
                        parser.ctx,
                        property_name.span,
                        parser.current_token().module_id,
                        diag::FieldAlreadyDefined,
                        diag_params! { field = field, struct = strct },
                    );
                    continue;
                }
                fields.push((property_name, type_, visibility));
            }
            _ => unexpected_token(parser.ctx, parser.current_token(), "struct field"),
        }
    }

    let end_span = parser.expect(TokenKind::CloseCurly)?.span;

    let (pub_mod,) = get_modifiers!(&mut parser, modifiers, [Pub]);

    let mut is_public = false;

    let mut start_span = struct_token.span;

    if let Some(pub_mod) = pub_mod {
        start_span = pub_mod.span;
        is_public = true;
    };

    let span = Span::new(start_span.start(), end_span.end());

    let visibility = if is_public {
        Visibility::Public
    } else {
        Visibility::Private
    };

    Ok(Item {
        kind: ItemKind::Struct {
            name,
            fields,
            items,
            generic_params,
        },
        node_id: NodeId::default(),
        attributes,
        span,
        visibility,
    })
}

pub fn parse_type_decl_item(
    mut parser: &mut Parser,
    attributes: ThinVec<Attribute>,
    modifiers: ThinVec<Modifier>,
) -> Result<Item> {
    let type_token = parser.expect(TokenKind::Type)?;
    let name = parser.expect_identifier()?;

    let generic_params = parse_optional_generic_params(parser)?;

    parser.expect(TokenKind::Equals)?;

    let type_ = parse_type(parser, BindingPower::DefaultBp)?;

    let end_span = parser.expect(TokenKind::Semicolon)?.span;

    let (pub_mod,) = get_modifiers!(&mut parser, modifiers, [Pub]);

    let mut is_public = false;

    let mut start_span = type_token.span;

    if let Some(pub_mod) = pub_mod {
        start_span = pub_mod.span;
        is_public = true;
    };

    let span = Span::new(start_span.start(), end_span.end());

    let visibility = if is_public {
        Visibility::Public
    } else {
        Visibility::Private
    };

    Ok(Item {
        kind: ItemKind::Type {
            name,
            generic_params,
            type_,
        },
        node_id: NodeId::default(),
        attributes,
        span,
        visibility,
    })
}

pub fn parse_trait_decl_item(
    mut parser: &mut Parser,
    attributes: ThinVec<Attribute>,
    modifiers: ThinVec<Modifier>,
) -> Result<Item> {
    let trait_token = parser.expect(TokenKind::Trait)?;
    let name = parser.expect_identifier()?;

    let generic_params = parse_optional_generic_params(parser)?;

    let mut items: ThinVec<AssocItem> = ThinVec::new();
    parser.expect(TokenKind::OpenCurly)?;
    loop {
        if !parser.has_tokens() || parser.current_token().kind == TokenKind::CloseCurly {
            break;
        }

        match parser.current_token().kind {
            TokenKind::Type => {
                let mut assoc = parse_type_assoc_item(parser)?;
                if matches!(&assoc.kind, AssocItemKind::Type { type_: Some(_), .. }) {
                    builders::emit_at(
                        parser.ctx,
                        assoc.span,
                        parser.current_token().module_id,
                        diag::TraitAssocTypeHasBody,
                        diag_params! {},
                    );
                }
                assoc.visibility = Visibility::Private;
                items.push(assoc);
            }
            TokenKind::Fn => {
                let stmt = parse_fn_decl_item(parser, ThinVec::new(), ThinVec::new())?;
                if let ItemKind::Fn(fn_decl) = stmt.kind {
                    if fn_decl.body.is_some() {
                        builders::emit_at(
                            parser.ctx,
                            stmt.span,
                            parser.current_token().module_id,
                            diag::TraitMethodHasBody,
                            diag_params! {},
                        );
                    }

                    items.push(AssocItem {
                        kind: AssocItemKind::Fn(fn_decl),
                        visibility: Visibility::Private,
                        span: stmt.span,
                        node_id: NodeId::default(),
                    });
                }
            }
            _ => unexpected_token(parser.ctx, parser.current_token(), "trait body"),
        }
    }
    let end_span = parser.expect(TokenKind::CloseCurly)?.span;

    let (pub_mod,) = get_modifiers!(&mut parser, modifiers, [Pub]);

    let mut is_public = false;

    let mut start_span = trait_token.span;

    if let Some(pub_mod) = pub_mod {
        start_span = pub_mod.span;
        is_public = true;
    };

    let span = Span::new(start_span.start(), end_span.end());

    let visibility = if is_public {
        Visibility::Public
    } else {
        Visibility::Private
    };

    Ok(Item {
        kind: ItemKind::Trait {
            items,
            name,
            generic_params,
        },
        node_id: NodeId::default(),
        attributes,
        span,
        visibility,
    })
}

fn parse_type_assoc_item(parser: &mut Parser) -> Result<AssocItem> {
    let type_token = parser.expect(TokenKind::Type)?;
    let name = parser.expect_identifier()?;

    let type_ = if parser.current_token().kind == TokenKind::Equals {
        parser.advance();
        Some(parse_type(parser, BindingPower::DefaultBp)?)
    } else {
        None
    };

    let end_span = parser.expect(TokenKind::Semicolon)?.span;
    let span = Span::new(type_token.span.start(), end_span.end());

    Ok(AssocItem {
        kind: AssocItemKind::Type { name, type_ },
        visibility: Visibility::Private,
        span,
        node_id: NodeId::default(),
    })
}

pub fn parse_fn_decl_item(
    mut parser: &mut Parser,
    attributes: ThinVec<Attribute>,
    modifiers: ThinVec<Modifier>,
) -> Result<Item> {
    let (pub_mod, extern_mod) = get_modifiers!(&mut parser, modifiers, [Pub, Extern]);

    let mut start_span = parser.expect(TokenKind::Fn)?.span;
    if let Some(pub_mod) = pub_mod {
        start_span = pub_mod.span;
    } else if let Some(extern_mod) = extern_mod {
        start_span = extern_mod.span;
    }

    let name = parser.expect_identifier()?;

    let generic_params = parse_optional_generic_params(parser)?;

    parser.expect(TokenKind::OpenParen)?;
    let mut parameters: ThinVec<(Ident, Type, NodeId)> = ThinVec::new();

    loop {
        if parser.current_token().kind == TokenKind::CloseParen {
            break;
        }

        let arg_name = parser.expect_identifier()?;

        parser.expect(TokenKind::Colon)?;
        let type_ = parse_type(parser, BindingPower::DefaultBp)?;

        parameters.push((arg_name, type_, NodeId::default()));

        if parser.current_token().kind == TokenKind::Comma {
            parser.advance();
        }
    }

    parser.expect(TokenKind::CloseParen)?;

    // TODO: Maybe check if a '->' token is here and emit a helpful error message?

    let return_type = parse_type(parser, BindingPower::DefaultBp)?;

    let end_span;
    let mut body: Option<Block> = None;
    match parser.current_token().kind {
        TokenKind::OpenCurly => {
            let open_brace_span = parser.current_token().span;
            parser.advance();
            let (stmts, body_span) = parse_body(parser, open_brace_span)?;
            end_span = body_span;
            body = Some(Block {
                stmts,
                span: body_span,
            });
        }
        TokenKind::Semicolon => {
            end_span = parser.expect(TokenKind::Semicolon)?.span;
        }
        _ => {
            let tok = parser.current_token();
            builders::emit_at(
                parser.ctx,
                tok.span,
                tok.module_id,
                diag::ExpectedTermOrBodyAfterSignature,
                diag_params! {},
            );
            unreachable!();
        }
    }

    let span = Span::new(start_span.start(), end_span.end());

    let visibility = if pub_mod.is_some() {
        Visibility::Public
    } else {
        Visibility::Private
    };

    Ok(Item {
        kind: ItemKind::Fn(Fn {
            parameters,
            body,
            name,
            return_type,
            is_extern: extern_mod.is_some(),
            generic_params,
        }),
        node_id: NodeId::default(),
        attributes,
        span,
        visibility,
    })
}

pub fn parse_impl_item(
    mut parser: &mut Parser,
    attributes: ThinVec<Attribute>,
    modifiers: ThinVec<Modifier>,
) -> Result<Item> {
    no_attributes!(&mut parser, &attributes);
    no_modifiers!(&mut parser, &modifiers);

    let start_span = parser.expect(TokenKind::Impl)?.span;
    let trait_ = parse_path(parser)?;
    parser.expect(TokenKind::For)?;
    let self_ty = parse_path(parser)?;

    let mut items: ThinVec<AssocItem> = ThinVec::new();
    parser.expect(TokenKind::OpenCurly)?;
    loop {
        if !parser.has_tokens() || parser.current_token().kind == TokenKind::CloseCurly {
            break;
        }

        match parser.current_token().kind {
            TokenKind::Type => {
                let mut assoc = parse_type_assoc_item(parser)?;
                let has_body = matches!(&assoc.kind, AssocItemKind::Type { type_: Some(_), .. });
                if !has_body {
                    builders::emit_at(
                        parser.ctx,
                        assoc.span,
                        parser.current_token().module_id,
                        diag::ImplTypeMissingBody,
                        diag_params! {},
                    );
                }
                assoc.visibility = Visibility::Public;
                items.push(assoc);
            }
            TokenKind::Fn => {
                let stmt = parse_fn_decl_item(parser, ThinVec::new(), ThinVec::new())?;
                if let ItemKind::Fn(fn_decl) = stmt.kind {
                    if fn_decl.body.is_none() {
                        builders::emit_at(
                            parser.ctx,
                            fn_decl.name.span,
                            parser.current_token().module_id,
                            diag::ImplMethodMissingBody,
                            diag_params! {},
                        );
                    }
                    items.push(AssocItem {
                        kind: AssocItemKind::Fn(fn_decl),
                        visibility: Visibility::Public,
                        span: stmt.span,
                        node_id: NodeId::default(),
                    });
                }
            }
            _ => unexpected_token(parser.ctx, parser.current_token(), "impl body"),
        }
    }
    let end_span = parser.expect(TokenKind::CloseCurly)?.span;

    Ok(Item {
        kind: ItemKind::Impl {
            items,
            self_ty: (self_ty, NodeId::default()),
            trait_: (trait_, NodeId::default()),
        },
        node_id: NodeId::default(),
        attributes,
        span: Span::new(start_span.start(), end_span.end()),
        // Impl blocks do not have visibility modifiers in the source grammar, so we use
        // Visibility::Public as a placeholder value for AST uniformity. The visibility of
        // individual associated items within the impl block should be used instead.
        visibility: Visibility::Private,
    })
}

pub fn parse_module_item(
    mut parser: &mut Parser,
    attributes: ThinVec<Attribute>,
    modifiers: ThinVec<Modifier>,
) -> Result<Item> {
    let (pub_mod,) = get_modifiers!(&mut parser, modifiers, [Pub]);

    let start_span = parser.expect(TokenKind::Mod)?.span;
    let name = parser.expect_identifier()?;

    let end_span: Span;
    let body = if parser.current_token().kind == TokenKind::Semicolon {
        end_span = parser.advance().span;
        None
    } else {
        parser.expect(TokenKind::OpenCurly)?;
        let mut items = ThinVec::new();
        while parser.has_tokens() && parser.current_token().kind != TokenKind::CloseCurly {
            items.push(parse_item(parser)?);
        }
        end_span = parser.expect(TokenKind::CloseCurly)?.span;
        Some(items)
    };

    let visibility = if pub_mod.is_some() {
        Visibility::Public
    } else {
        Visibility::Private
    };

    Ok(Item {
        kind: ItemKind::Module { name, body },
        node_id: NodeId::default(),
        attributes,
        span: Span::new(start_span.start(), end_span.end()),
        visibility,
    })
}

pub fn parse_import_item(
    mut parser: &mut Parser,
    attributes: ThinVec<Attribute>,
    modifiers: ThinVec<Modifier>,
) -> Result<Item> {
    let (pub_mod,) = get_modifiers!(&mut parser, modifiers, [Pub]);

    let start_span = parser.expect(TokenKind::Import)?.span;
    let tree = parse_import_tree(parser)?;
    let end_span = parser.expect(TokenKind::Semicolon)?.span;

    let span = Span::new(start_span.start(), end_span.end());

    let visibility = if pub_mod.is_some() {
        Visibility::Public
    } else {
        Visibility::Private
    };

    Ok(Item {
        kind: ItemKind::Import(tree),
        node_id: NodeId::default(),
        attributes,
        span,
        visibility,
    })
}

fn parse_import_tree(parser: &mut Parser) -> Result<ImportTree> {
    let prefix = parse_path(parser)?;
    let kind = if parser.current_token().kind == TokenKind::ColonColon {
        parser.advance();
        if parser.current_token().kind == TokenKind::Star {
            parser.advance();
            ImportTreeKind::Glob
        } else {
            ImportTreeKind::Nested {
                items: parse_import_tree_list(parser)?,
                span: Span::new(prefix.span.start(), parser.current_token().span.end()),
            }
        }
    } else {
        ImportTreeKind::Simple(parse_rename(parser)?)
    };

    let span = Span::new(prefix.span.start(), parser.current_token().span.end() - 1);

    Ok(ImportTree { prefix, kind, span })
}

fn parse_import_tree_list(parser: &mut Parser) -> Result<ThinVec<ImportTree>> {
    let mut items = ThinVec::new();

    parser.expect(TokenKind::OpenCurly)?;

    loop {
        items.push(parse_import_tree(parser)?);

        if parser.current_token().kind == TokenKind::CloseCurly {
            break;
        }

        if parser.current_token().kind == TokenKind::Comma {
            parser.advance();
            if parser.current_token().kind == TokenKind::CloseCurly {
                break;
            }
        } else {
            break;
        }
    }

    parser.expect(TokenKind::CloseCurly)?;

    Ok(items)
}

pub fn parse_stmt(parser: &mut Parser) -> Result<Stmt> {
    let current_kind = parser.current_token().kind;

    match current_kind {
        TokenKind::Let => parse_let_stmt(parser),
        _ => parse_expr_stmt(parser),
    }
}

fn parse_let_stmt(parser: &mut Parser) -> Result<Stmt> {
    let let_token = parser.advance();
    let mut type_ = Type {
        kind: TypeKind::Infer,
        span: Span::new(let_token.span.end(), let_token.span.end()),
        node_id: NodeId::default(),
    };
    let mut assigned_value: Option<Expr> = None;

    let is_constant = parser.current_token().kind != TokenKind::Mut;

    if !is_constant {
        parser.advance();
    }

    let variable_name = parser.expect_identifier()?;

    if parser.current_token().kind == TokenKind::Colon {
        parser.advance();
        type_ = parse_type(parser, BindingPower::DefaultBp)?;
    }

    if parser.current_token().kind != TokenKind::Semicolon {
        parser.expect(TokenKind::Equals)?;
        assigned_value = Some(parse_expr(parser, BindingPower::Assignment)?);
    }

    let end_span = parser.expect(TokenKind::Semicolon)?.span;
    let span = Span::new(let_token.span.start(), end_span.end());

    if assigned_value.is_none() && is_constant {
        builders::emit_at(
            parser.ctx,
            span,
            parser.current_token().module_id,
            diag::ConstItemWithoutValue,
            diag_params! {},
        );
    }

    let mutability = if is_constant {
        Mutability::Constant
    } else {
        Mutability::Mutable
    };

    Ok(Stmt {
        kind: StmtKind::Let {
            name: variable_name,
            ty: type_,
            value: assigned_value,
            mutability,
        },
        node_id: NodeId::default(),
        span,
    })
}

fn parse_expr_stmt(parser: &mut Parser) -> Result<Stmt> {
    let expr = parse_expr(parser, BindingPower::DefaultBp)?;

    let mut has_semicolon = false;
    let mut semi_span = expr.span;
    if parser.current_token().kind == TokenKind::Semicolon {
        has_semicolon = true;
        semi_span = parser.current_token().span;
        parser.advance();
    }

    let span = Span::new(expr.span.start(), semi_span.end());
    let kind = if has_semicolon {
        StmtKind::Semi(expr)
    } else {
        StmtKind::Expr(expr)
    };

    Ok(Stmt {
        kind,
        span,
        node_id: NodeId::default(),
    })
}

fn parse_optional_generic_params(parser: &mut Parser) -> Result<Option<GenericParams>> {
    if parser.current_token().kind == TokenKind::Less {
        let start_span = parser.expect(TokenKind::Less)?.span;
        let mut params = ThinVec::new();
        loop {
            if parser.current_token().kind == TokenKind::More {
                break;
            }
            if !params.is_empty() {
                parser.expect(TokenKind::Comma)?;
                if parser.current_token().kind == TokenKind::More {
                    break;
                }
            }
            let name = parser.expect_identifier()?;
            let default = if parser.current_token().kind == TokenKind::Equals {
                parser.advance();
                Some(parse_type(parser, BindingPower::DefaultBp)?)
            } else {
                None
            };
            params.push(GenericParam {
                name,
                default,
                node_id: NodeId::default(),
            });
        }
        let end_span = parser.expect(TokenKind::More)?.span;
        Ok(Some(GenericParams {
            params,
            span: Span::new(start_span.start(), end_span.end()),
        }))
    } else {
        Ok(None)
    }
}
