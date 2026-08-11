use oxic_diag::include_diagnostics;

use crate::ast::visit::{VisitAction, Visitable, Visitor};
use crate::ast::{
    AssocItem, AssocItemKind, Ast, Block, Expr, ExprKind, Fn, GenericParams, Ident, Item, ItemKind,
    Stmt, StmtKind,
};
use crate::context::with_ctx_mut;
use crate::diag_params;
use crate::errors::builders;
use crate::errors::widgets::{CodeWidget, HighlightType, LocationWidget};
use crate::hir::ModuleId;
use fxhash::FxHashMap;

include_diagnostics!("diagnostics.toml");

struct AstValidator {
    module_id: ModuleId,
    in_function: bool,
    in_loop: bool,
    is_top_level: bool,
    in_trait: bool,
}

impl AstValidator {
    fn check_duplicate_names<'a, I>(&self, names: I, context: &str)
    where
        I: IntoIterator<Item = &'a Ident>,
    {
        let mut seen = FxHashMap::default();
        for ident in names {
            if let Some(first_span) = seen.insert(&ident.value, ident.span) {
                with_ctx_mut(|ctx| {
                    let ident_str = ctx.interner.lookup(ident.value).to_string();
                    let err = builders::prepare_diag_at_with_info(
                        ctx,
                        ident.span,
                        self.module_id,
                        &diag::DuplicateDefinition,
                        diag_params! { item = ident_str, scope = context },
                        format!("First definition of `{}` here", ident_str).as_str(),
                    )
                    .add_widget(
                        LocationWidget::new(first_span, self.module_id, ctx)
                            .expect("failed to create error"),
                    )
                    .add_widget(
                        CodeWidget::new(first_span, self.module_id, HighlightType::Info, ctx)
                            .expect("failed to create error"),
                    );
                    ctx.errors.add(err, ctx.enable_printing);
                });
            }
        }
    }

    fn validate_generic_param_order(&self, generic_params: &Option<GenericParams>) {
        let Some(generic_params) = generic_params else {
            return;
        };
        let mut seen_default = false;
        for param in &generic_params.params {
            if param.default.is_some() {
                seen_default = true;
            } else if seen_default {
                with_ctx_mut(|ctx| {
                    builders::emit_at(
                        ctx,
                        param.name.span,
                        self.module_id,
                        diag::GenericDefaultBefore,
                        diag_params! {},
                    );
                });
            }
        }
    }

    fn validate_fn_decl(&mut self, f: &Fn) {
        self.check_duplicate_names(f.parameters.iter().map(|a| &a.0), "function parameters");
        self.validate_generic_param_order(&f.generic_params);

        if f.is_extern {
            if f.body.is_some() {
                with_ctx_mut(|ctx| {
                    builders::emit_at(
                        ctx,
                        f.name.span,
                        self.module_id,
                        diag::ExternFunctionBody,
                        diag_params! {},
                    );
                });
            }
        } else if f.body.is_none() && !self.in_trait {
            with_ctx_mut(|ctx| {
                builders::emit_at(
                    ctx,
                    f.name.span,
                    self.module_id,
                    diag::NonExternFunctionBody,
                    diag_params! {},
                );
            });
        }

        if let Some(body) = &f.body {
            let old_in_function = self.in_function;
            let old_top_level = self.is_top_level;
            self.in_function = true;
            self.is_top_level = false;
            self.validate_block(body);
            self.in_function = old_in_function;
            self.is_top_level = old_top_level;
        }
    }

    fn validate_assoc_item(&mut self, item: &AssocItem) {
        match &item.kind {
            AssocItemKind::Fn(f) => self.validate_fn_decl(f),
            AssocItemKind::Type { type_, .. } => {
                if let Some(type_) = type_ {
                    type_.visit(self);
                }
            }
        }
    }

    fn validate_block(&mut self, block: &Block) {
        let stmts = &block.stmts;
        let len = stmts.len();

        for (i, stmt) in stmts.iter().enumerate() {
            if let StmtKind::Expr(expr) = &stmt.kind {
                if Self::is_block_expr(&expr.kind) {
                    continue;
                }

                if i != len - 1 {
                    with_ctx_mut(|ctx| {
                        builders::emit_at(
                            ctx,
                            stmt.span,
                            self.module_id,
                            diag::TailExprNotAtTail,
                            diag_params! {},
                        );
                    });
                }
            }
        }

        for stmt in stmts.iter() {
            stmt.visit(self);
        }
    }

    fn is_block_expr(kind: &ExprKind) -> bool {
        matches!(
            kind,
            ExprKind::Block(_) | ExprKind::If { .. } | ExprKind::While { .. } | ExprKind::Loop(_)
        )
    }

    fn is_lvalue(expr: &Expr) -> bool {
        matches!(
            &expr.kind,
            ExprKind::Path(_)
                | ExprKind::MemberAccess { .. }
                | ExprKind::Dereference { .. }
                | ExprKind::Index { .. }
        )
    }
}

impl Visitor for AstValidator {
    fn visit_item(&mut self, item: &Item) -> VisitAction {
        match &item.kind {
            ItemKind::Fn(f) => {
                self.validate_fn_decl(f);
                VisitAction::SkipChildren
            }
            ItemKind::Impl { items, .. } => {
                let old_top_level = self.is_top_level;
                self.is_top_level = false;
                for item in items.iter() {
                    self.validate_assoc_item(item);
                }
                self.is_top_level = old_top_level;
                VisitAction::SkipChildren
            }
            ItemKind::Struct {
                fields,
                items,
                generic_params,
                ..
            } => {
                self.validate_generic_param_order(generic_params);
                self.check_duplicate_names(fields.iter().map(|f| &f.0), "struct fields");
                self.check_duplicate_names(
                    items.iter().map(|item| match &item.kind {
                        AssocItemKind::Fn(f) => &f.name,
                        AssocItemKind::Type { name, .. } => name,
                    }),
                    "struct associated items",
                );

                let old_top_level = self.is_top_level;
                self.is_top_level = false;
                for item in items.iter() {
                    self.validate_assoc_item(item);
                }
                self.is_top_level = old_top_level;

                VisitAction::SkipChildren
            }
            ItemKind::Trait {
                items,
                generic_params,
                ..
            } => {
                self.validate_generic_param_order(generic_params);
                self.check_duplicate_names(
                    items.iter().map(|item| match &item.kind {
                        AssocItemKind::Fn(f) => &f.name,
                        AssocItemKind::Type { name, .. } => name,
                    }),
                    "trait associated items",
                );

                let old_top_level = self.is_top_level;
                let old_in_trait = self.in_trait;
                self.is_top_level = false;
                self.in_trait = true;
                for item in items.iter() {
                    self.validate_assoc_item(item);
                }
                self.is_top_level = old_top_level;
                self.in_trait = old_in_trait;

                VisitAction::SkipChildren
            }
            ItemKind::Const { .. } => VisitAction::Continue,
            ItemKind::Import(_) => VisitAction::Continue,
            ItemKind::Type { generic_params, .. } => {
                self.validate_generic_param_order(generic_params);
                VisitAction::Continue
            }
            ItemKind::Module { body, .. } => {
                if let Some(items) = body {
                    let mut names = Vec::new();
                    for item in items.iter() {
                        match &item.kind {
                            ItemKind::Fn(f) => names.push(&f.name),
                            ItemKind::Struct { name, .. } => names.push(name),
                            ItemKind::Trait { name, .. } => names.push(name),
                            ItemKind::Const { name, .. } => names.push(name),
                            ItemKind::Module { name, .. } => names.push(name),
                            ItemKind::Type { name, .. } => names.push(name),
                            ItemKind::Impl { .. } | ItemKind::Import(_) => {}
                        }
                    }
                    self.check_duplicate_names(names, "module scope");

                    let old_top_level = self.is_top_level;
                    self.is_top_level = true;
                    body.visit(self);
                    self.is_top_level = old_top_level;
                    VisitAction::SkipChildren
                } else {
                    VisitAction::SkipChildren
                }
            }
        }
    }

    fn visit_stmt(&mut self, stmt: &Stmt) -> VisitAction {
        match &stmt.kind {
            StmtKind::Let {
                name: _,
                ty: _,
                value,
                mutability: _,
            } => {
                if let Some(val) = value {
                    val.visit(self);
                }

                VisitAction::SkipChildren
            }
            _ => VisitAction::Continue,
        }
    }

    fn visit_expr(&mut self, expr: &Expr) -> VisitAction {
        match &expr.kind {
            ExprKind::StructInstantiation { path: _, fields } => {
                let mut seen = FxHashMap::default();
                for (ident, val) in fields.iter() {
                    if let Some(first_span) = seen.insert(&ident.value, ident.span) {
                        with_ctx_mut(|ctx| {
                            let ident_str = ctx.interner.lookup(ident.value).to_string();
                            let err = builders::prepare_diag_at_with_info(
                                ctx,
                                ident.span,
                                self.module_id,
                                &diag::DuplicateField,
                                diag_params! { field = ident_str },
                                "First initialization of `{}` here",
                            )
                            .add_widget(
                                LocationWidget::new(first_span, self.module_id, ctx)
                                    .expect("failed to create error"),
                            )
                            .add_widget(
                                CodeWidget::new(
                                    first_span,
                                    self.module_id,
                                    HighlightType::Info,
                                    ctx,
                                )
                                .expect("failed to create error"),
                            );
                            ctx.errors.add(err, ctx.enable_printing);
                        });
                    }
                    val.visit(self);
                }

                VisitAction::SkipChildren
            }
            ExprKind::Block(b) => {
                let old_top_level = self.is_top_level;
                self.is_top_level = false;
                self.validate_block(b);
                self.is_top_level = old_top_level;

                VisitAction::SkipChildren
            }
            ExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                condition.visit(self);
                self.validate_block(then_branch);
                if let Some(else_expr) = else_branch {
                    else_expr.visit(self);
                }
                VisitAction::SkipChildren
            }
            ExprKind::While { condition, body } => {
                condition.visit(self);
                let old_in_loop = self.in_loop;
                self.in_loop = true;
                self.validate_block(body);
                self.in_loop = old_in_loop;
                VisitAction::SkipChildren
            }
            ExprKind::Loop(body) => {
                let old_in_loop = self.in_loop;
                self.in_loop = true;
                self.validate_block(body);
                self.in_loop = old_in_loop;
                VisitAction::SkipChildren
            }
            ExprKind::Break(_) => {
                if !self.in_loop {
                    with_ctx_mut(|ctx| {
                        builders::emit_at(
                            ctx,
                            expr.span,
                            self.module_id,
                            diag::BreakOutsideLoop,
                            diag_params! {},
                        );
                    });
                }
                VisitAction::Continue
            }
            ExprKind::Return(_) => {
                if !self.in_function {
                    with_ctx_mut(|ctx| {
                        builders::emit_at(
                            ctx,
                            expr.span,
                            self.module_id,
                            diag::ReturnOutsideFunction,
                            diag_params! {},
                        );
                    });
                }
                VisitAction::Continue
            }
            ExprKind::Assignment { assignee, .. } => {
                if !Self::is_lvalue(assignee) {
                    with_ctx_mut(|ctx| {
                        builders::emit_at(
                            ctx,
                            assignee.span,
                            self.module_id,
                            diag::InvalidAssignmentTarget,
                            diag_params! {},
                        );
                    });
                }
                VisitAction::Continue
            }
            _ => VisitAction::Continue,
        }
    }
}

pub fn validate_ast(ast: &Ast, module_id: ModuleId) {
    let mut validator = AstValidator {
        module_id,
        in_function: false,
        in_loop: false,
        is_top_level: true,
        in_trait: false,
    };

    let mut top_level_names = Vec::new();
    for item in ast.items.iter() {
        match &item.kind {
            ItemKind::Fn(f) => top_level_names.push(&f.name),
            ItemKind::Struct { name, .. } => top_level_names.push(name),
            ItemKind::Trait { name, .. } => top_level_names.push(name),
            ItemKind::Const { name, .. } => top_level_names.push(name),
            ItemKind::Module { name, .. } => top_level_names.push(name),
            ItemKind::Type { name, .. } => top_level_names.push(name),
            ItemKind::Impl { .. } | ItemKind::Import(_) => {}
        }
    }
    validator.check_duplicate_names(top_level_names, "module scope");

    ast.visit(&mut validator);
}
