mod call;

use std::cmp::Ordering;

use thin_vec::ThinVec;

use crate::ast::{Ident, Literal, Mutability};
use crate::context::Ctx;
use crate::diag_params;
use crate::errors::builders;
use crate::hir::{
    self, AssocItemKind, BinOp, Block, Body, DefId, Expr, ExprKind, FloatTy, FnDecl, HirId, IntTy,
    ItemKind, MaybeOwner, ModuleId, Node, PrimTy, QPath, StmtKind, UintTy, UnOp,
};
use crate::interner::{Interner, Symbol};
use crate::resolve::{Res, ResolverOutputs};
use crate::span::Span;
use crate::typeck::env::ScopeEnv;
use crate::typeck::fold::substitute_ty_vars;
use crate::typeck::infctx::{InferCtx, TyVarSource};
use crate::typeck::types::{Scheme, Ty};
use crate::typeck::unify::{OrPushErr, UnifyError, unify};
use crate::typeck::{Adjustment, CoherenceTable, MemberRes, TyVarId, Typeck, diag};
use fxhash::{FxHashMap, FxHashSet};

// Labels aren't supported yet, so early returns are only checked for loops. AST Validation should
// catch uses of `break` outside of loops
#[derive(Debug)]
struct BlockTyRes {
    tail: Ty,
    early: Option<Ty>,
}

fn tail_span(expr: &Expr) -> Span {
    match &expr.kind {
        ExprKind::Block(block) => block
            .tail
            .as_ref()
            .map(|tail| tail.span)
            .unwrap_or(expr.span),
        _ => expr.span,
    }
}

impl<'ctx, 'hir, 'res> Typeck<'ctx, 'hir, 'res> {
    pub(crate) fn check_bodies(&mut self) {
        let mut icx = InferCtx::default();
        icx.push_level();

        let mut node_types: FxHashMap<HirId, Ty> = FxHashMap::default();
        let mut member_res: FxHashMap<HirId, MemberRes> = FxHashMap::default();
        let mut local_schemes: FxHashMap<HirId, Scheme> = FxHashMap::default();
        let mut adjustments: FxHashMap<HirId, Vec<Adjustment>> = FxHashMap::default();

        let mut checker = BodyChecker {
            ctx: self.ctx,
            icx: &mut icx,
            item_schemes: &mut self.item_schemes,
            inherent_methods: &mut self.inherent_methods,
            trait_methods: &mut self.trait_methods,
            coherence: &mut self.coherence,
            resolver: self.resolver,
            node_types: &mut node_types,
            member_res: &mut member_res,
            local_schemes: &mut local_schemes,
            adjustments: &mut adjustments,
            env: ScopeEnv::new(),
            module_id: ModuleId(0),
        };

        for (i, owner) in self.krate.owners.iter().enumerate() {
            let def_id = DefId(i as u32);

            let MaybeOwner::Owner(info) = owner else {
                continue;
            };

            let module_id = self.def_to_module.get(&def_id).expect("contains def id");
            checker.module_id = *module_id;

            match &info.nodes.nodes[0].node {
                Node::Item(item) => match &item.kind {
                    ItemKind::Fn(fun) => {
                        checker.register_if_generic(&fun.generic_params);
                        if let Some(body_id) = fun.body_id
                            && let Some(body) = info.nodes.body(body_id)
                        {
                            checker.check_fn_body(&fun.decl, body);
                        }
                    }
                    ItemKind::Const { ty, body_id, .. } => {
                        if let Some(body_id) = body_id
                            && let Some(body) = info.nodes.body(*body_id)
                        {
                            checker.check_const_body(ty, body);
                        }
                    }
                    _ => {}
                },
                Node::AssocItem(assoc) => {
                    let AssocItemKind::Fn(fun) = &assoc.kind;
                    if let Some(&parent_def_id) = checker.coherence.assoc_to_parent.get(&def_id) {
                        checker.register_if_generic_def(parent_def_id);
                    }
                    checker.register_if_generic(&fun.generic_params);
                    if let Some(body_id) = fun.body_id
                        && let Some(body) = info.nodes.body(body_id)
                    {
                        checker.check_fn_body(&fun.decl, body);
                    }
                }
                _ => {}
            }
        }

        self.hir_id_to_ty_var = std::mem::take(&mut icx.hir_id_to_ty_var);

        let int_ids = icx.vars_with_source(TyVarSource::IntLit);
        let i32_ty = Ty::Prim(PrimTy::Int(IntTy::I32));
        for var in int_ids {
            if icx.is_bound(var) {
                continue;
            }
            let var_span = icx.ty_var_span(var).unwrap_or(Span::new(0, 0));
            let var_module = icx.ty_var_module(var);
            unify(&mut icx, &Ty::Var(var), &i32_ty, var_span, var_module).or_push_err(&mut icx);
        }
        let float_ids = icx.vars_with_source(TyVarSource::FloatLit);
        let f64_ty = Ty::Prim(PrimTy::Float(FloatTy::F64));
        for var in float_ids {
            if icx.is_bound(var) {
                continue;
            }
            let var_span = icx.ty_var_span(var).unwrap_or(Span::new(0, 0));
            let var_module = icx.ty_var_module(var);
            unify(&mut icx, &Ty::Var(var), &f64_ty, var_span, var_module).or_push_err(&mut icx);
        }

        let empty_array_ids = icx.vars_with_source(TyVarSource::EmptyArray);
        for var in empty_array_ids {
            if icx.is_bound(var) {
                continue;
            }
            let var_span = icx.ty_var_span(var).unwrap_or(Span::new(0, 0));
            let var_module = icx.ty_var_module(var);
            builders::emit_at(
                self.ctx,
                var_span,
                var_module,
                diag::InferEmptyArray,
                diag_params! {},
            )
        }

        let generic_defaults = std::mem::take(&mut icx.generic_defaults);
        for (var, default_ty) in generic_defaults {
            if icx.is_bound(var) {
                continue;
            }
            let span = icx.ty_var_span(var).unwrap_or(Span::new(0, 0));
            let module_id = icx.ty_var_module(var);
            unify(&mut icx, &Ty::Var(var), &default_ty, span, module_id).or_push_err(&mut icx);
        }

        let resolved: FxHashMap<HirId, Ty> = node_types
            .iter()
            .map(|(&id, ty)| (id, icx.resolve(ty)))
            .collect();

        self.node_types.extend(resolved);
        self.member_res.extend(member_res);
        self.adjustments.extend(adjustments);

        for err in &icx.errors {
            emit_unify_error(err, self.resolver, self.ctx, &icx);
        }
    }
}

#[allow(clippy::type_complexity)]
struct BodyChecker<'a, 'b, 'ctx, 'res> {
    icx: &'a mut InferCtx,
    item_schemes: &'b mut FxHashMap<DefId, Scheme>,
    inherent_methods: &'b mut FxHashMap<DefId, FxHashMap<Symbol, DefId>>,
    trait_methods: &'b mut FxHashMap<DefId, FxHashMap<Symbol, Vec<(DefId, DefId)>>>,
    coherence: &'b mut CoherenceTable,
    ctx: &'ctx mut Ctx,
    resolver: &'res ResolverOutputs,
    node_types: &'a mut FxHashMap<HirId, Ty>,
    member_res: &'a mut FxHashMap<HirId, MemberRes>,
    local_schemes: &'a mut FxHashMap<HirId, Scheme>,
    adjustments: &'a mut FxHashMap<HirId, Vec<Adjustment>>,
    env: ScopeEnv,
    module_id: ModuleId,
}

impl<'a, 'b, 'ctx, 'res> BodyChecker<'a, 'b, 'ctx, 'res> {
    fn register_if_generic(&mut self, generic_params: &Option<ThinVec<hir::GenericParam>>) {
        if let Some(params) = generic_params {
            for param in params {
                let ty_var = self.icx.next_ty_var();
                self.icx.hir_id_to_ty_var.insert(param.hir_id, ty_var);
            }
        }
    }

    fn register_if_generic_def(&mut self, def: DefId) {
        if let Some(info) = self.coherence.generic_params.get(&def) {
            for &hir_id in &info.hir_ids {
                if !self.icx.hir_id_to_ty_var.contains_key(&hir_id) {
                    let ty_var = self.icx.next_ty_var();
                    self.icx.hir_id_to_ty_var.insert(hir_id, ty_var);
                }
            }
        }
    }

    fn check_const_body(&mut self, ty: &hir::Ty, body: &Body) {
        let expected = Ty::from_hir(self.icx, ty);
        self.node_types.insert(ty.hir_id, expected.clone());
        let body_ty = self.check_expr(&body.value);
        if let Err(err) = unify(
            self.icx,
            &expected,
            &body_ty,
            body.value.span,
            self.module_id,
        ) {
            self.report_type_error(err);
        }
    }

    fn check_fn_body(&mut self, decl: &FnDecl, body: &Body) {
        self.env.push();
        for (param, input) in body.params.iter().zip(decl.params.iter()) {
            let param_ty = Ty::from_hir(self.icx, input);
            self.node_types.insert(input.hir_id, param_ty.clone());
            let scheme = Scheme::monomorphic(param_ty);
            self.local_schemes.insert(param.hir_id, scheme.clone());
            self.env.insert(param.hir_id, scheme);
        }
        let expected = Ty::from_hir(self.icx, &decl.ret);
        self.node_types.insert(decl.ret.hir_id, expected.clone());
        self.check_expr(&body.value);
        self.check_return_values(&body.value, &expected, body.value.span);
        if let Some(body_ty) = self.node_types.get(&body.value.hir_id).cloned()
            && let Err(err) = unify(
                self.icx,
                &expected,
                &body_ty,
                tail_span(&body.value),
                self.module_id,
            )
        {
            self.report_type_error(err);
        }
        self.env.pop();
    }

    fn check_return_values(&mut self, expr: &Expr, expected: &Ty, span: Span) {
        match &expr.kind {
            ExprKind::Return(inner) => {
                let inner = if let Some(inner) = inner {
                    self.node_types
                        .get(&inner.hir_id)
                        .cloned()
                        .unwrap_or(Ty::Error)
                } else {
                    Ty::Prim(PrimTy::Void)
                };
                if let Err(err) = unify(self.icx, expected, &inner, span, self.module_id) {
                    self.report_type_error(err);
                }
            }
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.check_return_values_in_block(then_branch, expected);
                if let Some(else_branch) = else_branch {
                    self.check_return_values(else_branch, expected, span);
                }
            }
            ExprKind::Block(block) => self.check_return_values_in_block(block, expected),
            ExprKind::Loop(block) => self.check_return_values_in_block(block, expected),
            _ => {}
        }
    }

    fn check_return_values_in_block(&mut self, block: &Block, expected: &Ty) {
        for stmt in &block.stmts {
            if let StmtKind::Expr(expr) = &stmt.kind {
                self.check_return_values(expr, expected, stmt.span);
            }
        }
        if let Some(tail) = &block.tail {
            self.check_return_values(tail, expected, tail.span);
        }
    }

    fn check_expr(&mut self, expr: &Expr) -> Ty {
        let id = expr.hir_id;
        let ty = self.check_expr_kind(&expr.kind, id, expr.span);
        self.node_types.insert(id, ty.clone());
        ty
    }

    fn check_expr_kind(&mut self, kind: &ExprKind, hir_id: HirId, expr_span: Span) -> Ty {
        match kind {
            ExprKind::Error => Ty::Error,
            ExprKind::Literal(lit) => self.check_lit(lit, expr_span),
            ExprKind::Path(qpath) => self.check_path(qpath),
            ExprKind::Binary { left, op, right } => self.check_binary(left, *op, right),
            ExprKind::Unary { op, right } => self.check_unary(*op, right),
            ExprKind::Dereference { expr } => self.check_dereference(expr),
            ExprKind::Reference { expr, mutability } => self.check_reference(expr, *mutability),
            ExprKind::Call { callee, args } => self.check_call(callee, args, expr_span),
            ExprKind::StructInit {
                def,
                generic_args,
                fields,
            } => self.check_struct_init(*def, generic_args, fields, expr_span),
            ExprKind::ArrayInit { contents } => self.check_array_init(contents, expr_span),
            ExprKind::TupleInit(elements) => {
                Ty::Tuple(elements.iter().map(|expr| self.check_expr(expr)).collect())
            }
            ExprKind::Block(block) => self.check_block(block).tail,
            ExprKind::Loop(block) => self.check_loop(block),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_ty = self.check_expr(cond);
                let bool_ty = Ty::Prim(PrimTy::Bool);
                if let Err(err) = unify(self.icx, &bool_ty, &cond_ty, cond.span, self.module_id) {
                    self.report_type_error(err);
                }
                let then_span = then_branch.span;
                let then_ty = self.check_block(then_branch).tail;
                let void_ty = Ty::Prim(PrimTy::Void);
                let else_ty = else_branch.as_ref().map(|expr| self.check_expr(expr));
                match else_ty {
                    Some(else_ty) => {
                        if let Err(err) =
                            unify(self.icx, &then_ty, &else_ty, then_span, self.module_id)
                        {
                            self.report_type_error(err);
                        }
                        then_ty
                    }
                    None => {
                        if let Err(err) =
                            unify(self.icx, &void_ty, &then_ty, then_span, self.module_id)
                        {
                            self.report_type_error(err);
                        }
                        void_ty
                    }
                }
            }
            ExprKind::Break(expr) | ExprKind::Return(expr) => {
                if let Some(expr) = expr {
                    self.check_expr(expr);
                }
                Ty::Never
            }
            ExprKind::Assign { target, value, .. } => {
                let target_ty = self.check_expr(target);
                let value_ty = self.check_expr(value);
                if let Err(err) = unify(self.icx, &target_ty, &value_ty, value.span, self.module_id)
                {
                    self.report_type_error(err);
                }
                Ty::Prim(PrimTy::Void)
            }
            ExprKind::MemberAccess { base, member } => {
                self.check_member_access(*member, base, expr_span, hir_id)
            }
            ExprKind::Index { base, index } => self.check_index(base, index, expr_span, hir_id),
            ExprKind::As { expr, ty } => {
                self.check_expr(expr);
                let target_ty = Ty::from_hir(self.icx, ty);
                self.node_types.insert(ty.hir_id, target_ty.clone());
                target_ty
            }
            ExprKind::MethodCall { .. } | ExprKind::Field { .. } => {
                // MethodCall and Field cannot exist yet
                unreachable!()
            }
        }
    }

    fn check_lit(&mut self, lit: &Literal, span: Span) -> Ty {
        match lit {
            Literal::Integer(_) => Ty::Var(self.icx.next_int_var(span, self.module_id)),
            Literal::Float(_) => Ty::Var(self.icx.next_float_var(span, self.module_id)),
            Literal::Bool(_) => Ty::Prim(PrimTy::Bool),
            Literal::Char(_) => Ty::Prim(PrimTy::Uint(UintTy::U8)),
            Literal::String(_) => Ty::Slice(Ty::Prim(PrimTy::Uint(UintTy::U8)).into_box()),
        }
    }

    fn check_path(&mut self, qpath: &QPath) -> Ty {
        match qpath {
            QPath::Resolved(path) => match &path.res {
                Res::Def(def_id) | Res::SelfTyAlias { alias_to: def_id } => {
                    let scheme = match self.item_schemes.get(def_id) {
                        Some(scheme) => scheme.clone(),
                        None => return Ty::Error,
                    };
                    let explicit_args = path
                        .segments
                        .last()
                        .and_then(|seg| seg.generic_args.as_ref());
                    if matches!(scheme.body, Ty::Adt(_, _)) {
                        match explicit_args {
                            Some(args) => self
                                .instantiate_with_explicit_args(*def_id, &scheme, args, path.span),
                            None if scheme.vars.is_empty() => self.icx.instantiate(&scheme),
                            None => Ty::Adt(*def_id, None),
                        }
                    } else {
                        self.instantiate_fn_scheme(*def_id, &scheme, explicit_args, path.span)
                    }
                }
                Res::Local(id) | Res::GenericParam(id) => match self.env.get(id) {
                    Some(scheme) => self.icx.instantiate(scheme),
                    None => Ty::Error,
                },
                Res::PrimTy(prim) => Ty::Prim(*prim),
                Res::Err => Ty::Error,
            },
            QPath::TypeRelative { .. } => Ty::Error,
        }
    }

    fn try_complete_generic_args(
        &self,
        def_id: DefId,
        args: &mut ThinVec<hir::Ty>,
        expected_len: usize,
    ) -> bool {
        match args.len().cmp(&expected_len) {
            Ordering::Equal => true,
            Ordering::Greater => false,
            Ordering::Less => {
                let Some(info) = self.coherence.generic_params.get(&def_id) else {
                    return false;
                };
                for i in args.len()..expected_len {
                    match info.defaults.get(i) {
                        Some(Some(default_ty)) => args.push(default_ty.clone()),
                        _ => return false,
                    }
                }
                true
            }
        }
    }

    fn instantiate_with_explicit_args(
        &mut self,
        def_id: DefId,
        scheme: &Scheme,
        explicit_args: &ThinVec<hir::Ty>,
        span: Span,
    ) -> Ty {
        let provided = explicit_args.len();
        let mut args = explicit_args.clone();
        if !self.try_complete_generic_args(def_id, &mut args, scheme.vars.len()) {
            builders::emit_at(
                self.ctx,
                span,
                self.module_id,
                diag::UnexpectedGenericArgs,
                diag_params! {
                    expected = scheme.vars.len(),
                    s = if scheme.vars.len() == 1 { "" } else { "s" },
                    found = provided,
                },
            );
            return Ty::Error;
        }
        let mut mapping = FxHashMap::default();
        for &v in &scheme.vars {
            mapping.insert(v, self.icx.next_ty_var());
        }
        let parent_var_count = self
            .coherence
            .assoc_to_parent
            .get(&def_id)
            .and_then(|parent_def_id| self.coherence.generic_params.get(parent_def_id))
            .map(|parent_info| parent_info.hir_ids.len())
            .unwrap_or(0);
        let method_vars = &scheme.vars[parent_var_count..];
        if let Some(info) = self.coherence.generic_params.get(&def_id) {
            for (hir_id, &v) in info.hir_ids.iter().zip(method_vars) {
                if let Some(&fresh) = mapping.get(&v) {
                    self.icx.hir_id_to_ty_var.entry(*hir_id).or_insert(fresh);
                }
            }
        }
        for (hir_arg_ty, &v) in args.iter().zip(method_vars) {
            let arg_ty = Ty::from_hir(self.icx, hir_arg_ty);
            self.node_types.insert(hir_arg_ty.hir_id, arg_ty.clone());
            let &fresh = mapping.get(&v).expect("fresh var exists");
            unify(self.icx, &Ty::Var(fresh), &arg_ty, span, self.module_id).or_push_err(self.icx);
        }
        self.icx.instantiate_with(&scheme.body, &mapping)
    }

    fn instantiate_fn_scheme(
        &mut self,
        def_id: DefId,
        scheme: &Scheme,
        explicit_args: Option<&ThinVec<hir::Ty>>,
        span: Span,
    ) -> Ty {
        match explicit_args {
            Some(args) => self.instantiate_with_explicit_args(def_id, scheme, args, span),
            None => self.icx.instantiate(scheme),
        }
    }

    fn qpath_recv_ty(&mut self, qpath: &QPath) -> Option<Ty> {
        let base = match qpath {
            QPath::Resolved(path) => match &path.res {
                Res::Def(def_id) | Res::SelfTyAlias { alias_to: def_id } => {
                    match self.item_schemes.get(def_id).cloned() {
                        Some(scheme) => {
                            if let Some(explicit_args) = path
                                .segments
                                .last()
                                .and_then(|seg| seg.generic_args.as_ref())
                            {
                                self.instantiate_with_explicit_args(
                                    *def_id,
                                    &scheme,
                                    explicit_args,
                                    path.span,
                                )
                            } else {
                                if matches!(scheme.body, Ty::Adt(_, _)) {
                                    Ty::Adt(*def_id, None)
                                } else {
                                    self.icx.instantiate(&scheme)
                                }
                            }
                        }
                        None => Ty::Error,
                    }
                }
                _ => return None,
            },
            QPath::TypeRelative { qself, .. } => return self.qpath_recv_ty(qself),
        };
        let base = self.icx.resolve(&base);
        if matches!(base, Ty::Adt(_, _)) {
            Some(base)
        } else {
            None
        }
    }

    fn check_binary(&mut self, left: &Expr, op: BinOp, right: &Expr) -> Ty {
        let left_span = left.span;
        let right_span = right.span;
        let left = self.check_expr(left);
        let right = self.check_expr(right);
        match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                unify(self.icx, &left, &right, left_span, self.module_id).or_push_err(self.icx);
                Ty::Prim(PrimTy::Bool)
            }
            BinOp::And | BinOp::Or => {
                let bool_ty = Ty::Prim(PrimTy::Bool);
                unify(self.icx, &bool_ty, &left, left_span, self.module_id).or_push_err(self.icx);
                unify(self.icx, &bool_ty, &right, right_span, self.module_id).or_push_err(self.icx);
                bool_ty
            }
            _ => {
                if !left.is_numeric(self.icx) {
                    builders::emit_at(
                        self.ctx,
                        left_span,
                        self.module_id,
                        diag::NonNumericOperand,
                        diag_params! { operator = op },
                    );
                    return Ty::Error;
                } else if !right.is_numeric(self.icx) {
                    builders::emit_at(
                        self.ctx,
                        right_span,
                        self.module_id,
                        diag::NonNumericOperand,
                        diag_params! { operator = op },
                    );
                    return Ty::Error;
                }

                unify(self.icx, &left, &right, left_span, self.module_id).or_push_err(self.icx);
                left
            }
        }
    }

    fn check_unary(&mut self, op: UnOp, right: &Expr) -> Ty {
        let right_span = right.span;
        let right = self.check_expr(right);
        match op {
            UnOp::Not => {
                let bool_ty = Ty::Prim(PrimTy::Bool);
                unify(self.icx, &bool_ty, &right, right_span, self.module_id).or_push_err(self.icx);
                bool_ty
            }
            UnOp::Neg => {
                let resolved = self.icx.resolve(&right);
                if !resolved.is_numeric(self.icx) {
                    builders::emit_at(
                        self.ctx,
                        right_span,
                        self.module_id,
                        diag::NonNumericOperand,
                        diag_params! { operator = op },
                    );
                    return Ty::Error;
                }
                resolved
            }
        }
    }

    fn check_reference(&mut self, expr: &Expr, mutability: Mutability) -> Ty {
        let expr = self.check_expr(expr);
        Ty::Ptr(expr.into_box(), mutability)
    }

    fn check_dereference(&mut self, expr: &Expr) -> Ty {
        let span = expr.span;
        let left = self.check_expr(expr);
        match left {
            Ty::Ptr(inner, _) => (*inner).clone(),
            _ => {
                builders::emit_at(
                    self.ctx,
                    span,
                    self.module_id,
                    diag::DerefNonPointer,
                    diag_params! { type = ty_display(&left, self.resolver, &self.ctx.interner) },
                );
                Ty::Error
            }
        }
    }

    fn def_ty_var_subst(&self, def: DefId, args: &[Ty]) -> FxHashMap<TyVarId, Ty> {
        let mut subst = FxHashMap::default();
        if let Some(info) = self.coherence.generic_params.get(&def) {
            for (hir_id, arg_ty) in info.hir_ids.iter().zip(args.iter()) {
                if let Some(&registered_var) = self.icx.hir_id_to_ty_var.get(hir_id) {
                    subst.insert(registered_var, arg_ty.clone());
                }
            }
        }
        subst
    }

    fn check_struct_init(
        &mut self,
        def: DefId,
        generic_args: &Option<ThinVec<hir::Ty>>,
        fields: &ThinVec<(Ident, Expr)>,
        span: Span,
    ) -> Ty {
        self.register_if_generic_def(def);

        let param_hir_ids = &self
            .coherence
            .generic_params
            .get(&def)
            .expect("struct exists")
            .hir_ids;

        let fresh_var_map: FxHashMap<HirId, TyVarId> = param_hir_ids
            .iter()
            .map(|&hir_id| (hir_id, self.icx.next_ty_var()))
            .collect();

        let (struct_ty, ty_var_subst) = if let Some(generic_args) = generic_args {
            let provided = generic_args.len();
            let mut hir_args = generic_args.clone();
            if !self.try_complete_generic_args(def, &mut hir_args, param_hir_ids.len()) {
                builders::emit_at(
                    self.ctx,
                    span,
                    self.module_id,
                    diag::UnexpectedGenericArgs,
                    diag_params! {
                        expected = param_hir_ids.len(),
                        s = if param_hir_ids.len() == 1 { "" } else { "s" },
                        found = provided,
                    },
                );
                return Ty::Error;
            }
            let args: ThinVec<Ty> = hir_args
                .iter()
                .map(|arg| {
                    let arg_ty = Ty::from_hir(self.icx, arg);
                    self.node_types.insert(arg.hir_id, arg_ty.clone());
                    arg_ty
                })
                .collect();
            for (arg, hir_id) in args.iter().zip(param_hir_ids.iter()) {
                if let Some(&fresh) = fresh_var_map.get(hir_id) {
                    unify(self.icx, &Ty::Var(fresh), arg, span, self.module_id)
                        .or_push_err(self.icx);
                }
            }
            let subst = self.def_ty_var_subst(def, &args);
            (Ty::Adt(def, Some(args)), subst)
        } else {
            if param_hir_ids.is_empty() {
                (Ty::Adt(def, None), FxHashMap::default())
            } else {
                let args: ThinVec<Ty> = param_hir_ids
                    .iter()
                    .map(|&hir_id| Ty::Var(*fresh_var_map.get(&hir_id).expect("fresh var exists")))
                    .collect();
                self.stash_generic_defaults(def, &fresh_var_map);
                let subst = self.def_ty_var_subst(def, &args);
                (Ty::Adt(def, Some(args)), subst)
            }
        };

        self.check_struct_fields(def, struct_ty, fields, span, &ty_var_subst)
    }

    fn stash_generic_defaults(&mut self, def: DefId, fresh_var_map: &FxHashMap<HirId, TyVarId>) {
        let info = match self.coherence.generic_params.get(&def) {
            Some(info) => info,
            None => return,
        };
        let subst: FxHashMap<TyVarId, Ty> = info
            .hir_ids
            .iter()
            .filter_map(|hir_id| {
                fresh_var_map.get(hir_id).and_then(|&fresh| {
                    self.icx
                        .hir_id_to_ty_var
                        .get(hir_id)
                        .map(|&def_var| (def_var, Ty::Var(fresh)))
                })
            })
            .collect();
        for (hir_id, default) in info.hir_ids.iter().zip(info.defaults.iter()) {
            if let Some(default_ty) = default
                && let Some(&fresh) = fresh_var_map.get(hir_id)
            {
                let default_ty = Ty::from_hir(self.icx, default_ty);
                let default_ty = substitute_ty_vars(&default_ty, &subst);
                self.icx.add_generic_default(fresh, default_ty);
            }
        }
    }

    fn check_struct_fields(
        &mut self,
        def: DefId,
        struct_ty: Ty,
        fields: &ThinVec<(Ident, Expr)>,
        span: Span,
        ty_var_subst: &FxHashMap<TyVarId, Ty>,
    ) -> Ty {
        let field_table = self
            .coherence
            .struct_fields
            .get(&def)
            .cloned()
            .unwrap_or_default();

        let sym_to_span: FxHashMap<Symbol, Span> = fields
            .iter()
            .map(|(name, _)| (name.value, name.span))
            .collect();
        let init_names: FxHashSet<Symbol> = fields.iter().map(|(name, _)| name.value).collect();
        let struct_names: FxHashSet<Symbol> = field_table.keys().copied().collect();

        for name in init_names.difference(&struct_names) {
            let field = self.ctx.interner.lookup(*name).to_string();
            builders::emit_at(
                self.ctx,
                *sym_to_span.get(name).expect("field exists"),
                self.module_id,
                diag::UnknownField,
                diag_params! {
                    field = field,
                    type = ty_display(&struct_ty, self.resolver, &self.ctx.interner)
                },
            );
        }

        for name in struct_names.difference(&init_names) {
            let field = self.ctx.interner.lookup(*name).to_string();
            builders::emit_at(
                self.ctx,
                span,
                self.module_id,
                diag::MissingField,
                diag_params! {
                    field = field,
                    type = ty_display(&struct_ty, self.resolver, &self.ctx.interner)
                },
            );
        }

        for (name, expr) in fields {
            let expr_span = expr.span;
            let expr = self.check_expr(expr);
            if let Some((hir_field_ty, _)) = field_table.get(&name.value) {
                let mut field_ty = Ty::from_hir(self.icx, hir_field_ty);
                if !ty_var_subst.is_empty() {
                    field_ty = substitute_ty_vars(&field_ty, ty_var_subst);
                }
                if let Err(err) = unify(self.icx, &field_ty, &expr, expr_span, self.module_id) {
                    self.icx.errors.push(err);
                }
            }
        }

        struct_ty
    }

    fn check_array_init(&mut self, contents: &ThinVec<Expr>, span: Span) -> Ty {
        let mut elem_ty = None;
        for expr in contents {
            let expr_ty = self.check_expr(expr);
            if let Some(elem_ty) = &elem_ty {
                if let Err(err) = unify(self.icx, elem_ty, &expr_ty, expr.span, self.module_id) {
                    self.report_type_error(err);
                }
            } else {
                elem_ty = Some(expr_ty);
            }
        }
        let elem_ty = elem_ty.unwrap_or_else(|| {
            let var = self.icx.next_ty_var_at(
                self.icx.current_level(),
                TyVarSource::EmptyArray,
                Some(span),
                Some(self.module_id),
            );
            Ty::Var(var)
        });
        Ty::Slice(elem_ty.into_box())
    }

    fn check_block(&mut self, block: &Block) -> BlockTyRes {
        self.env.push();
        let mut break_ty = None;
        let mut diverged = false;
        for stmt in &block.stmts {
            if diverged {
                match &stmt.kind {
                    StmtKind::Let {
                        ty: hir_ty, init, ..
                    } => {
                        let ty = Ty::from_hir(self.icx, hir_ty);
                        self.node_types.insert(hir_ty.hir_id, ty);
                        if let Some(init) = init {
                            self.check_expr(init);
                        }
                    }
                    StmtKind::Expr(expr) => {
                        self.check_expr(expr);
                    }
                }
                continue;
            }
            match &stmt.kind {
                StmtKind::Let {
                    ty: hir_ty,
                    init,
                    local,
                    ..
                } => {
                    let ty = Ty::from_hir(self.icx, hir_ty);
                    self.node_types.insert(hir_ty.hir_id, ty.clone());
                    self.icx.push_level();
                    let init_span = init.as_ref().map(|e| e.span).unwrap_or(stmt.span);
                    let bound = init
                        .as_ref()
                        .map(|expr| self.check_expr(expr))
                        .unwrap_or_else(|| ty.clone());
                    if let Err(err) = unify(self.icx, &ty, &bound, init_span, self.module_id) {
                        self.icx.errors.push(err);
                    }
                    let scope = self.icx.current_level();
                    let parent = scope.saturating_sub(1);
                    let quantified = self.icx.generalize(&ty, parent);
                    let scheme = Scheme {
                        vars: quantified,
                        body: ty.clone(),
                    };
                    self.local_schemes.insert(*local, scheme.clone());
                    self.env.insert(*local, scheme);
                    self.icx.pop_level();
                    if let Some(init) = init {
                        self.collect_break_ty_from_expr(init, &mut break_ty, stmt.span);
                    }
                }
                StmtKind::Expr(expr) => {
                    self.collect_break_ty_from_expr(expr, &mut break_ty, expr.span);
                    let expr_ty = self.check_expr(expr);
                    if expr_ty == Ty::Never {
                        diverged = true;
                    }
                }
            }
        }
        let mut tail_ty = Ty::Prim(PrimTy::Void);
        if diverged {
            if let Some(tail) = &block.tail {
                self.check_expr(tail);
            }
            tail_ty = Ty::Never;
        } else if let Some(tail) = &block.tail {
            tail_ty = self.check_expr(tail);
            self.collect_break_ty_from_expr(tail, &mut break_ty, tail.span);
        }
        self.env.pop();
        BlockTyRes {
            tail: tail_ty,
            early: break_ty,
        }
    }

    fn collect_break_ty_from_block(
        &mut self,
        block: &Block,
        break_ty: &mut Option<Ty>,
        span: Span,
    ) {
        for stmt in &block.stmts {
            match &stmt.kind {
                StmtKind::Expr(expr) => {
                    self.collect_break_ty_from_expr(expr, break_ty, span);
                }
                StmtKind::Let { init, .. } => {
                    if let Some(init) = init {
                        self.collect_break_ty_from_expr(init, break_ty, span);
                    }
                }
            }
        }
        if let Some(tail) = &block.tail {
            self.collect_break_ty_from_expr(tail, break_ty, span);
        }
    }

    fn collect_break_ty_from_expr(&mut self, expr: &Expr, break_ty: &mut Option<Ty>, span: Span) {
        match &expr.kind {
            ExprKind::Break(break_expr) => {
                let break_value_ty = break_expr
                    .as_ref()
                    .map_or(Ty::Prim(PrimTy::Void), |inner| self.check_expr(inner));

                if let Some(existing_break_ty) = break_ty
                    && let Err(err) = unify(
                        self.icx,
                        existing_break_ty,
                        &break_value_ty,
                        span,
                        self.module_id,
                    )
                {
                    self.report_type_error(err);
                    return;
                }

                *break_ty = Some(break_value_ty);
            }
            ExprKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.collect_break_ty_from_block(then_branch, break_ty, span);
                if let Some(else_expr) = else_branch {
                    self.collect_break_ty_from_expr(else_expr, break_ty, span);
                }
            }
            ExprKind::Block(block) => {
                self.collect_break_ty_from_block(block, break_ty, span);
            }
            _ => {}
        }
    }

    fn check_loop(&mut self, block: &Block) -> Ty {
        let block_ty_res = self.check_block(block);

        let void_ty = Ty::Prim(PrimTy::Void);
        if let Err(err) = unify(
            self.icx,
            &void_ty,
            &block_ty_res.tail,
            block.span,
            self.module_id,
        ) {
            self.report_type_error(err);
        }

        block_ty_res.early.unwrap_or(Ty::Never)
    }

    fn lookup_adt_field(
        &mut self,
        struct_id: DefId,
        generic_args: &Option<ThinVec<Ty>>,
        member: Symbol,
        hir_id: HirId,
    ) -> Option<Ty> {
        self.register_if_generic_def(struct_id);
        let fields = self.coherence.struct_fields.get(&struct_id)?;
        let (hir_field_ty, index) = fields.get(&member)?;
        self.member_res
            .insert(hir_id, MemberRes::Field { index: *index });
        let mut field_ty = Ty::from_hir(self.icx, hir_field_ty);
        match generic_args {
            Some(generic_args) => {
                let subst = self.def_ty_var_subst(struct_id, generic_args);
                if !subst.is_empty() {
                    field_ty = substitute_ty_vars(&field_ty, &subst);
                }
            }
            None => {
                if let Some(info) = self.coherence.generic_params.get(&struct_id) {
                    let mut subst: FxHashMap<TyVarId, Ty> = FxHashMap::default();
                    let mut resolved: ThinVec<Ty> = ThinVec::new();
                    let mut has_missing = false;
                    for (i, default) in info.defaults.iter().enumerate() {
                        match default {
                            Some(ty) => {
                                let mut ty = Ty::from_hir(self.icx, ty);
                                if !subst.is_empty() {
                                    ty = substitute_ty_vars(&ty, &subst);
                                }
                                if let Some(&var) = self.icx.hir_id_to_ty_var.get(&info.hir_ids[i])
                                {
                                    subst.insert(var, ty.clone());
                                }
                                resolved.push(ty);
                            }
                            None => {
                                has_missing = true;
                                break;
                            }
                        }
                    }
                    if !has_missing {
                        let subst = self.def_ty_var_subst(struct_id, &resolved);
                        if !subst.is_empty() {
                            field_ty = substitute_ty_vars(&field_ty, &subst);
                        }
                    }
                }
            }
        }
        Some(field_ty)
    }

    fn check_member_access(
        &mut self,
        member: Symbol,
        base: &Expr,
        expr_span: Span,
        hir_id: HirId,
    ) -> Ty {
        let member_span = Span::new(base.span.end() + 1, expr_span.end());
        let recv_ty = self.check_expr(base);
        let recv_ty = self.icx.resolve(&recv_ty);

        // TODO: Maybe run in a loop to dereference types like `&&T`
        let recv_ty = if let Ty::Ptr(inner, _) = &recv_ty {
            self.adjustments
                .entry(base.hir_id)
                .or_default()
                .push(Adjustment::AutoDeref);
            inner.as_ref()
        } else {
            &recv_ty
        };

        match recv_ty {
            Ty::Adt(struct_id, generic_args) => {
                if let Some(field_ty) =
                    self.lookup_adt_field(*struct_id, generic_args, member, hir_id)
                {
                    return field_ty;
                }

                let field = self.ctx.interner.lookup(member).to_string();
                builders::emit_at(
                    self.ctx,
                    member_span,
                    self.module_id,
                    diag::UnknownField,
                    diag_params! {
                        field = field,
                        type = ty_display(recv_ty, self.resolver, &self.ctx.interner)
                    },
                );
            }
            Ty::Slice(elem) => {
                let interner = &self.ctx.interner;
                if interner.lookup(member) == "len" {
                    self.member_res
                        .insert(hir_id, MemberRes::Field { index: 1 });
                    return Ty::Prim(PrimTy::Uint(UintTy::Usize));
                }
                if interner.lookup(member) == "ptr" {
                    self.member_res
                        .insert(hir_id, MemberRes::Field { index: 0 });
                    return Ty::Ptr(elem.clone(), Mutability::Constant);
                }
                let field = self.ctx.interner.lookup(member).to_string();
                builders::emit_at(
                    self.ctx,
                    member_span,
                    self.module_id,
                    diag::UnknownFieldInSlice,
                    diag_params! { field = field },
                );
            }
            _ => {
                let field = self.ctx.interner.lookup(member).to_string();
                builders::emit_at(
                    self.ctx,
                    member_span,
                    self.module_id,
                    diag::TypeWithNoFields,
                    diag_params! {
                        field = field,
                        type = ty_display(recv_ty, self.resolver, &self.ctx.interner)
                    },
                );
            }
        }
        Ty::Error
    }

    fn check_index(&mut self, base: &Expr, index: &Expr, expr_span: Span, _hir_id: HirId) -> Ty {
        let base_ty = self.check_expr(base);
        let base = self.icx.resolve(&base_ty);
        match base {
            Ty::Slice(elem) | Ty::Array(elem, _) => {
                let index_ty = self.check_expr(index);
                let usize_ty = Ty::Prim(PrimTy::Uint(UintTy::Usize));
                if let Err(err) = unify(self.icx, &usize_ty, &index_ty, index.span, self.module_id)
                {
                    self.report_type_error(err);
                }
                *elem.clone()
            }
            _ => {
                self.check_expr(index);
                builders::emit_at(
                    self.ctx,
                    expr_span,
                    self.module_id,
                    diag::CannotIndex,
                    diag_params! { type = ty_display(&base, self.resolver, &self.ctx.interner) },
                );
                Ty::Error
            }
        }
    }

    fn report_type_error(&mut self, err: UnifyError) {
        emit_unify_error(&err, self.resolver, self.ctx, self.icx);
    }
}

pub(super) fn emit_unify_error(
    err: &UnifyError,
    resolver: &ResolverOutputs,
    ctx: &mut Ctx,
    icx: &InferCtx,
) {
    match err {
        UnifyError::Mismatch {
            expected,
            found,
            span,
            module_id,
        } => {
            let expected = icx.resolve(expected);
            let found = icx.resolve(found);
            let expected_str = ty_display(&expected, resolver, &ctx.interner);
            let found_str = ty_display(&found, resolver, &ctx.interner);
            let info = generic_mismatch_info(&expected, &found, resolver, &ctx.interner);
            if let Some(info) = info {
                builders::emit_at_with_info(
                    ctx,
                    *span,
                    *module_id,
                    &info,
                    diag::TypeMismatch,
                    diag_params! {
                        expected = expected_str,
                        found = found_str
                    },
                );
            } else {
                builders::emit_at(
                    ctx,
                    *span,
                    *module_id,
                    diag::TypeMismatch,
                    diag_params! {
                        expected = expected_str,
                        found = found_str
                    },
                );
            }
        }
        UnifyError::OccursCheck {
            span, module_id, ..
        } => {
            builders::emit_at(ctx, *span, *module_id, diag::RecursiveType, diag_params! {});
        }
    };
}

fn generic_mismatch_info(
    expected: &Ty,
    found: &Ty,
    resolver: &ResolverOutputs,
    interner: &Interner,
) -> Option<String> {
    match (expected, found) {
        (Ty::Adt(d1, Some(g1)), Ty::Adt(d2, Some(g2))) if d1 == d2 && g1.len() != g2.len() => {
            let name = resolver.defs[d1.0 as usize]
                .name
                .map(|sym| interner.lookup(sym).to_string())
                .unwrap_or_else(|| format!("Struct#{}", d1.0));
            Some(format!(
                "struct `{name}` has {} generic parameter{}, but {} {} provided",
                g1.len(),
                if g1.len() == 1 { "" } else { "s" },
                g2.len(),
                if g2.len() == 1 { "was" } else { "were" },
            ))
        }
        _ => None,
    }
}

fn ty_display(ty: &Ty, resolver: &ResolverOutputs, interner: &Interner) -> String {
    match ty {
        Ty::Var(id) => format!("Var#{}", id),
        Ty::Prim(p) => p.name_str().to_string(),
        Ty::Ptr(inner, m) => format!(
            "&{}{}",
            if matches!(m, crate::ast::Mutability::Mutable) {
                "mut "
            } else {
                ""
            },
            ty_display(inner, resolver, interner)
        ),
        Ty::Slice(inner) => format!("[]{}", ty_display(inner, resolver, interner)),
        Ty::Array(inner, n) => format!("[{}]{}", n, ty_display(inner, resolver, interner)),
        Ty::Fn { params, ret } => {
            let ps: Vec<String> = params
                .iter()
                .map(|t| ty_display(t, resolver, interner))
                .collect();
            format!(
                "({}) -> {}",
                ps.join(", "),
                ty_display(ret, resolver, interner)
            )
        }
        Ty::Tuple(elements) => {
            let es: Vec<String> = elements
                .iter()
                .map(|t| ty_display(t, resolver, interner))
                .collect();
            format!("({})", es.join(", "))
        }
        Ty::Adt(d, generics) => {
            let name = resolver.defs[d.0 as usize]
                .name
                .map(|sym| interner.lookup(sym).to_string())
                .unwrap_or_else(|| format!("Struct#{}", d.0));
            format!(
                "{}{}",
                name,
                generics_to_string(generics.as_ref(), resolver, interner)
            )
        }
        Ty::Never => "!".to_string(),
        Ty::MethodCallee => "<method-callee>".to_string(),
        Ty::Error => "<error>".to_string(),
    }
}

fn generics_to_string(
    generics: Option<&ThinVec<Ty>>,
    resolver: &ResolverOutputs,
    interner: &Interner,
) -> String {
    if generics.is_none() {
        return String::new();
    }
    let generics = generics.expect("generics exists");
    let mut s = String::new();
    s.push_str("::<");
    for (i, ty_var) in generics.iter().enumerate() {
        if i > 0 {
            s.push_str(", ");
        }
        s.push_str(&ty_display(ty_var, resolver, interner));
    }
    s.push('>');
    s
}
