use thin_vec::ThinVec;

use crate::ast::visit::{VisitAction, Visitable, Visitor};
use crate::ast::{
    AssocItem, AssocItemKind, ImportTree, ImportTreeKind, Item, ItemKind, NodeId, Path,
    PathSegment, Visibility, path_segments_to_string,
};
use crate::diag_params;
use crate::errors::{CompilationError, builders};
use crate::hir::{DefId, ModuleId};
use crate::interner::Symbol;
use crate::resolve::path::PathError;
use crate::resolve::{Def, DefKind, NameBinding, NameResolution, PendingImport, Resolver, diag};
use crate::span::Span;

impl<'a, 'ctx> Resolver<'a, 'ctx> {
    /// Allocates a definition and registers its name resolution
    fn create_def(
        &mut self,
        id: NodeId,
        name: Symbol,
        kind: DefKind,
        visibility: Visibility,
        span: Span,
    ) -> DefId {
        let def_id = self.alloc_def(id, Some(name), kind, Some(visibility), span);
        let binding = NameBinding { def_id, visibility };
        self.current_module_mut()
            .resolutions
            .insert(name, NameResolution::non_glob_import(binding));
        def_id
    }

    /// Allocates a definition without registering its name resolution
    fn alloc_def(
        &mut self,
        id: NodeId,
        name: Option<Symbol>,
        kind: DefKind,
        visibility: Option<Visibility>,
        span: Span,
    ) -> DefId {
        let idx = self.defs.len() as u32;
        let def_id = DefId(idx);
        self.defs.push(Def {
            name,
            kind,
            visibility,
            span,
        });
        self.def_map.insert(id, def_id);
        def_id
    }

    fn register_import(&mut self, import_item: ImportTree, visibility: Visibility) {
        self.pending_imports.push(PendingImport {
            import_item,
            visibility,
            module: ModuleId(self.module_idx as u32),
        });
    }

    fn collect_items_for_node(&self, node_idx: usize) -> ThinVec<Item> {
        let node = &self.module_tree.nodes[node_idx];
        match node.ast_idx {
            Some(ast_idx) => self.asts[ast_idx].items.clone(),
            None => node.inline_body.clone().unwrap_or_default(),
        }
    }

    pub(super) fn traverse_tree<F>(&mut self, mut visitor: F)
    where
        F: FnMut(&mut Self, usize, &[Item]),
    {
        self.traverse_tree_rec(0, &mut visitor);
    }

    fn traverse_tree_rec<F>(&mut self, node_idx: usize, visitor: &mut F)
    where
        F: FnMut(&mut Self, usize, &[Item]),
    {
        let children: Vec<usize> = self.module_tree.nodes[node_idx].children.clone();
        let items = self.collect_items_for_node(node_idx);
        visitor(self, node_idx, &items);
        for &child in &children {
            self.traverse_tree_rec(child, visitor);
        }
    }

    pub(super) fn collect_definitions(&mut self) {
        self.traverse_tree(|this, node_idx, items| {
            this.module_idx = node_idx;
            for item in items {
                item.visit(&mut DefCollector::new(this));
            }
        });
    }

    pub(super) fn build_graph(&mut self) {
        self.traverse_tree(|this, node_idx, items| {
            this.module_idx = node_idx;
            for item in items {
                item.visit(&mut ImportCollector::new(this));
            }
        });
    }

    pub(super) fn resolve_imports(&mut self) {
        let mut progress = true;
        while progress && !self.pending_imports.is_empty() {
            progress = false;

            // iterate with index so we can remove resolved entries in-place
            let mut i = 0usize;
            while i < self.pending_imports.len() {
                // try resolve; if resolved we remove from pending and set progress = true
                match self.resolve_import(i) {
                    ResolutionStatus::Resolved => {
                        self.pending_imports.swap_remove(i);
                        progress = true;
                        continue;
                    }
                    ResolutionStatus::Failed => {
                        self.pending_imports.swap_remove(i);
                        progress = true;
                        continue;
                    }
                    ResolutionStatus::Pending => {
                        // cannot resolve yet: keep item for next pass
                        i += 1;
                        continue;
                    }
                }
            }
        }

        if !self.pending_imports.is_empty() {
            for pi in &self.pending_imports {
                let last_seg = pi.import_item.prefix.segments.last().expect("non-empty");
                let module_prefix =
                    &pi.import_item.prefix.segments[..pi.import_item.prefix.segments.len() - 1];
                let module_path = path_segments_to_string(module_prefix, self.ctx);
                let name = self.ctx.interner.lookup(last_seg.ident.value).to_string();
                if module_path.is_empty() {
                    builders::emit_at(
                        self.ctx,
                        last_seg.span,
                        pi.module,
                        diag::ItemNotFound,
                        diag_params! { name = name },
                    );
                } else {
                    builders::emit_at(
                        self.ctx,
                        last_seg.span,
                        pi.module,
                        diag::ItemNotFoundInModule,
                        diag_params! { name = name, module = module_path },
                    );
                }
            }
        }
    }

    fn resolve_import(&mut self, idx: usize) -> ResolutionStatus {
        let pi = &self.pending_imports[idx];

        match &pi.import_item.kind {
            ImportTreeKind::Simple(_) => self.resolve_simple_import(idx),
            ImportTreeKind::Glob => self.resolve_glob_import(idx),
            // Nested imports are flattened during the build_graph() stage
            ImportTreeKind::Nested { .. } => unreachable!(),
        }
    }

    fn resolve_glob_import(&mut self, idx: usize) -> ResolutionStatus {
        let pi = &self.pending_imports[idx];
        let prefix = &pi.import_item.prefix;
        let segments = &prefix.segments;

        let current_module = pi.module.0 as usize;
        let module_node_idx = match self.get_module_node_idx(current_module, segments, pi) {
            Ok(idx) => idx,
            Err(err) => {
                self.ctx.errors.add(err, self.ctx.enable_printing);
                return ResolutionStatus::Failed;
            }
        };

        self.module_idx = current_module;
        // If this fell back to glob import when best_binding() is private, it could cause weird
        // behaviour, so always choose the best_binding(), even if it's private
        let public_bindings: Vec<_> = self.modules[module_node_idx]
            .resolutions
            .iter()
            .map(|(&sym, res)| (sym, res.best_binding()))
            .filter(|(_, binding)| binding.visibility == Visibility::Public)
            .collect();
        for (sym, binding) in public_bindings {
            self.current_module_mut()
                .resolutions
                .insert(sym, NameResolution::glob_import(binding));
        }

        ResolutionStatus::Resolved
    }

    fn resolve_simple_import(&mut self, idx: usize) -> ResolutionStatus {
        let pi = &self.pending_imports[idx];
        let prefix = &pi.import_item.prefix;
        let segments = &prefix.segments;
        let ImportTreeKind::Simple(rename) = &pi.import_item.kind else {
            unreachable!()
        };

        if segments.len() < 2 {
            builders::emit_at(
                self.ctx,
                pi.import_item.span,
                pi.module,
                diag::ImportSingleSegment,
                diag_params! {},
            );
            return ResolutionStatus::Failed;
        }

        let local_sym = rename
            .as_ref()
            .map(|r| r.value)
            .unwrap_or(unsafe { segments.last().unwrap_unchecked().ident.value });
        let target_sym = &segments[segments.len() - 1].ident.value;

        let current_module = pi.module.0 as usize;

        // Walk path segments (excluding last which is the symbol name) to find target module
        let module_prefix = &segments[..segments.len() - 1];
        let module_node_idx = match self.get_module_node_idx(current_module, module_prefix, pi) {
            Ok(idx) => idx,
            Err(err) => {
                self.ctx.errors.add(err, self.ctx.enable_printing);
                return ResolutionStatus::Failed;
            }
        };

        let target_res = self.modules[module_node_idx]
            .resolutions
            .get(target_sym)
            .copied();
        let Some(target_res) = target_res else {
            return ResolutionStatus::Pending;
        };

        let target_binding = target_res.best_binding();
        if target_binding.visibility != Visibility::Public {
            builders::emit_at(
                self.ctx,
                pi.import_item.span,
                pi.module,
                diag::ImportPrivateItem,
                diag_params! {},
            );
            return ResolutionStatus::Failed;
        }

        let binding = NameBinding {
            def_id: target_binding.def_id,
            visibility: pi.visibility,
        };

        self.module_idx = current_module;
        self.current_module_mut()
            .resolutions
            .insert(local_sym, NameResolution::non_glob_import(binding));

        ResolutionStatus::Resolved
    }

    fn get_module_node_idx(
        &self,
        current_module: usize,
        segments: &[PathSegment],
        pi: &PendingImport,
    ) -> Result<usize, CompilationError> {
        match self.resolve_module_path(current_module, segments) {
            Ok(idx) => Ok(idx),
            Err(err) => Err(match err {
                PathError::NoParentForSuper { span } => builders::prepare_diag_at(
                    self.ctx,
                    span,
                    pi.module,
                    &diag::NoParentForSuper,
                    diag_params! {},
                ),
                PathError::ModuleNotFound { name, span } => builders::prepare_diag_at(
                    self.ctx,
                    span,
                    pi.module,
                    &diag::ModuleNotFound,
                    diag_params! { name = name },
                ),
            }),
        }
    }
}

#[derive(Debug)]
struct DefCollector<'a, 'res, 'ctx> {
    resolver: &'a mut Resolver<'res, 'ctx>,
}

impl<'a, 'res, 'ctx> DefCollector<'a, 'res, 'ctx> {
    pub fn new(resolver: &'a mut Resolver<'res, 'ctx>) -> Self {
        Self { resolver }
    }
}

impl<'a, 'res, 'ctx> Visitor for DefCollector<'a, 'res, 'ctx> {
    fn visit_item(&mut self, item: &Item) -> VisitAction {
        match &item.kind {
            ItemKind::Const { name, .. } => {
                let def_id = self.resolver.create_def(
                    item.node_id,
                    name.value,
                    DefKind::Const,
                    item.visibility,
                    item.span,
                );
                self.resolver.register_def_to_module(def_id);
                VisitAction::SkipChildren
            }
            ItemKind::Struct { name, .. } => {
                let def_id = self.resolver.create_def(
                    item.node_id,
                    name.value,
                    DefKind::Struct,
                    item.visibility,
                    item.span,
                );
                self.resolver.register_def_to_module(def_id);
                VisitAction::Continue
            }
            ItemKind::Trait { name, .. } => {
                let def_id = self.resolver.create_def(
                    item.node_id,
                    name.value,
                    DefKind::Trait,
                    item.visibility,
                    item.span,
                );
                self.resolver.register_def_to_module(def_id);
                VisitAction::Continue
            }
            ItemKind::Impl { .. } => {
                let def_id =
                    self.resolver
                        .alloc_def(item.node_id, None, DefKind::Impl, None, item.span);
                self.resolver.register_def_to_module(def_id);
                VisitAction::Continue
            }
            ItemKind::Fn(f) => {
                let def_id = self.resolver.create_def(
                    item.node_id,
                    f.name.value,
                    DefKind::Function,
                    item.visibility,
                    item.span,
                );
                self.resolver.register_def_to_module(def_id);
                VisitAction::SkipChildren
            }
            ItemKind::Type { name, .. } => {
                let def_id = self.resolver.create_def(
                    item.node_id,
                    name.value,
                    DefKind::TypeAlias,
                    item.visibility,
                    item.span,
                );
                self.resolver.register_def_to_module(def_id);
                VisitAction::SkipChildren
            }
            ItemKind::Module { .. } => {
                let def_id =
                    self.resolver
                        .alloc_def(item.node_id, None, DefKind::Mod, None, item.span);
                self.resolver.register_def_to_module(def_id);
                VisitAction::SkipChildren
            }
            ItemKind::Import(_) => {
                let def_id =
                    self.resolver
                        .alloc_def(item.node_id, None, DefKind::Import, None, item.span);
                self.resolver.register_def_to_module(def_id);
                VisitAction::SkipChildren
            }
        }
    }

    fn visit_assoc_item(&mut self, item: &AssocItem) -> VisitAction {
        let (kind, name) = match &item.kind {
            AssocItemKind::Fn(f) => (DefKind::AssocFn, f.name.value),
            AssocItemKind::Type { name, .. } => (DefKind::AssocType, name.value),
        };
        let def_id = self.resolver.alloc_def(
            item.node_id,
            Some(name),
            kind,
            Some(item.visibility),
            item.span,
        );
        self.resolver.register_def_to_module(def_id);
        VisitAction::SkipChildren
    }
}

fn flatten_import_tree(tree: &ImportTree) -> Vec<ImportTree> {
    match &tree.kind {
        ImportTreeKind::Simple(_) | ImportTreeKind::Glob => {
            vec![tree.clone()]
        }
        ImportTreeKind::Nested { items, .. } => items
            .iter()
            .flat_map(|item| flatten_nested_item(&tree.prefix, item))
            .collect(),
    }
}

fn flatten_nested_item(parent_prefix: &Path, tree: &ImportTree) -> Vec<ImportTree> {
    match &tree.kind {
        ImportTreeKind::Simple(_) | ImportTreeKind::Glob => {
            let mut segments = parent_prefix.segments.clone();
            segments.extend(tree.prefix.segments.clone());
            let new_prefix = Path {
                segments,
                span: Span::new(parent_prefix.span.start(), tree.prefix.span.end()),
            };
            vec![ImportTree {
                prefix: new_prefix,
                kind: tree.kind.clone(),
                span: tree.span,
            }]
        }
        ImportTreeKind::Nested { items, .. } => {
            let mut segments = parent_prefix.segments.clone();
            segments.extend(tree.prefix.segments.clone());
            let extended_prefix = Path {
                segments,
                span: Span::new(parent_prefix.span.start(), tree.prefix.span.end()),
            };
            items
                .iter()
                .flat_map(|item| flatten_nested_item(&extended_prefix, item))
                .collect()
        }
    }
}

#[derive(Debug)]
struct ImportCollector<'a, 'res, 'ctx> {
    resolver: &'a mut Resolver<'res, 'ctx>,
}

impl<'a, 'res, 'ctx> ImportCollector<'a, 'res, 'ctx> {
    pub fn new(resolver: &'a mut Resolver<'res, 'ctx>) -> Self {
        Self { resolver }
    }
}

impl<'a, 'res, 'ctx> Visitor for ImportCollector<'a, 'res, 'ctx> {
    fn visit_item(&mut self, item: &Item) -> VisitAction {
        if let ItemKind::Import(tree) = &item.kind {
            let trees = flatten_import_tree(tree);
            for tree in trees {
                self.resolver.register_import(tree, item.visibility);
            }
        }
        VisitAction::SkipChildren
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResolutionStatus {
    /// Successfully resolved and applied to the module
    Resolved,
    /// Failed permanently
    Failed,
    /// Temporary failure (might succeed in later pass)
    Pending,
}
