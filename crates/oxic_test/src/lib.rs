#![cfg_attr(feature = "nightly", feature(proc_macro_tracked_path))]

mod parser;

use std::fs;
use std::path::Path;

use anyhow::Result;
use proc_macro::{Span, TokenStream};
use proc_macro2::{Span as Span2, TokenStream as TokenStream2};
use quote::quote;
use syn::{Ident, LitStr};

#[cfg(feature = "nightly")]
use proc_macro::tracked::path as track_path;

#[cfg(not(feature = "nightly"))]
fn track_path(_path: &Path) {}

#[proc_macro]
pub fn oxic_test(_input: TokenStream) -> TokenStream {
    let Some(source_path) = Span::call_site().local_file() else {
        // rust-analyzer doesn't support getting the source file path, so we just return a test that
        // always fails. https://github.com/rust-lang/rust-analyzer/issues/15950
        return quote! {
            #[test]
            fn oxic_test_fallback() {
                panic!("oxic_test: failed to get source file path");
            }
        }
        .into();
    };
    let mut integration_dir = source_path;
    integration_dir.pop();
    integration_dir.push("integration");

    if !integration_dir.is_dir() {
        panic!("integration directory not found at {:?}", integration_dir);
    }

    let mut tests = TokenStream2::new();
    collect_oxi_files(&integration_dir, &integration_dir, &mut tests)
        .unwrap_or_else(|e| panic!("Failed to collect .oxi files: {e}"));

    tests.into()
}

fn collect_oxi_files(base: &Path, dir: &Path, tests: &mut TokenStream2) -> Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();

        track_path(&path);
        if path.is_dir() {
            let name = path.file_name().unwrap().to_str().unwrap();
            if name == "auxiliary" {
                continue;
            }
            collect_oxi_files(base, &path, tests)?;
        } else if path.extension().is_some_and(|e| e == "oxi") {
            let source = fs::read_to_string(&path)?;
            let relative = path.strip_prefix(base).unwrap();
            let name = relative
                .with_extension("")
                .to_str()
                .unwrap()
                .replace([std::path::MAIN_SEPARATOR, '-'], "_");
            let test = test_case_from_source(base, &name, &source)?;
            tests.extend(test);
        }
    }
    Ok(())
}

fn test_case_from_source(dir: &Path, name: &str, source: &str) -> Result<TokenStream2> {
    let test_case = parser::parse_file(source)?;

    let should_succeed = test_case.expected_errors.is_empty();
    let source = LitStr::new(source, Span2::call_site());
    let test_name = Ident::new(name, Span2::call_site());

    let expect_errors: TokenStream2 = test_case
        .expected_errors
        .iter()
        .map(|err| {
            let err = LitStr::new(err, Span2::call_site());
            quote! { .expect_error(#err) }
        })
        .collect();

    let auxiliary_modules = get_auxiliary_modules(dir, test_case.auxiliary_modules);
    let auxiliary_modules: TokenStream2 = auxiliary_modules
        .iter()
        .map(|(name, source)| {
            let filename = format!("{name}.oxi");
            let filename = LitStr::new(&filename, Span2::call_site());
            let source = LitStr::new(source, Span2::call_site());
            quote! { .add_source(#filename, #source) }
        })
        .collect();

    Ok(quote! {
        #[test]
        fn #test_name() {
            crate::common::with(|ctx| {
                ctx.add_source("main.oxi", #source)
                   .succeeds(#should_succeed)
                   #expect_errors
                   #auxiliary_modules;
            })
        }
    })
}

fn get_auxiliary_modules(dir: &Path, modules: Vec<String>) -> Vec<(String, String)> {
    let auxiliary_dir = dir.join("auxiliary");

    modules
        .into_iter()
        .map(|module| {
            let path = auxiliary_dir.join(format!("{module}.oxi"));
            track_path(&path);
            let source = std::fs::read_to_string(&path)
                .unwrap_or_else(|_| panic!("Failed to read auxiliary module at {:?}", path));
            (module, source)
        })
        .collect()
}
