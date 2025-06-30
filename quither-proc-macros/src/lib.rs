// Copyright 2021 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use ::proc_macro::TokenStream;
use ::proc_macro2::TokenStream as TokenStream2;
use ::quote::quote;
use ::std::collections::HashSet;
use ::syn::spanned::Spanned;
use ::syn::visit::{Visit, visit_ident, visit_path, visit_path_arguments};
use ::syn::visit_mut::{
    VisitMut, visit_expr_match_mut, visit_expr_mut, visit_item_impl_mut, visit_item_mut,
    visit_item_struct_mut, visit_item_type_mut, visit_path_mut,
};
use ::syn::{
    BinOp, Block, Expr, ExprBinary, ExprBlock, ExprLit, ExprParen, ExprPath, ExprUnary,
    GenericArgument, GenericParam, Generics, Ident, ImplItem, Item, ItemImpl, ItemStruct, Lit,
    LitBool, Path, PathArguments, PathSegment, Stmt, Type, TypePath, UnOp, WhereClause,
    WherePredicate, parse, parse_macro_input,
};

/// A proc macro to generate code for `quither` crate.
///
/// **This macro is for internal use by the `quither` crate. Do not use it directly in your own projects.**
///
/// This macro can be used for an attribute macro for `Item`s, like an `impl` block.
/// Without passing any arguments, this macro copies the annotated item 7 times, with:
///  - Replacing the path segment `Xither` (without generic parameters) or `Xither<X, Y>` (with 2 generic parameters)
///    with `Either`, `Neither`, `Both`, `EitherOrNeither`, `EitherOrBoth` or `NeitherOrBoth`.
///    MAKE SURE TO NOT EXPOSE THE NAME `Xither` TO THE `quither` CRATE'S PUBLIC API OR DOCUMENTATION.
///  - Replacing the path segment like `Xither<X, Y, e, n, b>`, where `e`, `n`, and `b` are boolean
///    constants, with corresponding variant types like `Either<X, Y>`, `EitherOrBoth<X, Y>`, etc.
///    `e`, `n`, and `b` indicate whether the corresponding variant type has `Either`, `Neither`,
///    or `Both` enum variants.
///  - Replacing the `has_either`, `has_neither`, and `has_both` expressions with the corresponding
///    boolean constants (i.e. `true` or `false`), depend on the current copied item's state.
///  - A syntax subtree inside this macro can also have `quither(...)` attribute to enable / disable
///    that syntax subtree. The attribute accepts a boolean expression consist of:
///    - `true` or `false` literals
///    - `has_either`, `has_neither`, and `has_both` expressions
///    - `&&` and `||` operators
///    - `!` operator.
///  - Attributes `#[either]` / `#[neither]` / `#[both]` works as a shortcut for `#[quither(has_either)]`,
///    `#[quither(has_neither)]`, and `#[quither(has_both)]` respectively.
///
/// The outmost `#[quither]` attribute can take arguments as same as the inner one,
/// which controls which variant types are generated. For example, if you specify
/// `#[quither(has_either && !has_neither)]`, then the macro will generate `Either` and `EitherOrBoth`
/// types only.
#[proc_macro_attribute]
pub fn quither(args: TokenStream, input: TokenStream) -> TokenStream {
    let args_expr_opt: Option<Expr> = (!args.is_empty()).then(|| parse(args).unwrap());

    let ast = parse_macro_input!(input as Item);
    let mut results = Vec::<TokenStream2>::new();
    for (has_either, has_neither, has_both) in [
        (true, false, false),
        (false, true, false),
        (false, false, true),
        (true, true, false),
        (true, false, true),
        (false, true, true),
        (true, true, true),
    ] {
        let mut ast = ast.clone();
        let mut processor = CodeProcessor {
            has_either,
            has_neither,
            has_both,
        };
        if let Some(false) = args_expr_opt
            .as_ref()
            .and_then(|args_expr| processor.check_quither_condition(&args_expr))
        {
            continue;
        }
        processor.visit_item_mut(&mut ast);

        let generated_item = quote! { #ast };
        results.push(generated_item);
    }
    quote! {
        #(#results)*
    }
    .into()
}

struct CodeProcessor {
    has_either: bool,
    has_neither: bool,
    has_both: bool,
}

impl VisitMut for CodeProcessor {
    fn visit_path_mut(&mut self, node: &mut Path) {
        // Type `Xither<L, R>` or `Xither<L, R, has_either, has_neither, has_both>` will be
        // replaced with something like `EitherOrBoth<L, R>` depend on the bool arguments.
        for segment in node.segments.iter_mut() {
            self.replace_quither_path_segment(segment, |ident, new_part| {
                ident.to_string().replace("Xither", new_part)
            });
        }
        visit_path_mut(self, node);
    }

    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        self.replace_has_quither_expr(expr);
        visit_expr_mut(self, expr);
    }

    fn visit_item_mut(&mut self, item: &mut Item) {
        visit_item_mut(self, item);
    }

    fn visit_item_struct_mut(&mut self, item_struct: &mut ItemStruct) {
        visit_item_struct_mut(self, item_struct);
        self.replace_quither_type_definition(&mut item_struct.ident, &mut item_struct.generics);
    }

    fn visit_item_type_mut(&mut self, item_type: &mut syn::ItemType) {
        visit_item_type_mut(self, item_type);
        self.replace_quither_type_definition(&mut item_type.ident, &mut item_type.generics);
    }

    fn visit_item_impl_mut(&mut self, item_impl: &mut ItemImpl) {
        visit_item_impl_mut(self, item_impl);

        item_impl.items.retain_mut(|item| {
            let attr_vec = match item {
                ImplItem::Fn(item_fn) => &mut item_fn.attrs,
                ImplItem::Const(item_const) => &mut item_const.attrs,
                ImplItem::Type(item_type) => &mut item_type.attrs,
                ImplItem::Macro(item_macro) => &mut item_macro.attrs,
                _ => return true,
            };
            let quither_attr_result =
                find_first_and_remove_vec_mut(attr_vec, |attr| self.check_attr_is_true(attr));
            match quither_attr_result {
                Some(true) => true,
                Some(false) => false, // Remove the item if the attribute is false.
                None => true,
            }
        });

        // If the `<L, R>` arguments are not found in the impl, we need to remove them.
        // This can happen when only the `Neither` type is used.
        let unused_type_params = self
            .remove_unused_type_params(item_impl)
            .collect::<Vec<_>>();
        if let Some(where_clause) = &mut item_impl.generics.where_clause {
            self.remove_where_clause_for_type_params(where_clause, unused_type_params.iter());
        }
    }

    fn visit_expr_match_mut(&mut self, ma: &mut syn::ExprMatch) {
        visit_expr_match_mut(self, ma);
        ma.arms.retain_mut(|arm| {
            let attr_vec = &mut arm.attrs;
            find_first_and_remove_vec_mut(attr_vec, |attr| self.check_attr_is_true(attr))
                .unwrap_or(true)
        });
    }
}

impl CodeProcessor {
    fn replace_quither_path_segment<F>(&self, segment: &mut PathSegment, new_name_gen: F)
    where
        F: FnOnce(&str, &str) -> String,
    {
        let ident_string = segment.ident.to_string();
        if !ident_string.contains("Xither") {
            return;
        }
        let Some(bool_args) = self.implicit_345th_bool_arguments_for_path_segment(segment) else {
            return;
        };
        let new_name_part = Self::quither_name_gen(bool_args);
        segment.ident = Ident::new(
            &new_name_gen(&ident_string, new_name_part),
            segment.ident.span(),
        );
        if bool_args == (false, true, false) {
            // For `Neither` type, we need to remove the `<L, R>` arguments.
            segment.arguments = PathArguments::None
        } else if let PathArguments::AngleBracketed(syn_args) = &mut segment.arguments {
            // For other types, we need to keep the `<L, R>` arguments, but remove the
            // `<has_either, has_neither, has_both>` arguments if available.
            while syn_args.args.len() > 2 {
                syn_args.args.pop();
            }
            if syn_args.args.is_empty() {
                segment.arguments = PathArguments::None
            }
        }
    }

    fn replace_quither_type_definition(&self, ident: &mut Ident, params: &mut Generics) {
        if !self.has_either && !self.has_both {
            // For `Neither` type, we need to remove the `<L, R>` params after `impl`.
            params.params.clear();
            params.where_clause = None;
        }

        let ident_str = ident.to_string();
        if let Some(_) = ident_str.find("Xither") {
            let new_ident_str = ident_str.replace(
                "Xither",
                Self::quither_name_gen((self.has_either, self.has_neither, self.has_both)),
            );
            *ident = Ident::new(&new_ident_str, ident.span());
        }
    }

    fn replace_has_quither_expr(&self, expr: &mut Expr) {
        let Expr::Path(ExprPath { path, .. }) = expr else {
            return;
        };
        let Some(ident) = path.get_ident() else {
            return;
        };
        let found_value = if ident == "has_either" {
            Some(self.has_either)
        } else if ident == "has_neither" {
            Some(self.has_neither)
        } else if ident == "has_both" {
            Some(self.has_both)
        } else {
            None
        };
        if let Some(found_value) = found_value {
            *expr = Expr::Lit(ExprLit {
                lit: Lit::Bool(LitBool {
                    value: found_value,
                    span: expr.span(),
                }),
                attrs: Vec::new(),
            });
        }
    }

    fn implicit_345th_bool_arguments_for_path_segment(
        &self,
        segment: &syn::PathSegment,
    ) -> Option<(bool, bool, bool)> {
        if let PathArguments::AngleBracketed(syn_args) = &segment.arguments {
            let args = syn_args.args.clone().into_pairs().collect::<Vec<_>>();
            if args.len() == 5 {
                let has_either = self.generic_argument_as_a_bool(&args[2].value())?;
                let has_neither = self.generic_argument_as_a_bool(&args[3].value())?;
                let has_both = self.generic_argument_as_a_bool(&args[4].value())?;
                return Some((has_either, has_neither, has_both));
            }
        }
        Some((self.has_either, self.has_neither, self.has_both))
    }

    fn generic_argument_as_a_bool(&self, arg: &GenericArgument) -> Option<bool> {
        if let GenericArgument::Const(arg_expr) = arg {
            self.check_quither_condition(&arg_expr)
        } else if let GenericArgument::Type(Type::Path(TypePath { path, .. })) = arg {
            self.check_quither_condition_for_path(&path)
        } else {
            None
        }
    }

    fn remove_unused_type_params(&self, item_impl: &mut ItemImpl) -> impl Iterator<Item = Ident> {
        let mut type_param_finder = TypeParamFinder::default();
        type_param_finder.visit_type(&item_impl.self_ty);
        if let Some((_, trait_path, _)) = &item_impl.trait_ {
            type_param_finder.visit_path(trait_path);
        }
        let (used, unused) = item_impl
            .generics
            .params
            .iter()
            .cloned()
            .partition::<Vec<_>, _>(|param| {
                let GenericParam::Type(tp) = param else {
                    return false;
                };
                type_param_finder.does_appear(&tp.ident)
            });
        item_impl.generics.params = used.into_iter().collect();
        item_impl.generics.params.pop_punct();
        unused.into_iter().filter_map(|param| {
            let GenericParam::Type(tp) = param else {
                return None;
            };
            Some(tp.ident)
        })
    }

    fn remove_where_clause_for_type_params<'a>(
        &self,
        where_clause: &mut WhereClause,
        unused_type_params: impl Iterator<Item = &'a Ident> + Clone,
    ) {
        where_clause.predicates = where_clause
            .predicates
            .iter()
            .cloned()
            .filter_map(|pred| {
                let WherePredicate::Type(tp) = &pred else {
                    return Some(pred);
                };
                let mut finder = TypeParamFinder::default();
                finder.visit_type(&tp.bounded_ty);
                if unused_type_params
                    .clone()
                    .any(|param| finder.does_appear(param))
                {
                    // Any of the given unused type params is found in the bounded type,
                    // so we need to remove this predicate.
                    None
                } else {
                    Some(pred)
                }
            })
            .collect();
        where_clause.predicates.pop_punct();
    }

    fn check_attr_is_true(&self, attr: &syn::Attribute) -> Option<bool> {
        let attr_path = attr.meta.path();
        if attr_path.is_ident("either") {
            return Some(self.has_either);
        } else if attr_path.is_ident("neither") {
            return Some(self.has_neither);
        } else if attr_path.is_ident("both") {
            return Some(self.has_both);
        } else if attr_path.is_ident("quither") {
            return self.check_quither_condition(&attr.parse_args().ok()?);
        } else {
            return None;
        }
    }

    fn check_quither_condition(&self, args: &Expr) -> Option<bool> {
        match args {
            Expr::Binary(ExprBinary {
                left, right, op, ..
            }) => {
                let left = self.check_quither_condition(left)?;
                let right = self.check_quither_condition(right)?;
                match op {
                    BinOp::And(_) => Some(left && right),
                    BinOp::Or(_) => Some(left || right),
                    _ => None,
                }
            }
            Expr::Unary(ExprUnary {
                expr,
                op: UnOp::Not(_),
                ..
            }) => self.check_quither_condition(expr).map(|b| !b),
            Expr::Paren(ExprParen { expr, .. }) => self.check_quither_condition(expr),
            Expr::Block(ExprBlock {
                block: Block { stmts, .. },
                ..
            }) => {
                if stmts.len() != 1 {
                    return None;
                }
                let Some(Stmt::Expr(expr, _)) = stmts.first() else {
                    return None;
                };
                self.check_quither_condition(expr)
            }
            Expr::Path(ExprPath { path, .. }) => self.check_quither_condition_for_path(path),
            Expr::Lit(ExprLit {
                lit: Lit::Bool(LitBool { value, .. }),
                ..
            }) => Some(*value),
            _ => None,
        }
    }

    fn check_quither_condition_for_path(&self, path: &Path) -> Option<bool> {
        if path.is_ident("has_either") {
            Some(self.has_either)
        } else if path.is_ident("has_neither") {
            Some(self.has_neither)
        } else if path.is_ident("has_both") {
            Some(self.has_both)
        } else {
            None
        }
    }

    fn quither_name_gen(bool_args: (bool, bool, bool)) -> &'static str {
        match bool_args {
            (true, true, true) => "Quither",
            (true, true, false) => "EitherOrNeither",
            (true, false, true) => "EitherOrBoth",
            (true, false, false) => "Either",
            (false, true, true) => "NeitherOrBoth",
            (false, true, false) => "Neither",
            (false, false, true) => "Both",
            (false, false, false) => "Unreachable",
        }
    }
}

#[derive(Default, Debug)]
struct TypeParamFinder {
    idents: HashSet<Ident>,
}

impl TypeParamFinder {
    fn does_appear(&self, ident: &Ident) -> bool {
        self.idents.contains(ident)
    }
}

impl<'ast> Visit<'ast> for TypeParamFinder {
    fn visit_path(&mut self, path: &'ast Path) {
        visit_path(self, path);
        if let Some(ident) = path.get_ident() {
            self.idents.insert(ident.clone());
        }
    }

    fn visit_ident(&mut self, ident: &'ast Ident) {
        visit_ident(self, ident);
        self.idents.insert(ident.clone());
    }

    fn visit_path_segment(&mut self, segment: &'ast PathSegment) {
        // Do recurse into the type params, but not for the segment's ident
        // because it's already visited in `visit_path`.
        // We only need the standalone ident, not the path including `::`.
        visit_path_arguments(self, &segment.arguments);
    }
}

fn find_first_and_remove_vec_mut<T, U, F>(vec: &mut Vec<T>, f: F) -> Option<U>
where
    F: Fn(&mut T) -> Option<U>,
{
    for (i, item) in vec.iter_mut().enumerate() {
        if let Some(u) = f(item) {
            vec.remove(i);
            return Some(u);
        }
    }
    None
}

#[test]
fn test_quither_condition_value() {
    use ::syn::parse_quote;

    let cp = CodeProcessor {
        has_either: true,
        has_neither: false,
        has_both: true,
    };
    assert_eq!(
        Some(true),
        cp.check_quither_condition(&parse_quote! { true })
    );
    assert_eq!(
        Some(true),
        cp.check_quither_condition(&parse_quote! { has_either })
    );
    assert_eq!(
        Some(true),
        cp.check_quither_condition(&parse_quote! { { true } })
    );
    assert_eq!(
        Some(false),
        cp.check_quither_condition(&parse_quote! { { has_either && has_neither } })
    );
}

#[test]
fn test_visit_path_mut() {
    use ::proc_macro2::Span;
    use ::syn::parse_quote_spanned;

    let mut cp = CodeProcessor {
        has_either: true,
        has_neither: false,
        has_both: true,
    };
    let span = Span::call_site();

    let mut path = parse_quote_spanned! { span => Xither<L, R> };
    cp.visit_path_mut(&mut path);
    assert_eq!(path, parse_quote_spanned! { span => EitherOrBoth<L, R> });

    let mut path = parse_quote_spanned! { span => Xither<L, R, false, false, true> };
    cp.visit_path_mut(&mut path);
    assert_eq!(path, parse_quote_spanned! { span => Both<L, R, > });

    let mut path = parse_quote_spanned! { span => Xither<L, R, has_both, has_both, has_neither> };
    cp.visit_path_mut(&mut path);
    assert_eq!(
        path,
        parse_quote_spanned! { span => EitherOrNeither<L, R, > }
    );
}
