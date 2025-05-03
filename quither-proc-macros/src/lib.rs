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
use ::syn::visit_mut::{VisitMut, visit_expr_match_mut, visit_item_impl_mut, visit_path_mut};
use ::syn::{
    BinOp, Expr, ExprBinary, ExprLit, ExprParen, ExprPath, ExprUnary, GenericArgument, Ident,
    ImplItem, ItemImpl, Lit, LitBool, Path, PathArguments, PathSegment, Type, TypePath, UnOp,
    parse, parse_macro_input,
};

#[proc_macro_attribute]
pub fn quither(args: TokenStream, input: TokenStream) -> TokenStream {
    let args_expr_opt: Option<Expr> = (!args.is_empty()).then(|| parse(args).unwrap());

    let ast = parse_macro_input!(input as ItemImpl);
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
            .and_then(|args_expr| processor.check_quither_attr_condition(&args_expr))
        {
            continue;
        }
        processor.visit_item_impl_mut(&mut ast);

        if !has_either && !has_both {
            // For `Neither` type, we need to remove the `<L, R>` arguments after `impl`.
            ast.generics.params.clear();
            ast.generics.where_clause = None;
        }

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
        // Recursively visit the path, do replacements in inner paths first.
        visit_path_mut(self, node);

        // Type `Quither<L, R>` or `Quither<L, R, has_either, has_neither, has_both>` will be
        // replaced with something like `EitherOrBoth<L, R>` depend on the bool arguments.
        for segment in node.segments.iter_mut() {
            if segment.ident == "Quither" {
                self.replace_quither_path_segment(segment);
            }
        }

        self.replace_has_quither_path(node);
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
    fn replace_quither_path_segment(&mut self, segment: &mut PathSegment) {
        let args = match &mut segment.arguments {
            PathArguments::AngleBracketed(syn_args) => {
                syn_args.args.clone().into_pairs().collect::<Vec<_>>()
            }
            PathArguments::None => Vec::new(),
            _ => return,
        };
        let bool_args = if args.len() == 5 {
            let Some(has_either) = generic_argument_as_a_bool(&args[2].value()) else {
                return;
            };
            let Some(has_neither) = generic_argument_as_a_bool(&args[3].value()) else {
                return;
            };
            let Some(has_both) = generic_argument_as_a_bool(&args[4].value()) else {
                return;
            };
            (has_either, has_neither, has_both)
        } else if args.len() == 2 || args.len() == 0 {
            (self.has_either, self.has_neither, self.has_both)
        } else {
            return;
        };
        let new_ident = match bool_args {
            (true, true, true) => "Quither",
            (true, true, false) => "EitherOrNeither",
            (true, false, true) => "EitherOrBoth",
            (true, false, false) => "Either",
            (false, true, true) => "NeitherOrBoth",
            (false, true, false) => "Neither",
            (false, false, true) => "Both",
            (false, false, false) => {
                return;
            }
        };
        segment.ident = Ident::new(new_ident, segment.ident.span());
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

    fn replace_has_quither_path(&mut self, path: &mut Path) {
        let Some(ident) = path.get_ident() else {
            return;
        };
        if ident == "has_either" {
            *path = Ident::new(if self.has_either { "true" } else { "false" }, ident.span()).into();
        } else if ident == "has_neither" {
            *path = Ident::new(
                if self.has_neither { "true" } else { "false" },
                ident.span(),
            )
            .into();
        } else if ident == "has_both" {
            *path = Ident::new(if self.has_both { "true" } else { "false" }, ident.span()).into();
        }
    }

    fn check_attr_is_true(&self, attr: &syn::Attribute) -> Option<bool> {
        let attr_path = attr.meta.path();
        if path_is_an_ident(&attr_path, "either") {
            return Some(self.has_either);
        } else if path_is_an_ident(&attr_path, "neither") {
            return Some(self.has_neither);
        } else if path_is_an_ident(&attr_path, "both") {
            return Some(self.has_both);
        } else if path_is_an_ident(&attr_path, "quither") {
            return self.check_quither_attr_condition(&attr.parse_args().ok()?);
        } else {
            return None;
        }
    }

    fn check_quither_attr_condition(&self, args: &Expr) -> Option<bool> {
        match args {
            Expr::Binary(ExprBinary {
                left, right, op, ..
            }) => {
                let left = self.check_quither_attr_condition(left)?;
                let right = self.check_quither_attr_condition(right)?;
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
            }) => self.check_quither_attr_condition(expr).map(|b| !b),
            Expr::Paren(ExprParen { expr, .. }) => self.check_quither_attr_condition(expr),
            Expr::Path(ExprPath { path, .. }) => {
                if path_is_an_ident(path, "has_either") {
                    Some(self.has_either)
                } else if path_is_an_ident(path, "has_neither") {
                    Some(self.has_neither)
                } else if path_is_an_ident(path, "has_both") {
                    Some(self.has_both)
                } else {
                    None
                }
            }
            _ => None,
        }
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

fn path_is_an_ident(path: &Path, ident: &str) -> bool {
    if path.segments.len() != 1 {
        return false;
    }
    if path.leading_colon.is_some() {
        return false;
    }
    let Some(first_segment) = path.segments.first() else {
        return false;
    };
    first_segment.ident == ident && first_segment.arguments.is_empty()
}

fn generic_argument_is_an_ident(arg: &GenericArgument, expected_ident: &str) -> bool {
    match arg {
        GenericArgument::Type(Type::Path(TypePath {
            path, qself: None, ..
        })) => {
            let Some(ident) = path.get_ident() else {
                return false;
            };
            ident == expected_ident
        }
        GenericArgument::Const(Expr::Lit(ExprLit { lit, .. })) => {
            let Lit::Bool(LitBool { value, .. }) = lit else {
                return false;
            };
            match value {
                true => expected_ident == "true",
                false => expected_ident == "false",
            }
        }
        _ => false,
    }
}

fn generic_argument_as_a_bool(arg: &GenericArgument) -> Option<bool> {
    if generic_argument_is_an_ident(arg, "true") {
        Some(true)
    } else if generic_argument_is_an_ident(arg, "false") {
        Some(false)
    } else {
        None
    }
}
