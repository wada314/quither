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
use ::syn::{
    BinOp, Expr, ExprBinary, ExprParen, ExprPath, ExprUnary, GenericArgument, Ident, ImplItem,
    ItemImpl, Path, PathArguments, Type, TypePath, UnOp, parse_macro_input,
    visit_mut::{VisitMut, visit_path_mut},
};

#[proc_macro_attribute]
pub fn enb(_args: TokenStream, input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as ItemImpl);
    let mut results = Vec::<TokenStream2>::new();
    for (e, n, b) in [
        (true, false, false),
        (false, true, false),
        (false, false, true),
        (true, true, false),
        (true, false, true),
        (false, true, true),
        (true, true, true),
    ] {
        results.push(expand_enb(ast.clone(), e, n, b));
    }
    quote! {
        #(#results)*
    }
    .into()
}

fn expand_enb(
    mut input: ItemImpl,
    has_either: bool,
    has_neither: bool,
    has_both: bool,
) -> TokenStream2 {
    let mut replacer = CodeProcessor {
        has_either,
        has_neither,
        has_both,
    };
    replacer.visit_item_impl_mut(&mut input);

    if !has_either && !has_both {
        // For `Neither` type, we need to remove the `<L, R>` arguments after `impl`.
        input.generics.params.clear();
    }

    quote! { #input }
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

        let Some(last_segment) = node.segments.last_mut() else {
            return;
        };

        // Type `Enb<L, R>` or `Enb<L, R, has_either, has_neither, has_both>` will be
        // replaced with something like `EitherOrBoth<L, R>` depend on the bool arguments.
        if last_segment.ident == "Enb" {
            let PathArguments::AngleBracketed(syn_args) = &mut last_segment.arguments else {
                return;
            };
            let args = syn_args.args.clone().into_pairs().collect::<Vec<_>>();
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
            } else if args.len() == 2 {
                (self.has_either, self.has_neither, self.has_both)
            } else {
                return;
            };
            let new_ident = match bool_args {
                (true, true, true) => "EitherOrNeitherOrBoth",
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
            last_segment.ident = Ident::new(new_ident, last_segment.ident.span());
            if bool_args == (false, true, false) {
                // For `Neither` type, we need to remove the `<L, R>` arguments.
                last_segment.arguments = PathArguments::None
            } else {
                // For other types, we need to keep the `<L, R>` arguments, but remove the
                // `<has_either, has_neither, has_both>` arguments if available.
                while syn_args.args.len() > 2 {
                    syn_args.args.pop();
                }
            }
        }
    }

    fn visit_item_impl_mut(&mut self, item_impl: &mut ItemImpl) {
        let _ = find_and_remove_vec_mut(&mut item_impl.items, |item| {
            let attr_vec = match item {
                ImplItem::Fn(item_fn) => &mut item_fn.attrs,
                ImplItem::Const(item_const) => &mut item_const.attrs,
                ImplItem::Type(item_type) => &mut item_type.attrs,
                ImplItem::Macro(item_macro) => &mut item_macro.attrs,
                _ => return Some(()),
            };
            let enb_attr_result =
                find_and_remove_vec_mut(attr_vec, |attr| self.check_attr_is_true(attr));
            match enb_attr_result {
                Some(true) => None,
                Some(false) => Some(()), // Remove the item if the attribute is false.
                None => None,
            }
        });
    }
}

impl CodeProcessor {
    fn check_attr_is_true(&self, attr: &syn::Attribute) -> Option<bool> {
        let attr_path = attr.meta.path();
        if path_is_an_ident(&attr_path, "either") {
            return Some(self.has_either);
        } else if path_is_an_ident(&attr_path, "neither") {
            return Some(self.has_neither);
        } else if path_is_an_ident(&attr_path, "both") {
            return Some(self.has_both);
        } else if path_is_an_ident(&attr_path, "enb") {
            return self.check_enb_attr_condition(&attr.parse_args().ok()?);
        } else {
            return None;
        }
    }

    fn check_enb_attr_condition(&self, args: &Expr) -> Option<bool> {
        match args {
            Expr::Binary(ExprBinary {
                left, right, op, ..
            }) => {
                let left = self.check_enb_attr_condition(left)?;
                let right = self.check_enb_attr_condition(right)?;
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
            }) => self.check_enb_attr_condition(expr),
            Expr::Paren(ExprParen { expr, .. }) => self.check_enb_attr_condition(expr),
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

fn find_and_remove_vec_mut<T, U, F>(vec: &mut Vec<T>, f: F) -> Option<U>
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

fn type_path_is_an_ident(path: &TypePath, ident: &str) -> bool {
    path.qself.is_none() && path_is_an_ident(&path.path, ident)
}

fn generic_argument_is_an_ident(arg: &GenericArgument, ident: &str) -> bool {
    let GenericArgument::Type(Type::Path(path)) = arg else {
        return false;
    };
    type_path_is_an_ident(path, ident)
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
