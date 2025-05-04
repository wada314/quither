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
use ::proc_macro2::{Span, TokenStream as TokenStream2};
use ::quote::quote;
use ::syn::spanned::Spanned;
use ::syn::visit_mut::{
    VisitMut, visit_expr_match_mut, visit_expr_mut, visit_item_impl_mut, visit_item_mut,
    visit_item_struct_mut, visit_path_mut,
};
use ::syn::{
    BinOp, Block, Expr, ExprBinary, ExprBlock, ExprLit, ExprParen, ExprPath, ExprUnary,
    GenericArgument, Ident, ImplItem, Item, ItemImpl, ItemStruct, Lit, LitBool, Path,
    PathArguments, PathSegment, Stmt, Type, TypePath, UnOp, parse, parse_macro_input, parse_quote,
    parse_quote_spanned,
};

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
        // Type `Quither<L, R>` or `Quither<L, R, has_either, has_neither, has_both>` will be
        // replaced with something like `EitherOrBoth<L, R>` depend on the bool arguments.
        for segment in node.segments.iter_mut() {
            let ident = segment.ident.to_string();
            if let Some(_) = ident.find("Quither") {
                self.replace_quither_path_segment(segment, |new_part| {
                    ident.replace("Quither", new_part)
                });
            }
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

        if !self.has_either && !self.has_both {
            // For `Neither` type, we need to remove the `<L, R>` arguments after `impl`.
            item_struct.generics.params.clear();
            item_struct.generics.where_clause = None;
        }

        let ident_str = item_struct.ident.to_string();
        if let Some(_) = ident_str.find("Quither") {
            let new_ident_str = ident_str.replace(
                "Quither",
                Self::quither_name_gen((self.has_either, self.has_neither, self.has_both)),
            );
            item_struct.ident = Ident::new(&new_ident_str, item_struct.ident.span());
        }
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

        if !self.has_either && !self.has_both {
            // For `Neither` type, we need to remove the `<L, R>` arguments after `impl`.
            item_impl.generics.params.clear();
            item_impl.generics.where_clause = None;
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
    fn replace_quither_path_segment<F>(&mut self, segment: &mut PathSegment, new_name_gen: F)
    where
        F: FnOnce(&str) -> String,
    {
        let args = match &mut segment.arguments {
            PathArguments::AngleBracketed(syn_args) => {
                syn_args.args.clone().into_pairs().collect::<Vec<_>>()
            }
            PathArguments::None => Vec::new(),
            _ => return,
        };
        let bool_args = if args.len() == 5 {
            let Some(has_either) = self.generic_argument_as_a_bool(&args[2].value()) else {
                return;
            };
            let Some(has_neither) = self.generic_argument_as_a_bool(&args[3].value()) else {
                return;
            };
            let Some(has_both) = self.generic_argument_as_a_bool(&args[4].value()) else {
                return;
            };
            (has_either, has_neither, has_both)
        } else if args.len() == 2 || args.len() == 0 {
            (self.has_either, self.has_neither, self.has_both)
        } else {
            return;
        };
        let new_name_part = Self::quither_name_gen(bool_args);
        segment.ident = Ident::new(&new_name_gen(new_name_part), segment.ident.span());
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

    fn replace_has_quither_expr(&mut self, expr: &mut Expr) {
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

    fn generic_argument_as_a_bool(&self, arg: &GenericArgument) -> Option<bool> {
        if let GenericArgument::Const(arg_expr) = arg {
            self.check_quither_condition(&arg_expr)
        } else if let GenericArgument::Type(Type::Path(TypePath { path, .. })) = arg {
            self.check_quither_condition_for_path(&path)
        } else {
            None
        }
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
    let mut cp = CodeProcessor {
        has_either: true,
        has_neither: false,
        has_both: true,
    };
    let span = Span::call_site();

    let mut path = parse_quote_spanned! { span => Quither<L, R> };
    cp.visit_path_mut(&mut path);
    assert_eq!(path, parse_quote_spanned! { span => EitherOrBoth<L, R> });

    let mut path = parse_quote_spanned! { span => Quither<L, R, false, false, true> };
    cp.visit_path_mut(&mut path);
    assert_eq!(path, parse_quote_spanned! { span => Both<L, R, > });

    let mut path = parse_quote_spanned! { span => Quither<L, R, has_both, has_both, has_neither> };
    cp.visit_path_mut(&mut path);
    assert_eq!(
        path,
        parse_quote_spanned! { span => EitherOrNeither<L, R, > }
    );
}
