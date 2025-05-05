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
use ::syn::spanned::Spanned;
use ::syn::visit::{Visit, visit_path, visit_path_segment, visit_type};
use ::syn::visit_mut::{
    VisitMut, visit_expr_match_mut, visit_expr_mut, visit_item_impl_mut, visit_item_mut,
    visit_item_struct_mut, visit_item_type_mut, visit_path_mut,
};
use ::syn::{
    BinOp, Block, Expr, ExprBinary, ExprBlock, ExprLit, ExprParen, ExprPath, ExprUnary,
    GenericArgument, Generics, Ident, ImplItem, Item, ItemImpl, ItemStruct, Lit, LitBool, Path,
    PathArguments, PathSegment, Stmt, Type, TypePath, UnOp, parse, parse_macro_input,
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
        self.replace_quither_type_definition(&mut item_struct.ident, &mut item_struct.generics);
    }

    fn visit_item_type_mut(&mut self, item_type: &mut syn::ItemType) {
        visit_item_type_mut(self, item_type);
        self.replace_quither_type_definition(&mut item_type.ident, &mut item_type.generics);
    }

    fn visit_item_impl_mut(&mut self, item_impl: &mut ItemImpl) {
        let lr_params_exist = self.check_lr_params_exist_in_impl(item_impl);

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

        if !lr_params_exist {
            // If the `<L, R>` arguments are not found in the impl, we need to remove them.
            // This can happen when only the `Neither` type is used.
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
    fn replace_quither_path_segment<F>(&self, segment: &mut PathSegment, new_name_gen: F)
    where
        F: FnOnce(&str) -> String,
    {
        let Some(bool_args) = self.implicit_345th_bool_arguments_for_path_segment(segment) else {
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

    fn replace_quither_type_definition(&self, ident: &mut Ident, params: &mut Generics) {
        if !self.has_either && !self.has_both {
            // For `Neither` type, we need to remove the `<L, R>` params after `impl`.
            params.params.clear();
            params.where_clause = None;
        }

        let ident_str = ident.to_string();
        if let Some(_) = ident_str.find("Quither") {
            let new_ident_str = ident_str.replace(
                "Quither",
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

    fn check_lr_params_exist_in_impl(&self, impl_item: &syn::ItemImpl) -> bool {
        let mut lr_argument_finder = LrArgumentFinder {
            found: false,
            processor: self,
        };
        visit_type(&mut lr_argument_finder, &impl_item.self_ty);
        if let Some((_, trait_path, _)) = &impl_item.trait_ {
            visit_path(&mut lr_argument_finder, trait_path);
        }
        lr_argument_finder.found
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

struct LrArgumentFinder<'a> {
    found: bool,
    processor: &'a CodeProcessor,
}

impl<'a, 'ast> Visit<'ast> for LrArgumentFinder<'a> {
    fn visit_path_segment(&mut self, segment: &'ast PathSegment) {
        visit_path_segment(self, segment);

        if !segment.ident.to_string().contains("Quither") {
            return;
        }
        let Some(bool_args) = self
            .processor
            .implicit_345th_bool_arguments_for_path_segment(segment)
        else {
            return;
        };
        if bool_args != (false, true, false) {
            // Unless the bool arguments are expressing `Neither` type, we can find the `L` and `R`
            // arguments.
            self.found = true;
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

#[test]
fn test_check_lr_params_exist_in_impl() {
    use ::proc_macro2::Span;
    use ::syn::parse_quote_spanned;

    let span = Span::call_site();
    let cp_neither = CodeProcessor {
        has_either: false,
        has_neither: true,
        has_both: false,
    };
    let cp_quither = CodeProcessor {
        has_either: true,
        has_neither: true,
        has_both: true,
    };

    let impl_item = parse_quote_spanned! { span =>
        impl<L, R> Quither<L, R> {}
    };
    assert!(!cp_neither.check_lr_params_exist_in_impl(&impl_item));
    assert!(cp_quither.check_lr_params_exist_in_impl(&impl_item));

    let impl_item = parse_quote_spanned! { span =>
        impl<L, R> From<Quither<L, R>> for EitherOrBoth<L, R> {}
    };
    assert!(!cp_neither.check_lr_params_exist_in_impl(&impl_item));
    assert!(cp_quither.check_lr_params_exist_in_impl(&impl_item));
}
