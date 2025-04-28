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
use ::syn::{ItemImpl, parse, parse_macro_input, visit_mut::VisitMut};

#[proc_macro_attribute]
pub fn enb(_args: TokenStream, input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as ItemImpl);
    let mut results = Vec::new();
    for (e, n, b) in [
        (true, false, false),
        (false, true, false),
        (false, false, true),
        (true, true, false),
        (true, false, true),
        (false, true, true),
        (true, true, true),
    ] {
        results.push(expand_enb(ast.clone(), e, n, b).into());
    }
    quote! {
        #(#results)*
    }
    .into()
}

fn expand_enb<T: VisitMut>(
    input: T,
    has_either: bool,
    has_neither: bool,
    has_both: bool,
) -> TokenStream2 {
    todo!()
}
