#![recursion_limit = "128"]

extern crate proc_macro;
extern crate proc_macro_hack;
extern crate quote;


use proc_macro::TokenStream;
use proc_macro_hack::proc_macro_hack;
use quote::{quote};


#[proc_macro_hack]
pub fn scanln(_input: TokenStream) -> TokenStream {
    let mut result = quote! {
        use darkly::Scanner;

        let mut scanner = darkly::scan_stdin();
    };
    let ee = quote! {
        let bar: Result<_, String> = scanner.scan_to("fdf");
        let bar = bar.unwrap_or_else(|e| panic!());
    };
    result.extend(ee.into_iter());

    let result = quote! { { #result 64 } };
    result.into()
}

