#![recursion_limit = "128"]

// TODO
// if we ever fix specialization, we should be able to avoid the unwraps here
// (and do it in the scanner?)

extern crate proc_macro;
extern crate proc_macro2;
extern crate quote;
extern crate syn;


use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{quote, ToTokens};
use syn::{Ident, Type, LitStr, Token, punctuated::Punctuated, token::Comma};
use syn::parse::{self, ParseStream};



#[proc_macro]
pub fn scanln(input: TokenStream) -> TokenStream {
    expand(input).into()
}

fn expand_expr_form(chunks: Vec<Chunk>) -> proc_macro2::TokenStream {
    let mut result = quote! {
        use darkly::Scanner;

        let mut scanner = darkly::scan_stdin();
    };
    let mut chunks = chunks.into_iter().peekable();
    let mut elements = vec![];
    while let Some(c) = chunks.next() {
        match c {
            Chunk::Text(ref s) => {
                result.extend(text_chunk(s).into_iter());
            }
            Chunk::Directive(DirKind::Hole) => {
                let next_is_text = chunks.peek().and_then(|n| match *n {
                    Chunk::Text(_) => Some(()),
                    Chunk::Directive(_) => None,
                });
                let next = next_is_text.map(|_| {
                    chunks.next().unwrap().expect_text()
                });
                let name = format!("__scan_var_{}", elements.len());
                result.extend(expr_expansion(&name, next).into_iter());
                elements.push(Ident::new(&name, Span::call_site()));
            }
            Chunk::Directive(DirKind::DebugHole) => unimplemented!(),
        }
    }

    // Put all the components together into a tuple.
    result.extend(quote! { (#(#elements,)*)}.into_iter());

    quote! { { #result } }
}

fn expr_expansion(name: &str, next_chunk: Option<String>) -> proc_macro2::TokenStream {
    // TODO refactor with Arg::expansion
    match next_chunk {
        None => {
            // TODO name is not a helpful identifier
            let panic_msg = format!("Error in scanln: expected value for `{}`, found `{{}}`", name);
            let name = Ident::new(name, Span::call_site());
            quote! {
                let #name: Result<_, String> = scanner.scan();
                let #name = #name.unwrap_or_else(|e| panic!(#panic_msg, e));
            }
        }
        Some(t) => {
            // TODO name is not a helpful identifier
            let panic_msg = format!("Error in scanln: expected value for `{}`, then `{}`, found `{{}}`", name, t);
            let name = Ident::new(name, Span::call_site());
            quote! {
                let #name: Result<_, String> = scanner.scan_to(#t);
                let #name = #name.unwrap_or_else(|e| panic!(#panic_msg, e));
            }
        }
    }
}


fn text_chunk(s: &str) -> proc_macro2::TokenStream {
    let panic_msg = format!("Error in scanln: expected `{}`, found `{{}}`", s);
    quote! {
        scanner.expect(#s).unwrap_or_else(|e| panic!(#panic_msg, e));
    }
}

fn expand(args: TokenStream) -> proc_macro2::TokenStream {
    let args: Args = syn::parse(args).expect("Parsing error");

    let chunks = process_lit_str(&args.str);

    if args.args.len() == 0 {
        return expand_expr_form(chunks);
    }

    assert!(args.args.len() == count_holes(&chunks), "Mismatched number of directives and arguments");

    let mut result = quote! {
        use darkly::Scanner;

        let mut scanner = darkly::scan_stdin();
    };
    let mut hole_count = 0;
    let mut chunks = chunks.into_iter().peekable();
    while let Some(c) = chunks.next() {
        match c {
            Chunk::Text(ref s) => {
                result.extend(text_chunk(s).into_iter());
            }
            Chunk::Directive(DirKind::Hole) => {
                let next_is_text = chunks.peek().and_then(|n| match *n {
                    Chunk::Text(_) => Some(()),
                    Chunk::Directive(_) => None,
                });
                let next = next_is_text.map(|_| {
                    chunks.next().unwrap().expect_text()
                });
                result.extend(args.args[hole_count].expansion(next).into_iter());
                hole_count += 1;
            }
            Chunk::Directive(DirKind::DebugHole) => unimplemented!(),
        }
    }
    result
}

#[derive(Eq, PartialEq, Debug, Clone)]
enum Chunk {
    Text(String),
    Directive(DirKind),
}

impl Chunk {
    fn expect_text(self) -> String {
        match self {
            Chunk::Text(t) => t,
            _ => panic!("expected text"),
        }
    }
}

#[derive(Eq, PartialEq, Debug, Clone)]
enum DirKind {
    // {}
    Hole,
    // {:?}
    DebugHole,
}

#[derive(Debug, Clone)]
struct Args {
    str: LitStr,
    args: Punctuated<Arg, Comma>,
}

impl parse::Parse for Args {
    fn parse(input: ParseStream) -> parse::Result<Args> {
        let str = input.parse()?;
        if input.peek(Comma) {
            input.parse::<Comma>()?;
        }
        let args = Punctuated::parse_terminated(input)?;

        Ok(Args {
            str,
            args,
        })
    }
}

#[derive(Debug, Clone)]
enum Arg {
    Ident(Ident),
    Typed(Ident, Type),
}

impl Arg {
    fn expansion(&self, next_chunk: Option<String>) -> proc_macro2::TokenStream {
        match *self {
            Arg::Ident(ref ident) => {
                match next_chunk {
                    None => {
                        let panic_msg = format!("Error in scanln: expected value for `{}`, found `{{}}`", ident);
                        quote! {
                            let #ident: Result<_, String> = scanner.scan();
                            let #ident = #ident.unwrap_or_else(|e| panic!(#panic_msg, e));
                        }
                    }
                    Some(t) => {
                        let panic_msg = format!("Error in scanln: expected value for `{}`, then `{}`, found `{{}}`", ident, t);
                        quote! {
                            let #ident: Result<_, String> = scanner.scan_to(#t);
                            let #ident = #ident.unwrap_or_else(|e| panic!(#panic_msg, e));
                        }
                    }
                }
            }
            Arg::Typed(ref ident, ref ty) => {
                match next_chunk {
                    None => {
                        let panic_msg = format!("Error in scanln: expected `{}`, found `{{}}`", ty.into_token_stream());
                        quote! {
                            let #ident: Result<#ty, String> = scanner.scan();
                            let #ident: #ty = #ident.unwrap_or_else(|e| panic!(#panic_msg, e));
                        }
                    }
                    Some(t) => {
                        let panic_msg = format!("Error in scanln: expected `{}`, then `{}`, found `{{}}`", ty.into_token_stream(), t);
                        quote! {
                            let #ident: Result<#ty, String> = scanner.scan_to(#t);
                            let #ident: #ty = #ident.unwrap_or_else(|e| panic!(#panic_msg, e));
                        }
                    }
                }
            }
        }
    }
}

impl parse::Parse for Arg {
    fn parse(input: ParseStream) -> parse::Result<Arg> {
        let ident = input.parse()?;
        if input.peek(Token![:]) {
            // A typed argument.
            input.parse::<Token![:]>()?;
            let ty = input.parse()?;
            Ok(Arg::Typed(ident, ty))
        } else {
            // An un-typed argument.
            Ok(Arg::Ident(ident))
        }
    }
}

fn process_lit_str(lit: &LitStr) -> Vec<Chunk> {
    tokenise_format_str(&lit.value())
}

fn count_holes(chunks: &[Chunk]) -> usize {
    chunks.iter().filter(|c| if let &Chunk::Directive(_) = *c { true } else { false }).count()

}

fn tokenise_format_str(s: &str) -> Vec<Chunk> {
    let mut result = vec![];

    #[derive(Copy, Clone)]
    enum State {
        Text,
        OpenBrace,
        CloseBrace,
        Hole,
    }

    let mut state = State::Text;
    let mut buf = String::new();
    let mut chars = s.chars();
    loop {
        match chars.next() {
            None => {
                match state {
                    State::Text => {
                        if !buf.is_empty() {
                            result.push(Chunk::Text(buf));
                        }
                    }
                    State::OpenBrace => panic!("Unclosed directive"),
                    State::CloseBrace => result.push(parse_directive(buf)),
                    State::Hole => panic!("Unclosed directive"),
                }
                return result;
            }
            Some(c) => {
                match (state, c) {
                    (State::OpenBrace, '{') => {
                        buf.push('{');
                        state = State::Text;
                    }
                    (State::OpenBrace, '}') => {
                        if !buf.is_empty() {
                            result.push(Chunk::Text(buf));
                            buf = String::new();
                        }
                        result.push(parse_directive(String::new()));
                        state = State::Text;
                    }
                    (State::OpenBrace, c) => {
                        if !buf.is_empty() {
                            result.push(Chunk::Text(buf));
                            buf = String::new();
                        }
                        buf.push(c);
                        state = State::Hole;
                    }
                    (State::CloseBrace, '}') => {
                        buf.push('}');
                        state = State::Text;
                    }
                    (State::CloseBrace, c) => {
                        result.push(parse_directive(buf));
                        buf = String::new();
                        buf.push(c);
                        state = State::Text;
                    }
                    (State::Hole, '}') => {
                        result.push(parse_directive(buf));
                        buf = String::new();
                        state = State::Text;
                    }
                    (State::Text, '{') => {
                        state = State::OpenBrace;
                    }
                    (State::Text, '}') => {
                        state = State::CloseBrace;
                    }
                    (State::Text, c) | (State::Hole, c) => {
                        buf.push(c);
                    }
                }
            }
        }
    }
}

// s is the string of data between `{` and `}`.
fn parse_directive(s: String) -> Chunk {
    if s.is_empty() {
        Chunk::Directive(DirKind::Hole)
    } else if s == ":?" {
        Chunk::Directive(DirKind::DebugHole)
    } else {
        panic!("Unknown directive in format string: `{{{}}}`", s);
    }
}


#[cfg(test)]
mod tests {
    use super::{tokenise_format_str, DirKind, Chunk};

    #[test]
    fn test_tok_fmt_str() {
        assert!(tokenise_format_str("").is_empty());

        let expected = [Chunk::Text("Hello".to_owned())];
        for (c, e) in tokenise_format_str("Hello").iter().zip(expected.iter()) {
            assert_eq!(c, e);
        }

        let expected = [Chunk::Text("Hello, ".to_owned()),
                        Chunk::Directive(DirKind::Hole),
                        Chunk::Text("!".to_owned()),
                        Chunk::Directive(DirKind::DebugHole)];
        for (c, e) in tokenise_format_str("Hello, {}!{:?}").iter().zip(expected.iter()) {
            assert_eq!(c, e);
        }

        let expected = [Chunk::Directive(DirKind::DebugHole)];
        for (c, e) in tokenise_format_str("{:?}").iter().zip(expected.iter()) {
            assert_eq!(c, e);
        }

        let expected = [Chunk::Text("Hello, {}".to_owned()),
                        Chunk::Directive(DirKind::DebugHole),
                        Chunk::Text("{".to_owned()),
                        Chunk::Directive(DirKind::Hole),
                        Chunk::Text("}!".to_owned())];
        for (c, e) in tokenise_format_str("Hello, {{}}{:?}{{{}}}!").iter().zip(expected.iter()) {
            assert_eq!(c, e);
        }
    }

    // #[test]
    // TODO
    // fn it_works() {
    //     // let mut ss = scan_stdin();
    //     // println!("You typed: `{}`", ss.scan().unwrap(): String);
    //     // println!("You typed: `{}`", ss.scan_to(",").unwrap(): String);

    //     // scanln!("Hello, {}!", s);
    //     let mut ss = scan_stdin();
    //     ss.expect("Hello, ").unwrap();
    //     let s = ss.scan_to("!").unwrap();
    //     println!("Good bye, {}!", s: String);
    //     panic!();
    // }
}
