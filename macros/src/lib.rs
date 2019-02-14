#![recursion_limit = "128"]

// TODO
// if we ever fix specialization, we should be able to avoid the unwraps here
// (and do it in the scanner?)

extern crate proc_macro;

use syn;

use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, ToTokens};
use syn::parse::{self, ParseStream};
use syn::{punctuated::Punctuated, token::Comma, Ident, LitStr, Token, Type};

#[proc_macro]
pub fn scanln(input: TokenStream) -> TokenStream {
    let args: StdinArgs = syn::parse(input).expect("Parsing error");
    expand_one(quote! { darkly::scan_stdin() }, args).into()
}

// TODO question should we terminate iteration on a bad match or an empty line?
#[proc_macro]
pub fn scanlns(input: TokenStream) -> TokenStream {
    let args: StdinArgs = syn::parse(input).expect("Parsing error");
    expand_iterative(quote! { darkly::scan_stdin() }, args).into()
}

#[proc_macro]
pub fn sscanln(input: TokenStream) -> TokenStream {
    let args: StrArgs = syn::parse(input).expect("Parsing error");
    let (s, args) = args.into();
    expand_one(quote! { darkly::scan_str(#s) }, args).into()
}

// TODO question should we terminate iteration on a bad match or an empty line?
#[proc_macro]
pub fn sscanlns(input: TokenStream) -> TokenStream {
    let args: StrArgs = syn::parse(input).expect("Parsing error");
    let (s, args) = args.into();
    expand_iterative(quote! { darkly::scan_str(#s) }, args).into()
}

#[proc_macro]
pub fn fscanln(input: TokenStream) -> TokenStream {
    let args: StrArgs = syn::parse(input).expect("Parsing error");
    let (s, args) = args.into();
    expand_one(quote! { darkly::scan_file_from_path(#s) }, args).into()
}

// TODO question should we terminate iteration on a bad match or an empty line?
#[proc_macro]
pub fn fscanlns(input: TokenStream) -> TokenStream {
    let args: StrArgs = syn::parse(input).expect("Parsing error");
    let (s, args) = args.into();
    expand_iterative(quote! { darkly::scan_file_from_path(#s) }, args).into()
}

fn expand_iter_form(init: TokenStream2, chunks: Vec<Chunk>) -> TokenStream2 {
    let mut chunks = chunks.into_iter().peekable();
    let mut elements = vec![];
    let mut types = vec![];
    let mut types_with_bounds = vec![];
    let mut vars = TokenStream2::new();
    // TODO we should return None rather than panicking in the chunk handlers
    while let Some(c) = chunks.next() {
        match c {
            Chunk::Text(ref s) => {
                vars.extend(iter_text_chunk(s).into_iter());
            }
            Chunk::Whitespace => {
                vars.extend(iter_ws_chunk().into_iter());
            }
            Chunk::Directive(DirKind::Hole) => {
                let next_chunk = chunks.peek().unwrap_or(EOF);
                let name = format!("__scan_var_{}", elements.len());
                let ty = Ident::new(&format!("__ScanTy_{}", elements.len()), Span::call_site());
                vars.extend(iter_expansion(&name, next_chunk).into_iter());
                types_with_bounds.push(quote! {#ty: std::str::FromStr});
                types.push(ty);
                elements.push(Ident::new(&name, Span::call_site()));
            }
            Chunk::Directive(DirKind::DebugHole) => unimplemented!(),
            Chunk::Eof => break,
        }
    }

    let (result, ty) = if elements.len() == 1 {
        let element = &elements[0];
        let ty = &types[0];
        (quote! { #element }, quote! { #ty })
    } else {
        // Put all the components together into a tuple.
        let types = types.clone();
        (quote! { (#(#elements,)*)}, quote! { (#(#types,)*)})
    };

    let types_with_bounds2 = types_with_bounds.clone();
    let types2 = types.clone();
    let types3 = types.clone();
    let result = quote! { {
        fn make_iterator<#(#types_with_bounds,)*>() -> impl Iterator<Item=#ty> {
            struct ScanIter<#(#types,)* S: darkly::Scanner> {
                scanner: S,
                pd: ::std::marker::PhantomData<#ty>,
            }

            impl<#(#types_with_bounds2,)* S: darkly::Scanner> Iterator for ScanIter<#(#types2,)* S> {
                type Item = #ty;
                fn next(&mut self) -> Option<Self::Item> {
                    #vars
                    Some(#result)
                }
            }

            let mut iter: ScanIter<#(#types3,)* _> = ScanIter {
                scanner: #init,
                pd: ::std::marker::PhantomData,
            };

            iter
        }
        make_iterator()
    } };

    result
}

fn expand_expr_form(chunks: Vec<Chunk>) -> TokenStream2 {
    let mut result = quote! {
        let mut scanner = darkly::scan_stdin();
    };
    let mut chunks = chunks.into_iter().peekable();
    let mut elements = vec![];
    while let Some(c) = chunks.next() {
        match c {
            Chunk::Text(ref s) => {
                result.extend(text_chunk(s).into_iter());
            }
            Chunk::Whitespace => {
                result.extend(ws_chunk().into_iter());
            }
            Chunk::Directive(DirKind::Hole) => {
                let next_chunk = chunks.peek().unwrap_or(EOF);
                let name = format!("__scan_var_{}", elements.len());
                result.extend(expr_expansion(&name, next_chunk).into_iter());
                elements.push(Ident::new(&name, Span::call_site()));
            }
            Chunk::Directive(DirKind::DebugHole) => unimplemented!(),
            Chunk::Eof => break,
        }
    }

    if elements.len() == 1 {
        let element = &elements[0];
        result.extend(quote! { #element }.into_iter());
    } else {
        // Put all the components together into a tuple.
        result.extend(quote! { (#(#elements,)*)}.into_iter());
    }

    quote! { { #result } }
}

fn iter_expansion(name: &str, next_chunk: &Chunk) -> TokenStream2 {
    let name = Ident::new(name, Span::call_site());
    // TODO refactor with Arg::expansion
    match next_chunk {
        Chunk::Directive(_) | Chunk::Eof => {
            quote! {
                let #name: Result<_, String> = self.scanner.scan();
                let #name = #name.ok()?;
            }
        }
        Chunk::Text(t) => {
            quote! {
                let #name: Result<_, String> = self.scanner.scan_to(#t);
                let #name = #name.ok()?;
            }
        }
        Chunk::Whitespace => {
            quote! {
                let #name: Result<_, String> = self.scanner.scan_to_whitespace();
                let #name = #name.ok()?;
            }
        }
    }
}

fn expr_expansion(name: &str, next_chunk: &Chunk) -> TokenStream2 {
    let name = Ident::new(name, Span::call_site());
    // TODO refactor with Arg::expansion
    match next_chunk {
        Chunk::Directive(_) | Chunk::Eof => {
            // TODO name is not a helpful identifier
            let panic_msg = format!(
                "Error in scanln: expected value for `{}`, found `{{}}`",
                name
            );
            quote! {
                let #name: Result<_, String> = scanner.scan();
                let #name = #name.unwrap_or_else(|e| panic!(#panic_msg, e));
            }
        }
        Chunk::Text(t) => {
            // TODO name is not a helpful identifier
            let panic_msg = format!(
                "Error in scanln: expected value for `{}`, then `{}`, found `{{}}`",
                name, t
            );
            quote! {
                let #name: Result<_, String> = scanner.scan_to(#t);
                let #name = #name.unwrap_or_else(|e| panic!(#panic_msg, e));
            }
        }
        Chunk::Whitespace => {
            // TODO name is not a helpful identifier
            let panic_msg = format!(
                "Error in scanln: expected value for `{}`, then ` `, found `{{}}`",
                name
            );
            quote! {
                let #name: Result<_, String> = scanner.scan_to_whitespace();
                let #name = #name.unwrap_or_else(|e| panic!(#panic_msg, e));
            }
        }
    }
}

fn iter_text_chunk(s: &str) -> TokenStream2 {
    quote! {
        self.scanner.expect(#s).ok()?;
    }
}

// TODO macro name in panic message
fn text_chunk(s: &str) -> TokenStream2 {
    let panic_msg = format!("Error in scanln: expected `{}`, found `{{}}`", s);
    quote! {
        darkly::Scanner::expect(&mut scanner, #s).unwrap_or_else(|e| panic!(#panic_msg, e));
    }
}

fn ws_chunk() -> TokenStream2 {
    quote! {
        darkly::Scanner::expect_whitespace(&mut scanner).unwrap_or_else(|e| panic!("Error in scanln: expected whitespace, found `{}`", e));
    }
}

fn iter_ws_chunk() -> TokenStream2 {
    quote! {
        darkly::Scanner::expect_whitespace(&mut self.scanner).unwrap_or_else(|e| panic!("Error in scanln: expected whitespace, found `{}`", e));
    }
}

fn expand_iterative(init: TokenStream2, args: StdinArgs) -> TokenStream2 {
    let chunks = process_lit_str(&args.str);

    if args.args.len() != 0 {
        panic!("arguments are not supported in iterative mode");
    }

    expand_iter_form(init, chunks)
}

fn expand_one(init: TokenStream2, args: StdinArgs) -> TokenStream2 {
    let chunks = process_lit_str(&args.str);

    if args.args.len() == 0 {
        return expand_expr_form(chunks);
    }

    assert!(
        args.args.len() == count_directives(&chunks),
        "Mismatched number of directives and arguments"
    );

    // TODO scoping of new vars vs priv names
    let mut result = quote! {
        let mut scanner = #init;
    };
    let mut hole_count = 0;
    let mut chunks = chunks.into_iter().peekable();
    while let Some(c) = chunks.next() {
        match c {
            Chunk::Text(ref s) => {
                result.extend(text_chunk(s).into_iter());
            }
            Chunk::Whitespace => {
                result.extend(ws_chunk().into_iter());
            }
            Chunk::Directive(DirKind::Hole) => {
                let next_chunk = chunks.peek().unwrap_or(EOF);
                result.extend(args.args[hole_count].expansion(next_chunk).into_iter());
                hole_count += 1;
            }
            Chunk::Directive(DirKind::DebugHole) => unimplemented!(),
            Chunk::Eof => break,
        }
    }
    result
}

#[derive(Eq, PartialEq, Debug, Clone)]
enum Chunk {
    Text(String),
    Whitespace,
    Directive(DirKind),
    Eof,
}

static EOF: &Chunk = &Chunk::Eof;

#[derive(Eq, PartialEq, Debug, Clone)]
enum DirKind {
    // {}
    Hole,
    // {:?}
    DebugHole,
}

#[derive(Debug, Clone)]
struct StdinArgs {
    str: LitStr,
    args: Punctuated<Arg, Comma>,
}

#[derive(Debug, Clone)]
struct StrArgs {
    input: LitStr,
    str: LitStr,
    args: Punctuated<Arg, Comma>,
}

impl parse::Parse for StdinArgs {
    fn parse(input: ParseStream<'_>) -> parse::Result<StdinArgs> {
        let str = input.parse()?;
        if input.peek(Comma) {
            input.parse::<Comma>()?;
        }
        let args = Punctuated::parse_terminated(input)?;

        Ok(StdinArgs { str, args })
    }
}

impl parse::Parse for StrArgs {
    fn parse(input: ParseStream<'_>) -> parse::Result<StrArgs> {
        let input_str = input.parse()?;
        input.parse::<Comma>()?;
        let str = input.parse()?;
        if input.peek(Comma) {
            input.parse::<Comma>()?;
        }
        let args = Punctuated::parse_terminated(input)?;

        Ok(StrArgs {
            input: input_str,
            str,
            args,
        })
    }
}

impl Into<(String, StdinArgs)> for StrArgs {
    fn into(self) -> (String, StdinArgs) {
        (
            self.input.value(),
            StdinArgs {
                str: self.str,
                args: self.args,
            },
        )
    }
}

#[derive(Debug, Clone)]
enum Arg {
    Ident(Ident),
    Typed(Ident, Type),
}

impl Arg {
    fn expansion(&self, next_chunk: &Chunk) -> TokenStream2 {
        match *self {
            Arg::Ident(ref ident) => match next_chunk {
                Chunk::Directive(_) | Chunk::Eof => {
                    let panic_msg = format!(
                        "Error in scanln: expected value for `{}`, found `{{}}`",
                        ident
                    );
                    quote! {
                        let #ident: Result<_, String> = darkly::Scanner::scan(&mut scanner);
                        let #ident = #ident.unwrap_or_else(|e| panic!(#panic_msg, e));
                    }
                }
                Chunk::Text(t) => {
                    let panic_msg = format!(
                        "Error in scanln: expected value for `{}`, then `{}`, found `{{}}`",
                        ident, t
                    );
                    quote! {
                        let #ident: Result<_, String> = darkly::Scanner::scan_to(&mut scanner, #t);
                        let #ident = #ident.unwrap_or_else(|e| panic!(#panic_msg, e));
                    }
                }
                Chunk::Whitespace => {
                    let panic_msg = format!(
                        "Error in scanln: expected value for `{}`, then ` `, found `{{}}`",
                        ident
                    );
                    quote! {
                        let #ident: Result<_, String> = darkly::Scanner::scan_to_whitespace(&mut scanner);
                        let #ident = #ident.unwrap_or_else(|e| panic!(#panic_msg, e));
                    }
                }
            },
            Arg::Typed(ref ident, ref ty) => match next_chunk {
                Chunk::Directive(_) | Chunk::Eof => {
                    let panic_msg = format!(
                        "Error in scanln: expected `{}`, found `{{}}`",
                        ty.into_token_stream()
                    );
                    quote! {
                        let #ident: Result<#ty, String> = darkly::Scanner::scan(&mut scanner);
                        let #ident: #ty = #ident.unwrap_or_else(|e| panic!(#panic_msg, e));
                    }
                }
                Chunk::Text(t) => {
                    let panic_msg = format!(
                        "Error in scanln: expected `{}`, then `{}`, found `{{}}`",
                        ty.into_token_stream(),
                        t
                    );
                    quote! {
                        let #ident: Result<#ty, String> = darkly::Scanner::scan_to(&mut scanner, #t);
                        let #ident: #ty = #ident.unwrap_or_else(|e| panic!(#panic_msg, e));
                    }
                }
                Chunk::Whitespace => {
                    let panic_msg = format!(
                        "Error in scanln: expected `{}`, then ` `, found `{{}}`",
                        ty.into_token_stream()
                    );
                    quote! {
                        let #ident: Result<#ty, String> = darkly::Scanner::scan_to_whitespace(&mut scanner);
                        let #ident: #ty = #ident.unwrap_or_else(|e| panic!(#panic_msg, e));
                    }
                }
            },
        }
    }
}

impl parse::Parse for Arg {
    fn parse(input: ParseStream<'_>) -> parse::Result<Arg> {
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

fn count_directives(chunks: &[Chunk]) -> usize {
    chunks
        .iter()
        .filter(|c| {
            if let &Chunk::Directive(_) = *c {
                true
            } else {
                false
            }
        })
        .count()
}

fn tokenise_format_str(s: &str) -> Vec<Chunk> {
    let mut result = vec![];

    #[derive(Copy, Clone)]
    enum State {
        Text,
        OpenBrace,
        CloseBrace,
        Hole,
        Whitespace,
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
                    State::Whitespace => {}
                }
                return result;
            }
            Some(c) => match (state, c) {
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
                (State::Text, '{') | (State::Whitespace, '{') => {
                    state = State::OpenBrace;
                }
                (State::Text, '}') | (State::Whitespace, '}') => {
                    state = State::CloseBrace;
                }
                (State::Text, ' ') | (State::Text, '\t') => {
                    if !buf.is_empty() {
                        result.push(Chunk::Text(buf));
                        buf = String::new();
                    }
                    result.push(Chunk::Whitespace);
                    state = State::Whitespace;
                }
                (State::Whitespace, ' ') | (State::Whitespace, '\t') => {}
                (State::Whitespace, c) => {
                    buf.push(c);
                    state = State::Text;
                }
                (State::Text, c) | (State::Hole, c) => {
                    buf.push(c);
                }
            },
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
    use super::{tokenise_format_str, Chunk, DirKind};

    #[test]
    fn test_tok_fmt_str() {
        assert!(tokenise_format_str("").is_empty());

        let expected = [Chunk::Text("Hello".to_owned())];
        for (c, e) in tokenise_format_str("Hello").iter().zip(expected.iter()) {
            assert_eq!(c, e);
        }

        let expected = [
            Chunk::Text("Hello,".to_owned()),
            Chunk::Whitespace,
            Chunk::Directive(DirKind::Hole),
            Chunk::Text("!".to_owned()),
            Chunk::Directive(DirKind::DebugHole),
        ];
        for (c, e) in tokenise_format_str("Hello, {}!{:?}")
            .iter()
            .zip(expected.iter())
        {
            assert_eq!(c, e);
        }

        let expected = [Chunk::Directive(DirKind::DebugHole)];
        for (c, e) in tokenise_format_str("{:?}").iter().zip(expected.iter()) {
            assert_eq!(c, e);
        }

        let expected = [
            Chunk::Text("Hello,".to_owned()),
            Chunk::Whitespace,
            Chunk::Text("{}".to_owned()),
            Chunk::Directive(DirKind::DebugHole),
            Chunk::Text("{".to_owned()),
            Chunk::Directive(DirKind::Hole),
            Chunk::Text("}!".to_owned()),
        ];
        for (c, e) in tokenise_format_str("Hello, {{}}{:?}{{{}}}!")
            .iter()
            .zip(expected.iter())
        {
            assert_eq!(c, e);
        }

        let expected = [
            Chunk::Text("Hello".to_owned()),
            Chunk::Whitespace,
            Chunk::Directive(DirKind::Hole),
            Chunk::Whitespace,
        ];
        let toks = tokenise_format_str("Hello {} ");
        assert_eq!(toks.len(), expected.len());
        for (c, e) in toks.iter().zip(expected.iter()) {
            assert_eq!(c, e);
        }
    }
}
