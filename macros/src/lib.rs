#![feature(specialization)]
#![feature(type_ascription)]

// TODO
// if we ever fix specialization, we should be able to avoid the unwraps here
// (and do it in the scanner?)

extern crate proc_macro;
extern crate rustc_plugin;
extern crate syntax;
extern crate syntax_pos;

use rustc_plugin::Registry;
use syntax::ast;
use syntax::ext::base::{SyntaxExtension, ProcMacro, ExtCtxt};
use syntax::parse::filemap_to_stream;
use syntax::parse::common::SeqSep;
use syntax::parse::token::{self, Token, Lit};
use syntax::print::pprust;
use syntax::ptr::P;
use syntax::symbol::Symbol;
use syntax::tokenstream::TokenStream;
use syntax_pos::Span;

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_syntax_extension(Symbol::intern("scanln"),
                                  SyntaxExtension::ProcMacro(Box::new(ScanLn)));
}

impl ProcMacro for ScanLn {
    fn expand<'cx>(&self,
                   ecx: &'cx mut ExtCtxt,
                   _span: Span,
                   ts: TokenStream)
                   -> TokenStream {
        self.expand(ts, ecx)
    }
}

struct ScanLn;

impl ScanLn {
    fn expand_expr_form(&self, chunks: Vec<Chunk>) -> TokenStream {
        let mut program = self.prelude();

        let mut elements = vec![];

        let mut chunks = chunks.into_iter().peekable();
        while let Some(c) = chunks.next() {
            match c {
                Chunk::Text(ref s) => {
                    program.push(self.text_chunk(s));
                }
                Chunk::Directive(DirKind::Hole) => {
                    let next = chunks.peek().and_then(|n| match *n {
                        Chunk::Text(_) => Some(()),
                        Chunk::Directive(_) => None,
                    });

                    // TODO/note can we use gensym here?
                    let name = format!("__scan_var_{}", elements.len());
                    let ident1 = token::Ident(ast::Ident::from_str(&name));
                    let ident2 = ident1.clone();
                    let ident3 = ident1.clone();
                    let ident4 = ident1.clone();
                    elements.push(quote!($ident4,));

                    // TODO refactor with expand?
                    match next {
                        // let $ident = scanner.scan().unwrap_or_else(|e| panic!("Error in scanln: expected value for `$ident`, found `{}`", e));
                        None => {
                            program.push(quote!(let $ident1: Result<_, String> = scanner.scan();));
                            // note: should be simpler
                            let panic_msg = Token::Literal(Lit::Str_(Symbol::intern(&format!("Error in scanln: expected value for `{}`, found `{{}}`", name))), None);
                            program.push(quote!(let $ident2 = $ident3.unwrap_or_else(|e| panic!($panic_msg, e));));
                        }
                        // let $ident = scanner.scan_to($t).unwrap_or_else(|e| panic!("Error in scanln: expected value for `$ident`, then `$t`, found `{}`", e));
                        Some(_) => {
                            let t = chunks.next().unwrap().expect_text();
                            let text = Token::Literal(Lit::Str_(Symbol::intern(&t)), None);
                            program.push(quote!(let $ident1: Result<_, String> = scanner.scan_to($text);));
                            let panic_msg = Token::Literal(Lit::Str_(Symbol::intern(&format!("Error in scanln: expected value for `{}`, then `{}`, found `{{}}`", name, t))), None);
                            program.push(quote!(let $ident2 = $ident3.unwrap_or_else(|e| panic!($panic_msg, e));));
                        }
                    }
                }
                Chunk::Directive(DirKind::DebugHole) => unimplemented!(),
            }
        }

        // Put all the components together into a tuple.
        let elements: TokenStream = elements.into_iter().collect();
        program.push(quote!(($elements)));

        let program: TokenStream = program.into_iter().collect();
        quote!({ $program })
    }

    fn prelude(&self) -> Vec<TokenStream> {
        // `extern crate darkly_scanner;`
        // `use darkly_scanner::{scan_stdin, Scanner};`
        // `let scanner = scan_stdin();`

        // note: this requires the user have scan in their Cargo.toml
        let extern_crate = quote!(extern crate darkly_scanner;);
        let imports = quote!(use darkly_scanner::{scan_stdin, Scanner};);
        let decl = quote!(let mut scanner = scan_stdin(););

        vec![extern_crate, imports, decl]
    }

    fn text_chunk(&self, s: &str) -> TokenStream {
        // scanner.expect("$s").unwrap_or_else(|e| panic!("Error in scanln: expected `$s`, found `{}`", e));
        let expect_msg = Token::Literal(Lit::Str_(Symbol::intern(s)), None);
        let panic_msg = Token::Literal(Lit::Str_(Symbol::intern(&format!("Error in scanln: expected `{}`, found `{{}}`", s))), None);
        quote!(scanner.expect($expect_msg).unwrap_or_else(|e| panic!($panic_msg, e));)
    }

    fn expand(&self, args: TokenStream, cx: &mut ExtCtxt) -> TokenStream {
        // note: nice parsing API?
        let mut parser = cx.new_parser_from_tts(&args.trees().collect::<Vec<_>>());
        let expr_list = parser.parse_seq_to_before_end(&token::Eof,
                                                       SeqSep::trailing_allowed(token::Comma),
                                                       |p| Ok(p.parse_expr()?));
        // note: error reporting
        assert!(!expr_list.is_empty(), "scanln requires at least a literal string argument");

        let chunks = process_lit_str(&expr_list[0]);
        let args = process_args(&expr_list[1..]);

        if args.len() == 0 {
            return self.expand_expr_form(chunks);
        }

        assert!(args.len() == count_holes(&chunks), "Mismatched number of directives and arguments");

        let mut program = self.prelude();

        let mut hole_count = 0;
        let mut chunks = chunks.into_iter().peekable();
        while let Some(c) = chunks.next() {
            match c {
                Chunk::Text(ref s) => {
                    program.push(self.text_chunk(s));
                }
                Chunk::Directive(DirKind::Hole) => {
                    let next = chunks.peek().and_then(|n| match *n {
                        Chunk::Text(_) => Some(()),
                        Chunk::Directive(_) => None,
                    });
                    match args[hole_count] {
                        Arg::Ident(ref ident) => {
                            // note easier way to use idents?
                            // note get around cloning? - quote! should take by referece
                            let ident1 = token::Ident(*ident);
                            let ident2 = ident1.clone();
                            let ident3 = ident1.clone();

                            match next {
                                // let $ident = scanner.scan().unwrap_or_else(|e| panic!("Error in scanln: expected value for `$ident`, found `{}`", e));
                                None => {
                                    program.push(quote!(let $ident1: Result<_, String> = scanner.scan();));
                                    // note: should be simpler
                                    let panic_msg = Token::Literal(Lit::Str_(Symbol::intern(&format!("Error in scanln: expected value for `{}`, found `{{}}`", ident))), None);
                                    program.push(quote!(let $ident2 = $ident3.unwrap_or_else(|e| panic!($panic_msg, e));));
                                }
                                // let $ident = scanner.scan_to($t).unwrap_or_else(|e| panic!("Error in scanln: expected value for `$ident`, then `$t`, found `{}`", e));
                                Some(_) => {
                                    let t = chunks.next().unwrap().expect_text();
                                    let text = Token::Literal(Lit::Str_(Symbol::intern(&t)), None);
                                    program.push(quote!(let $ident1: Result<_, String> = scanner.scan_to($text);));
                                    let panic_msg = Token::Literal(Lit::Str_(Symbol::intern(&format!("Error in scanln: expected value for `{}`, then `{}`, found `{{}}`", ident, t))), None);
                                    program.push(quote!(let $ident2 = $ident3.unwrap_or_else(|e| panic!($panic_msg, e));));
                                }
                            }
                        }
                        Arg::Typed(ref ident, ref ty) => {
                            let ident1 = token::Ident(*ident);
                            let ident2 = ident1.clone();
                            let ident3 = ident1.clone();
                            // note: would be nice for the user not to know about parse_sess, etc, and for this to be easy
                            let ty_str = pprust::ty_to_string(ty);
                            let ty1 = filemap_to_stream(cx.parse_sess, cx.parse_sess.codemap().new_filemap("<darkly input>".to_owned(), ty_str.clone()));
                            let ty2 = ty1.clone();

                            // TODO refactor with above
                            match next {
                                // let $ident: $ty = scanner.scan().unwrap_or_else(|e| panic!("Error in scanln: expected `$ty`, found `{}`", e));
                                None => {
                                    program.push(quote!(let $ident1: Result<$ty1, String> = scanner.scan();));
                                    // note: easy pretty printing of simple stuff?
                                    let panic_msg = Token::Literal(Lit::Str_(Symbol::intern(&format!("Error in scanln: expected `{}`, found `{{}}`", ty_str))), None);
                                    program.push(quote!(let $ident2: $ty2 = $ident3.unwrap_or_else(|e| panic!($panic_msg, e));));
                                }
                                // let $ident: $ty = scanner.scan_to($t).unwrap_or_else(|e| panic!("Error in scanln: expected `$ty`, then `$t`, found `{}`", e));
                                Some(_) => {
                                    let t = chunks.next().unwrap().expect_text();
                                    let text = Token::Literal(Lit::Str_(Symbol::intern(&t)), None);
                                    program.push(quote!(let $ident1: Result<$ty1, String> = scanner.scan_to($text);));
                                    let panic_msg = Token::Literal(Lit::Str_(Symbol::intern(&format!("Error in scanln: expected value for `{}`, then `{}`, found `{{}}`", ident, t))), None);
                                    program.push(quote!(let $ident2: $ty2 = $ident3.unwrap_or_else(|e| panic!($panic_msg, e));));
                                }
                            }
                        }
                    }

                    hole_count += 1;
                }
                Chunk::Directive(DirKind::DebugHole) => unimplemented!(),
            }
        }

        // TODO think about scoping - can't be in a block because are declaring variables, but don't want the extern crate/use/temp decls to escape
        // let program: TokenStream = program.into_iter().collect();
        // quote!({ $program })

        program.into_iter().collect()
    }
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
enum Arg {
    Ident(ast::Ident),
    Typed(ast::Ident, ast::Ty),
}

fn process_lit_str(expr: &ast::Expr) -> Vec<Chunk> {
    if let ast::ExprKind::Lit(ref l) = expr.node {
        if let ast::LitKind::Str(ref s, ast::StrStyle::Cooked) = l.node {
            return tokenise_format_str(&s.as_str());
        }
    }

    // TODO use pretty printing rather than Debug
    // Note: error reporting with spans
    panic!("Expected string literal, found: `{:?}`", expr);
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

fn process_args(exprs: &[P<ast::Expr>]) -> Vec<Arg> {
    exprs.iter().map(|e| {
        match e.node {
            ast::ExprKind::Path(None, ref p) => {
                if p.segments.len() != 1 || p.segments[0].parameters.is_some() {
                    panic!("Expected identifier, found path: {:?}", p);
                }

                Arg::Ident(p.segments[0].identifier.clone())
            }
            ast::ExprKind::Type(ref e, ref t) => {
                if let ast::ExprKind::Path(None, ref p) = e.node {
                    if p.segments.len() != 1 || p.segments[0].parameters.is_some() {
                        panic!("Expected identifier, found path: {:?}", p);
                    }
                    Arg::Typed(p.segments[0].identifier.clone(), (**t).clone())
                } else {
                    panic!("Expected identifier, found expression: {:?}", e);
                }
            }
            // TODO use pretty printing rather than Debug (and above)
            // note AST library would need a nice version
            _ => panic!("Expected identifier or type ascribed identifier, found: `{:?}`", e.node),
        }
    }).collect()
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
