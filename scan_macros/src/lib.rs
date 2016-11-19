#![feature(specialization)]
#![feature(type_ascription)]
#![feature(conservative_impl_trait)]
#![feature(plugin, plugin_registrar, rustc_private)]
#![crate_type = "dylib"]

// TODO
// if we ever fix specialization, we should be able to avoid the unwraps here
// (and do it in the scanner?)

#![plugin(proc_macro_plugin)]

extern crate proc_macro_tokens;
extern crate rustc_plugin;
extern crate syntax;

use proc_macro_tokens::prelude::*;
use rustc_plugin::Registry;
use syntax::ast;
// note used by unquote or quote!, should be imported themselves
use syntax::ast::Lit;
use syntax::ext::proc_macro_shim::prelude::*;
use syntax::ext::base::SyntaxExtension;
use syntax::parse::{ParseSess, new_parser_from_tts};
use syntax::parse::common::SeqSep;
use syntax::parse::token::BinOpToken;
use syntax::ptr::P;

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut Registry) {
    reg.register_syntax_extension(token::intern("scanln"),
                                  SyntaxExtension::ProcMacro(Box::new(scanln)));
}

fn scanln(args: TokenStream) -> TokenStream {
    // note: shouldn't have to come up with these
    let sess = ParseSess::new();
    let mut parser = new_parser_from_tts(&sess, args.to_tts());
    // note: nice parsing API?
    let expr_list = parser.parse_seq_to_before_end(&token::CloseDelim(token::Paren),
                                                   SeqSep::trailing_allowed(token::Comma),
                                                   |p| Ok(p.parse_expr()?));
    // note: error reporting
    assert!(!expr_list.is_empty(), "scanln requires at least a literal string argument");

    let chunks = process_lit_str(&expr_list[0]);
    let args = process_args(&expr_list[1..]);

    assert!(args.len() == count_holes(&chunks), "Mismatched number of directives and arguments");

    // Prelude
    // extern crate scan;
    // use scan::{scan_stdin, Scanner};
    // let scanner = scan_stdin();

    // note: can we make appending tokens easier?
    let mut tokens = qquote!(extern crate scan;);
    // note: should be extend/append, not functional concat
    tokens = TokenStream::concat(tokens, qquote!(use scan::{scan_stdin, Scanner};));
    // TODO note - qquote can't seem to handle empty parens
    let t2 = qquote!(let scanner = scan_stdin;);
    tokens = TokenStream::concat(tokens, t2);

    let mut hole_count = 0;
    for c in chunks {
        match c {
            Chunk::Text(ref s) => {
                // TODO - string literals in tokens
                // scanner.expect("$s").unwrap_or_else(|e| panic!("Error in scanln: expected `$s`, found `{}`", e));
                //tokens = TokenStream::concat(tokens, qquote!(scanner.expect("unquote s").unwrap_or_else(|e| panic!("Error in scanln: expected `unquote s`, found `{}`", e));));
            }
            Chunk::Directive(DirKind::Hole) => {
                // TODO
                // TODO scan or scan_to depending on if there is a text chunk next
                match args[hole_count] {
                    Arg::Ident(ref ident) => {
                        // note easier way to use idents, etc.
                        // single token, unquote without making tokens stream
                        let ident = TokenStream::from_tokens(vec![token::Ident(*ident)]);
                        // let $ident = scanner.scan().unwrap_or_else(|e| panic!("Error in scanln: expected value for `$ident`, found `{}`", e));
                        // note: would be nice to have $foo instead of unquote foo, unquote(foo) should work but gives warning
                        // TODO scan => scan()
                        // TODO causing an error abount Str_?
                        tokens = TokenStream::concat(tokens, qquote!(let unquote ident  = scanner.scan.unwrap_or_else(|e| panic!("Error in scanln: expected value for `unquote ident`, found `{}`", e));));
                    }
                    Arg::Typed(ref ident, ref ty) => {
                        let ident = TokenStream::from_tokens(vec![token::Ident(*ident)]);
                        // TODO need to convert ast::Ty to tokens
                        let ty = TokenStream::from_tokens(panic!());
                        // let $ident: $ty = scanner.scan().unwrap_or_else(|e| panic!("Error in scanln: expected `$ty`, found `{}`", e));
                        tokens = TokenStream::concat(tokens, qquote!(let unquote ident: unquote ty = scanner.scan().unwrap_or_else(|e| panic!("Error in scanln: expected `unquote ty`, found `{}`", e));));
                    }
                }

                hole_count += 1;
            }
            Chunk::Directive(DirKind::DebugHole) => unimplemented!(),
        }
    }

    // TODO wrap in block
    tokens
}

#[derive(Eq, PartialEq, Debug, Clone)]
enum Chunk {
    Text(String),
    Directive(DirKind),
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
            return tokenise_format_str(s);
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
                if p.segments.len() != 1 || !p.segments[0].parameters.is_empty() {
                    panic!("Expected identifier, found path: {:?}", p);
                }

                Arg::Ident(p.segments[0].identifier.clone())
            }
            ast::ExprKind::Type(ref e, ref t) => {
                if let ast::ExprKind::Path(None, ref p) = e.node {
                    if p.segments.len() != 1 || !p.segments[0].parameters.is_empty() {
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
    use scan::*;
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
