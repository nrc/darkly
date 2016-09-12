#![feature(pattern)]
#![feature(question_mark)]

// Questions
// Strongly linked to char/String, should it be more generic? (Pattern is str based)
// Could it be no-std?
// Can we impl Iterator for Scanner
// Should we return the result, rather than using this &mut bullshit? Then do the assignment in the macro?

// TODO
// typedef Result<usize, String>
// delimited scanning
// Replace StrScanner with typedef (or something) for ReadScanner<StringReader>

use std::str::pattern::Pattern;
use std::str::FromStr;

// TODO Serde
pub trait Deserialize {}

pub trait Scanner {
    fn expect<'a, P: Pattern<'a>>(&'a mut self, p: P) -> Result<usize, String>;
    fn scan_pat<'a, P: Pattern<'a>>(&'a mut self, p: P, result: &mut String) -> Result<usize, String>;

    fn has_next(&self) -> bool;
    // Err case is always empty string
    fn next(&mut self) -> Result<char, String>;

    // Reads until str is full (TODO or next delimiter?)
    fn scan_str(&mut self, result: &mut str) -> Result<usize, String>;
    // Reads to end of input
    // TODO could also be `get_rest` or something
    fn scan_string(&mut self, result: &mut String) -> Result<usize, String>;

    fn scan<T: FromStr>(&mut self, result: &mut T) -> Result<usize, String>;
    fn scan_to<'a, T: FromStr, P: Pattern<'a>>(&'a mut self, result: &mut T, next: P) -> Result<usize, String>;

    fn scan_de<T: Deserialize>(&mut self, _result: &mut T) -> Result<usize, String> { unimplemented!(); }
    fn scan_de_to<'a, T: Deserialize, P: Pattern<'a>>(&'a mut self, _result: &mut T, _next: P) -> Result<usize, String> { unimplemented!(); }
}

// TODO blanket impl for Pattern, FromStr, Option<T: Scannable>, Result<T: Scannable, String>. Return Result<T, String>. Infer what to do.
pub trait Scannable {}

pub struct StrScanner<'a> {
    input: &'a str,
    position: usize,
}

impl<'a> StrScanner<'a> {
    pub fn new(input: &str) -> StrScanner {
        StrScanner {
            input: input,
            position: 0,
        }
    }

    fn scan_internal<T: FromStr>(input: &str, result: &mut T) -> Result<usize, String> {
        match FromStr::from_str(input) {
            Ok(r) => {
                *result = r;
                Ok(input.len())
            }
            Err(_) => Err(input.to_owned())
        }
    }
}

impl<'b> Scanner for StrScanner<'b> {
    fn expect<'a, P: Pattern<'a>>(&'a mut self, p: P) -> Result<usize, String> {
        let rest = &self.input[self.position..];
        if let Some((0, s)) = rest.match_indices(p).next() {
            self.position += s.len();
            return Ok(s.len());
        }
        Err(self.input.to_owned())
    }
    fn scan_pat<'a, P: Pattern<'a>>(&'a mut self, p: P, result: &mut String) -> Result<usize, String> {
        let rest = &self.input[self.position..];
        if let Some((0, s)) = rest.match_indices(p).next() {
            self.position += s.len();
            *result = s.to_owned();
            return Ok(s.len());
        }
        Err(self.input.to_owned())
    }

    fn has_next(&self) -> bool {
        self.position < self.input.len()
    }
    fn next(&mut self) -> Result<char, String> {
        if !self.has_next() {
            return Err(String::new());
        }

        let rest = &self.input[self.position..];
        self.position += 1;

        rest.chars().next().ok_or(String::new())
    }

    fn scan_str(&mut self, result: &mut str) -> Result<usize, String> {
        let end = min(self.position + result.len(), self.input.len());
        // TODO memcpy here? Or at least hoist the as_bytes
        unsafe {
            let mres = ::std::mem::transmute::<&mut str, &mut [u8]>(result);
            for i in self.position..end {
                mres[i - self.position] = self.input.as_bytes()[i];
            }
        }
        self.position = end;
        Ok(result.len())
    }

    fn scan_string(&mut self, result: &mut String) -> Result<usize, String> {
        let rest = &self.input[self.position..];
        self.position = self.input.len();
        *result = rest.to_owned();
        Ok(rest.len())
    }

    fn scan<T: FromStr>(&mut self, result: &mut T) -> Result<usize, String> {
        let rest = &self.input[self.position..];
        self.position = self.input.len();
        StrScanner::scan_internal(rest, result)
    }

    // TODO should this have an _and_consume variant?
    fn scan_to<'a, T: FromStr, P: Pattern<'a>>(&'a mut self, result: &mut T, next: P) -> Result<usize, String> {
        let rest = &self.input[self.position..];
        match rest.find(next) {
            Some(i) => {
                self.position = i;
                StrScanner::scan_internal(&rest[..i], result)
            }
            None => {
                self.position = self.input.len();
                StrScanner::scan_internal(rest, result)
            }
        }
    }
}

fn main() {
    // let mut ss = StrScanner::new("Hello, world!");

    // ss.next().unwrap();
    // ss.next().unwrap();

    // let mut s = "    ".to_owned();
    // ss.scan_str(&mut s);
    // println!("`{}`", s);
    // let mut s = String::new();
    // ss.scan_string(&mut s);
    // println!("`{}`", s);
    // assert!(!ss.has_next());

    // TODO test scan_to/scan
    // let mut ss = StrScanner::new("Hello, world!");
    // let mut s = String::new();
    // ss.scan_to(&mut s, ",").unwrap();
    // println!("`{}`", s);
    // ss.next().unwrap();
    // ss.next().unwrap();
    // ss.scan(&mut s).unwrap();
    // println!("`{}`", s);

    let mut ss = StrScanner::new("Hello, world!");
    assert!(ss.expect("Hello").unwrap() == 5);
    ss.next().unwrap();
    ss.next().unwrap();
    let mut s = String::new();
    ss.scan_pat("world", &mut s).unwrap();
    println!("`{}`", s);    
}

// Is there no min function in std?
fn min(a: usize, b:usize) -> usize {
    if a <= b {
        a
    } else {
        b
    }
}
