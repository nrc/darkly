#![feature(pattern)]
#![feature(question_mark)]
#![feature(specialization)]
#![feature(type_ascription)]
#![feature(conservative_impl_trait)]

// Questions
// Strongly linked to char/String, should it be more generic? (Pattern is str based)
// Could it be no-std?
// Can we impl Iterator for Scanner
// Should we return the result, rather than using this &mut bullshit? Then do the assignment in the macro?

// TODO
// delimited scanning
// non-line-broken scanning
// ctor functions - stdin, Path, file, string

// References
// https://doc.rust-lang.org/nightly/std/fmt/index.html
// https://docs.oracle.com/javase/7/docs/api/java/util/Scanner.html
// https://en.wikipedia.org/wiki/Scanf_format_string
// https://github.com/DanielKeep/rust-scan

use std::cmp::min;
use std::io::{Read, BufReader, BufRead};
use std::str::pattern::Pattern;
use std::str::FromStr;

// TODO Serde
pub trait Deserialize {}

pub trait Scanner {
    fn expect<'a, P: Pattern<'a>>(&'a mut self, p: P) -> Result<usize, String>;

    fn has_next(&mut self) -> bool;
    // Err case is always empty string
    fn next(&mut self) -> Result<char, String>;

    // Reads until str is full or to break
    fn scan_str(&mut self, result: &mut str) -> Result<usize, String>;
    fn scan_str_to<'a, P: Pattern<'a>>(&'a mut self, result: &mut str, next: P) -> Result<usize, String>;

    // TODO these should return their results
    fn scan<T: FromStr>(&mut self, result: &mut T) -> Result<usize, String>;
    fn scan_to<'a, T: FromStr, P: Pattern<'a>>(&'a mut self, result: &mut T, next: P) -> Result<usize, String>;

    // TODO these should return their results
    fn scan_de<T: Deserialize>(&mut self, _result: &mut T) -> Result<usize, String> { unimplemented!(); }
    fn scan_de_to<'a, T: Deserialize, P: Pattern<'a>>(&'a mut self, _result: &mut T, _next: P) -> Result<usize, String> { unimplemented!(); }
}


// fn scan_from_serialiszed<T: ScanInput>(x: T)
//     where <T as ScanInput>::Scannable: Deserialize
// {}

// Is not kept in a state of readiness - you must call advance_line to re-establish
// invariants.
// Invariants:
// cur_line.is_some() => cur_pos < cur_line.unwrap().len()
// cur_line.is_some() <=> data to read
pub struct LineReadScanner<R: Read> {
    reader: BufReader<R>,
    cur_line: Option<String>,
    cur_pos: usize,
}

impl<R: Read> LineReadScanner<R> {
    pub fn new(reader: R) -> LineReadScanner<R> {
        LineReadScanner {
            reader: BufReader::new(reader),
            cur_line: None,
            cur_pos: 0,
        }
    }

    fn read_line(&mut self) {
        let mut s = String::new();
        match self.reader.read_line(&mut s) {
            Ok(n) if n == 0 => self.cur_line = None,
            Ok(_) => self.cur_line = Some(s),
            Err(_) => self.cur_line = None,
        }
        self.cur_pos = 0;
    }

    // Assures that we are in a cononical state, i.e., either we can read, or
    // self.cur_line.is_none();
    fn advance_line(&mut self) {
        let mut needs_read = true;
        loop {
            if let Some(ref line) = self.cur_line {
                // -1 because we don't want to read the newline delimiter.
                if self.cur_pos < line.len() - 1 {
                    needs_read = false;
                }
                if self.cur_pos == line.len() - 1 && line.as_bytes()[line.len() - 1] != 0xA {
                    needs_read = false;
                }
            }

            if !needs_read {
                break;
            }

            self.read_line();
            if self.cur_line.is_none() {
                break;
            }
        }
    }

    fn with_cur_line<'a, F, T>(&'a mut self, f: F) -> Result<T, String>
        where F: FnOnce(&'a str, &mut usize) -> Result<T, String>
    {
        self.advance_line();
        if let Some(ref line) = self.cur_line {
            f(line, &mut self.cur_pos)
        } else {
            Err(String::new())
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

impl<R: Read> Scanner for LineReadScanner<R> {
    fn expect<'a, P: Pattern<'a>>(&'a mut self, p: P) -> Result<usize, String> {
        self.with_cur_line(|line, cur_pos| {
            // TODO can we do this without allocating s?
            let rest = &line[*cur_pos..];
            if let Some((0, s)) = rest.match_indices(p).next() {
                *cur_pos += s.len();
                Ok(s.len())
            } else {
                Err(rest.to_owned())
            }            
        })
    }

    fn has_next(&mut self) -> bool {
        self.advance_line();
        self.cur_line.is_some()
    }

    fn next(&mut self) -> Result<char, String> {
        let result = self.with_cur_line(|line, cur_pos| {
            let rest = &line[*cur_pos..];
            if let Some(c) = rest.chars().next() {
                *cur_pos += c.len_utf8();
                Ok(c)
            } else {
                Err(rest.to_owned())
            }
        });

        if result.is_err() {
            self.cur_line = None;
        }

        result
    }

    fn scan_str(&mut self, result: &mut str) -> Result<usize, String> {
        self.with_cur_line(|line, cur_pos| {
            let end = min(*cur_pos + result.len(), line.len());
            // TODO memcpy here? Or at least hoist the as_bytes
            // TODO set length
            unsafe {
                let mres = ::std::mem::transmute::<&mut str, &mut [u8]>(result);
                for i in *cur_pos..end {
                    mres[i - *cur_pos] = line.as_bytes()[i];
                }
            }
            *cur_pos = end;
            Ok(result.len())
        })
    }

    fn scan_str_to<'a, P: Pattern<'a>>(&'a mut self, result: &mut str, next: P) -> Result<usize, String> {
        self.with_cur_line(|line, cur_pos| {
            let rest = &line[*cur_pos..];
            match rest.match_indices(next).next() {
                Some((index, s)) => {
                    let end = min(result.len(), index);
                    // TODO memcpy here? Or at least hoist the as_bytes
                    // TODO set length
                    unsafe {
                        let mres = ::std::mem::transmute::<&mut str, &mut [u8]>(result);
                        for i in 0..end {
                            mres[i] = rest.as_bytes()[i];
                        }
                    }
                    *cur_pos += index + s.len();
                    Ok(result.len())
                }
                None => {
                    let end = min(result.len(), rest.len());
                    // TODO memcpy here? Or at least hoist the as_bytes
                    // TODO set length
                    unsafe {
                        let mres = ::std::mem::transmute::<&mut str, &mut [u8]>(result);
                        for i in 0..end {
                            mres[i] = rest.as_bytes()[i];
                        }
                    }
                    *cur_pos = line.len();
                    Ok(result.len())
                }
            }
        })        
    }

    fn scan<T: FromStr>(&mut self, result: &mut T) -> Result<usize, String> {
        let result = self.with_cur_line(|line, cur_pos| {
            let rest = &line[*cur_pos..];
            LineReadScanner::<R>::scan_internal(rest, result)
        });
        self.cur_line = None;
        result
    }

    fn scan_to<'a, T: FromStr, P: Pattern<'a>>(&'a mut self, result: &mut T, next: P) -> Result<usize, String> {
        self.with_cur_line(|line, cur_pos| {
            let rest = &line[*cur_pos..];
            match rest.match_indices(next).next() {
                Some((i, s)) => {
                    *cur_pos += i + s.len();
                    LineReadScanner::<R>::scan_internal(&rest[..i], result)
                }
                None => {
                    *cur_pos = line.len();
                    LineReadScanner::<R>::scan_internal(rest, result)
                }
            }
        })
    }
}

pub fn str_scanner<'a>(input: &'a str) -> impl Scanner + 'a {
    LineReadScanner::new(input.as_bytes())
}

fn main() {

    // let mut ss = str_scanner("Hello, world!");

    // ss.expect("Hello").unwrap();
    // ss.expect(',').unwrap();
    // ss.expect(' ').unwrap();
    // while ss.has_next() {
    //     println!("{}", ss.next().unwrap());
    // }

    // let mut ss = str_scanner("Hello, world!");

    // ss.next().unwrap();
    // ss.next().unwrap();

    // let mut s = "     ".to_owned();
    // ss.scan_str(&mut s).unwrap();
    // println!("`{}`", s);
    // let mut s = String::new();
    // ss.scan(&mut s).unwrap();
    // println!("`{}`", s);
    // assert!(!ss.has_next());

    // let mut ss = str_scanner("Hello, world!");
    // let mut s = String::new();
    // ss.scan_to(&mut s, ",").unwrap();
    // println!("`{}`", s);
    // ss.next().unwrap();
    // ss.scan(&mut s).unwrap();
    // println!("`{}`", s);

    // let mut ss = str_scanner("Hello, world!");
    // assert!(ss.expect("Hello").unwrap() == 5);
    // ss.next().unwrap();
    // ss.next().unwrap();
}
