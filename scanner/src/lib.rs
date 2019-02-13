
extern crate darkly_macros;
extern crate proc_macro_hack;


#[proc_macro_hack::proc_macro_hack]
pub use darkly_macros::scanln;
pub use crate as darkly;



pub trait Scanner {}

pub fn scan_stdin<'a>() -> impl Scanner + 'a {
    LineReadScanner {}
}

pub struct LineReadScanner {
}

impl Scanner for LineReadScanner {}
