#![feature(proc_macro_hygiene)]

extern crate darkly;

use darkly::scanln;

// note: should not be necessary since we add to macro
// extern crate darkly_scanner;

fn main() {
    // scanln!("hello {}foo", x: u32);
    // println!("you entered `{}`", x);
    // assert!(x == 42);

    let (x,): (u32,) = scanln!("hello {}foo");
    println!("you entered `{}`", x);
    assert!(x == 42);
}
