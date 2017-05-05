#![feature(plugin)]
#![plugin(darkly)]
#![feature(type_ascription)]

// note: should not be necessary since we add to macro
extern crate darkly_scanner;

fn main() {
    scanln!("hello {}foo", x: u32);
    //let x = x: u32;
    println!("you entered `{}`", x);
    assert!(x == 42);
}
