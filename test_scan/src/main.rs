#![feature(plugin)]
#![plugin(scan_macros)]
#![feature(type_ascription)]

// note: should not be necessary since we add to macro
extern crate scan;

fn main() {
    scanln!("hello {}foo", x: u32);
    //let x = x: u32;
    println!("you entered `{}`", x);
    assert!(x == 42);
}
