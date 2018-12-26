#![feature(proc_macro_hygiene)]
#![feature(type_ascription)]

extern crate darkly;

use darkly::{scanln, scanlns};

// note: should not be necessary since we add to macro
// extern crate darkly_scanner;

fn main() {
    // scanln!("hello {}foo", x: u32);
    // println!("you entered `{}`", x);
    // assert!(x == 42);

    // let x: u32 = scanln!("hello {}foo");
    // println!("you entered `{}`", x);
    // assert!(x == 42);

    for x in scanlns!("hello {}foo") {
        println!("you entered `{}`", x: u32);
    }
    println!("done");

    // for (x, y) in scanlns!("{}, {}") {
    //     println!("you entered `{}, {}`", x: u32, y:i32);
    // }
    // println!("done");
}
