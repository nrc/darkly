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

    // for x in scanlns!("hello {}foo") {
    //     println!("you entered `{}`", x: u32);
    // }
    // println!("done");

    // for (x, y) in scanlns!("{}, {}") {
    //     println!("you entered `{}, {}`", x: u32, y:i32);
    // }
    // println!("done");

    // position=<-51031,  41143> velocity=< 5, -4>
    scanln!("position=< {}, {}> velocity=< {}, {}>", a, b, c, d);
    println!("{} {} {} {}", a: i32, b: i32, c: i32, d: i32);
}
