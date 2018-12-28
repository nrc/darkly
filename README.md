# Darkly

A scanner library and macros.

Example:

``` rust
fn main() {
    println!("Enter coordinates in the form (x, y)");
    scanln!("({}, {})", x: i32, y);
    let typed_y: i32 = y;
    println!("You entered x: {}, y: {}", x, typed_y);
}
```

Input of `(0, 42)` gives output of `You entered x: 0, y: 42`.

## Scan macros

Currently provides a `scanln` macro which reads a line at a time from stdin and
scans it. I plan to add `readln` for reading lines from any reader, and possibly
non-ln versions too.

The `scanln` macro attempts to be like `println` in reverse, it takes a query
string with holes and a list of variables. Each hole must match a variable.
Literal characters are matched exactly against the input, data in between is
assigned into the appropriate variables. If the input does not match the
literals, or is of the wrong type, then the scanner panics (but see below).

The variables passed to `scanln` can be untyped (e.g., `scanln!("{}", x)`) in
which case the type is inferred from the use of the variables. This generates
code like: `let x = FromStr::from_str(read(...));`.

Or they may be typed (e.g., `scanln!("{}", x: u32)`). This generates code like:
`let x: u32 = FromStr::from_str(read(...));`.

In either case, the types of variables must implement `std::str::FromStr`.


### Work in progress

* Use `{:?}` to deserialise data using Serde (c.f., `{}` which uses `FromStr`),
* `readln!` to read from a Reader, not just stdin,
* escape `{` and `}`,
* `Result`-based rather than panicking options, based on types (see below),
* Other query string features, similar to `println`, etc.

#### Non-panicking version

Currently `scanln` panics if the input does not match the query string. This is
ergonomic in simple cases, but not robust. To allow `scanln`'s users to handle
errors themselves, I plan to implement a non-panicking mode. Whether `scanln`
panics or not will depend on the type:

``` rust
scanln!("{}", x: u32); // Panics if can't parse as u32
scanln!("{}", x: Result<u32, _>); // Returns an Err if can't parse as u32
```

Implementing this is not quite possible - we need the 'lattice rule' extension
to trait specialisation. That is currently being worked on, when that lands the
above should work by extending the darkly-scan library, hopefully the macros are
ready to go.

## darkly-scanner

The underlying scanner library. Docs needed...
