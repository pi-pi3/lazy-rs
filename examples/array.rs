
#[macro_use]
extern crate lazy;

fn main() {
    // maybe it will be used, maybe not?
    // who cares? it's lazy, it doesn't take up any memory
    // (well, a couple bytes)
    let _lazy = lazy!((0_u64 .. 100000000000_u64).collect::<Vec<_>>());
    // this would actually take up `100000000 * mem::size_of::<u64>()` bytes
    // let _ready = ready!((0 .. 100000000).collect::<Vec<_>>());
    /* ... */
}
