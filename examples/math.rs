
#[macro_use]
extern crate lazy;

use lazy::Thunk;

type Float64 = Thunk<f64>; // Haskell, anyone?

fn complicated_function() -> f64 {
    let mut y = 1.0;
    (1 .. 1000000001)
        .map(|i| i as f64)
        .map(|f| { y += y/f; f+y })
        .map(f64::sqrt)
        .zip(0 .. 1000000000)
        .map(|(f, i)| if i % 2 == 0 { -f } else { f })
        .sum()
}

fn func(p: bool, a: Float64, b: Float64) -> Float64 {
    if p { a } else { b }
}

fn main() {
    let a = lazy!(complicated_function()) * lazy!(complicated_function());
    let b = ready!(5.0);
    let p = true;
    let result = func(p, a, b);
    println!("{}", result);
}
