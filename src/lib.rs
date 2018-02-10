#![feature(const_fn)]
#![feature(fnbox)]

use std::boxed::FnBox;
use std::cell::Cell;
use std::fmt::{self, Debug, Display};
use std::cmp::Ordering;
use std::ops::*;

#[macro_export]
macro_rules! ready {
    ($e:expr) => {
        {
            use $crate::Thunk;
            Thunk::ready($e)
        }
    }
}

#[macro_export]
macro_rules! lazy {
    ($e:expr) => {
        {
            use $crate::Thunk;
            Thunk::lazy(Box::new(move || $e))
        }
    };
    (clone($( $arg:ident ),*) $e:block) => {
        {
            use $crate::Thunk;
            $(
                let $arg = $arg.clone();
            )*
            Thunk::lazy(Box::new(move || $e))
        }
    }
}

#[macro_export]
macro_rules! lazy_move {
    ($e:expr) => {
        {
            use $crate::Thunk;
            Thunk::lazy(Box::new(move || $e))
        }
    }
}

enum Lazy<T> {
    Lazy(Box<FnBox() -> T>),
    Ready(T),
    Nil,
}

impl<T: Debug> Debug for Lazy<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Lazy::Lazy(_) => write!(f, "Lazy(...)"),
            Lazy::Ready(ref y) => write!(f, "Ready({:?})", y),
            Lazy::Nil => write!(f, "Nil"),
        }
    }
}

impl<T> Default for Lazy<T> {
    fn default() -> Lazy<T> {
        Lazy::Nil
    }
}

pub struct Thunk<T> {
    inner: Cell<Lazy<T>>,
}

impl<T> Thunk<T> {
    const fn with_inner(inner: Lazy<T>) -> Thunk<T> {
        Thunk {
            inner: Cell::new(inner),
        }
    }

    pub const fn lazy(f: Box<FnBox() -> T>) -> Thunk<T> {
        Thunk::with_inner(Lazy::Lazy(f))
    }

    pub const fn ready(y: T) -> Thunk<T> {
        Thunk::with_inner(Lazy::Ready(y))
    }

    pub fn is_ready(&self) -> bool {
        let inner = self.inner.as_ptr();
        unsafe {
            match *inner {
                Lazy::Lazy(_) => false,
                Lazy::Ready(_) => true,
                Lazy::Nil => unreachable!(),
            }
        }
    }

    fn inner(&self) -> *mut T {
        self.force();

        let inner = self.inner.as_ptr();
        unsafe {
            match *inner {
                Lazy::Lazy(_) => unreachable!(),
                Lazy::Ready(ref mut y) => y as *mut _,
                Lazy::Nil => unreachable!(),
            }
        }
    }

    fn force(&self) {
        let inner = self.inner.take();
        match inner {
            Lazy::Lazy(f) => self.inner.set(Lazy::Ready(FnBox::call_box(f, ()))),
            Lazy::Ready(y) => self.inner.set(Lazy::Ready(y)),
            Lazy::Nil => unreachable!(),
        }
    }

    pub fn unwrap(self) -> T {
        let inner = self.inner.into_inner();
        match inner {
            Lazy::Lazy(f) => FnBox::call_box(f, ()),
            Lazy::Ready(y) => y,
            Lazy::Nil => unreachable!(),
        }
    }
}

impl<T: Clone + Copy> Thunk<T> {
    pub fn get(&self) -> T {
        unsafe { *self.inner() }
    }
}

impl<T> From<T> for Thunk<T> {
    fn from(y: T) -> Thunk<T> {
        Thunk::ready(y)
    }
}

impl<T> AsRef<T> for Thunk<T> {
    fn as_ref(&self) -> &T {
        self
    }
}

impl<T> AsMut<T> for Thunk<T> {
    fn as_mut(&mut self) -> &mut T {
        self
    }
}

impl<T> Deref for Thunk<T> {
    type Target = T;

    fn deref(&self) -> &T {
        unsafe { self.inner().as_ref().unwrap() }
    }
}

impl<T> DerefMut for Thunk<T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.inner().as_mut().unwrap() }
    }
}

impl<T: Default + 'static> Default for Thunk<T> {
    fn default() -> Thunk<T> {
        Thunk::lazy(Box::new(T::default))
    }
}

impl<T: Clone> Clone for Thunk<T> {
    fn clone(&self) -> Thunk<T> {
        let val: &T = self;
        Thunk::ready(val.clone())
    }
}

impl<T: Debug> Debug for Thunk<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Thunk {0} inner: Cell {0} value: {2:?} {1} {1}",
            '{',
            '}',
            unsafe { self.inner.as_ptr().as_ref().unwrap() }
        )
    }
}

impl<T: Display> Display for Thunk<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let val: &T = self;
        Display::fmt(val, f)
    }
}

impl<T: PartialEq<U>, U> PartialEq<Thunk<U>> for Thunk<T> {
    fn eq(&self, rhs: &Thunk<U>) -> bool {
        let a: &T = self;
        let b: &U = rhs;
        a == b
    }
}

impl<T: PartialEq + Eq> Eq for Thunk<T> {}

impl<T: PartialOrd<U>, U> PartialOrd<Thunk<U>> for Thunk<T> {
    fn partial_cmp(&self, other: &Thunk<U>) -> Option<Ordering> {
        let a: &T = self;
        let b: &U = other;
        a.partial_cmp(b)
    }
}

impl<T: PartialOrd + Ord> Ord for Thunk<T> {
    fn cmp(&self, other: &Thunk<T>) -> Ordering {
        let a: &T = self;
        let b: &T = other;
        a.cmp(b)
    }
}

macro_rules! impl_op {
    ( $trait:path { $f:ident ( $a:ident) } ) => {
        impl<T: $trait + 'static> $trait for Thunk<T> {
            type Output = Thunk<<T as $trait>::Output>;

            fn $f(self) -> Self::Output {
                Thunk::lazy(Box::new(move || self.unwrap().$f()))
            }
        }
    };
    ( $t1:path => $t2:path { $f:ident ( $a:ident, $b:ident ) } ) => {
        impl<T: $t1 + 'static, U: 'static> $t2 for Thunk<T> {
            type Output = Thunk<<T as $t1>::Output>;

            fn $f(self, rhs: Thunk<U>) -> Self::Output {
                Thunk::lazy(
                    Box::new(
                        move || self.unwrap().$f(rhs.unwrap())
                    )
                )
            }
        }
    };
    (
        $t1:path => $t2:path = $t3:path {
            $f:ident ( $b1:ident ) = $impl:ident ( $a:ident, $b2:ident )
        }
    ) => {
        impl<T: $t3 + 'static, U: 'static> $t2 for Thunk<T> {
            fn $f(&mut self, rhs: Thunk<U>) {
                let inner = self.inner.take();
                let lhs = Thunk::with_inner(inner);
                let result = lhs.$impl(rhs);
                let result = result.inner.take();
                self.inner.set(result);
            }
        }
    }
}

impl_op! { Neg { neg(a) } }
impl_op! { Not { not(a) } }
impl_op! { Add<U> => Add<Thunk<U>> { add(a, b) } }
impl_op! { Sub<U> => Sub<Thunk<U>> { sub(a, b) } }
impl_op! { Mul<U> => Mul<Thunk<U>> { mul(a, b) } }
impl_op! { Div<U> => Div<Thunk<U>> { div(a, b) } }
impl_op! { Rem<U> => Rem<Thunk<U>> { rem(a, b) } }
impl_op! { BitOr<U> => BitOr<Thunk<U>> { bitor(a, b) } }
impl_op! { BitAnd<U> => BitAnd<Thunk<U>> { bitand(a, b) } }
impl_op! { BitXor<U> => BitXor<Thunk<U>> { bitxor(a, b) } }
impl_op! { Shl<U> => Shl<Thunk<U>> { shl(a, b) } }
impl_op! { Shr<U> => Shr<Thunk<U>> { shr(a, b) } }
impl_op! {
    AddAssign<U> => AddAssign<Thunk<U>> = Add<U, Output=T> {
        add_assign(b) = add(a, b)
    }
}
impl_op! {
    SubAssign<U> => SubAssign<Thunk<U>> = Sub<U, Output=T> {
        sub_assign(b) = sub(a, b)
    }
}
impl_op! {
    MulAssign<U> => MulAssign<Thunk<U>> = Mul<U, Output=T> {
        mul_assign(b) = mul(a, b)
    }
}
impl_op! {
    DivAssign<U> => DivAssign<Thunk<U>> = Div<U, Output=T> {
        div_assign(b) = div(a, b)
    }
}
impl_op! {
    RemAssign<U> => RemAssign<Thunk<U>> = Rem<U, Output=T> {
        rem_assign(b) = rem(a, b)
    }
}
impl_op! {
    BitOrAssign<U> => BitOrAssign<Thunk<U>> = BitOr<U, Output=T> {
        bitor_assign(b) = bitor(a, b)
    }
}
impl_op! {
    BitAndAssign<U> => BitAndAssign<Thunk<U>> = BitAnd<U, Output=T> {
        bitand_assign(b) = bitand(a, b)
    }
}
impl_op! {
    BitXorAssign<U> => BitXorAssign<Thunk<U>> = BitXor<U, Output=T> {
        bitxor_assign(b) = bitxor(a, b)
    }
}
impl_op! {
    ShlAssign<U> => ShlAssign<Thunk<U>> = Shl<U, Output=T> {
        shl_assign(b) = shl(a, b)
    }
}
impl_op! {
    ShrAssign<U> => ShrAssign<Thunk<U>> = Shr<U, Output=T> {
        shr_assign(b) = shr(a, b)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn basic() {
        let mut x = lazy!(41);
        let y = lazy!(1 + 2);
        let z = lazy!(clone(y) { *y + 5 });
        assert!(!x.is_ready());
        assert!(y.is_ready());
        assert!(!z.is_ready());
        assert_eq!(*z, 8);
        assert_eq!(*y, 3);
        *x = 42;
        assert_eq!(*x, 42);
    }

    #[test]
    fn mutable() {
        fn f(x: i64) -> i64 {
            2 * x + 1
        }
        #[derive(Debug, PartialEq)]
        struct Point(i64, i64);
        let x = 25;
        let mut p = lazy!({ Point(x, f(x)) });
        {
            let p_ref: &Point = &p;
            assert_eq!(p_ref, &Point(25, 51));
        }
        {
            let p_mut: &mut Point = &mut p;
            p_mut.0 = 5;
            p_mut.1 = f(p_mut.0);
            assert_eq!(p_mut, &Point(5, 11));
        }
        assert_eq!(*p, Point(5, 11));
    }

    #[test]
    fn arithmetic() {
        let a = lazy!(1_i64);
        let b = lazy!(2_i64);
        let c = a + b + -ready!(42_i64);
        assert!(!c.is_ready());
        assert_eq!(*c, 1 + 2 + -42);
    }

    #[test]
    fn assign() {
        let mut a = lazy!(0_i64);
        a += lazy!(42);
        assert!(!a.is_ready());
        assert_eq!(*a, 42);
    }

    #[test]
    fn debug() {
        let a = lazy!("a");
        let b = lazy!("b");
        *a;
        assert_eq!(
            &*format!("{:?}", a),
            "Thunk { inner: Cell { value: Ready(\"a\") } }"
        );
        assert_eq!(
            &*format!("{:?}", b),
            "Thunk { inner: Cell { value: Lazy(...) } }"
        );
        assert_eq!(&*format!("{:?}", *a), "\"a\"");
        assert_eq!(&*format!("{:?}", *b), "\"b\"");
    }
}
