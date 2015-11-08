#![feature(rustc_attrs)]
#![feature(step_trait, zero_one)]

use std::mem;
use std::iter::*;
use std::num::*;
use std::ops::Add;

/*fn fac(n: u32) -> u32 {
    let mut res = 1;
    for i in 2..n+1 {
        res *= i;
    }
    res
}*/

pub struct Range<Idx> {
    pub start: Idx,
    pub end: Idx,
}

impl<A: Step + One> Iterator for Range<A> where
    for<'a> &'a A: Add<&'a A, Output = A>
{
    type Item = A;

    #[rustc_mir(graphviz="example.gv")]
    fn next(&mut self) -> Option<A> {
        if self.start < self.end {
            let mut n = &self.start + &A::one();
            mem::swap(&mut n, &mut self.start);
            Some(n)
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match Step::steps_between(&self.start, &self.end, &A::one()) {
            Some(hint) => (hint, Some(hint)),
            None => (0, None)
        }
    }
}
