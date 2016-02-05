#![feature(rustc_attrs)]
#![no_std]

trait Bar {} impl Bar for u32 {}
trait Foo: Bar { type A; fn foo(a: Self::A); }
impl Foo for u32 { type A = u16; fn foo(a: u16) {} }

#[rustc_mir(graphviz="fac.gv")]
fn fac(n: u32) -> u32 {
    let mut res = 1;
    for i in 2..n+1 {
        res *= i;
    }
    res
}
