#![feature(rustc_attrs)]
#![no_std]

#[rustc_mir(graphviz="fac.gv")]
fn fac(n: u32) -> u32 {
    let mut res = 1;
    for i in 2..n+1 {
        res *= i;
    }
    res
}
