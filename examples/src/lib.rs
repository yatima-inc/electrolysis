//#![feature(rustc_attrs)]
//#[rustc_mir(graphviz="example.gv")]

fn fac(n: u32) -> u32 {
    let mut res = 1;
    for i in 2..n+1 {
        res *= i;
    }
    res
}
