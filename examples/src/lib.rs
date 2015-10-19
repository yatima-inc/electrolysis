fn fac(n: u32) -> u32 {
    let mut res = 1;
    for i in 2..n {
        res *= i;
    }
    res
}
