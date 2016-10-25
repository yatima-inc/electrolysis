fn foo(mut x: i32, mut y: i32) -> i32 {
    {
        let rs = [&mut x, &mut y];
        *rs[0] += 1;
    }
    x
}
