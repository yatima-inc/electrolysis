fn foo(b: bool, c: bool) -> i32 {
    let mut x = 0;
    if b { x += 1 }
    if c { x += 1 }
    x
}
