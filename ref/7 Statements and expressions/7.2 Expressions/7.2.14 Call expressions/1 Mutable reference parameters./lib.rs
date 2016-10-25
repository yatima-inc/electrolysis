fn add(x: &mut i32, y: i32) {
    *x += y
        ; () // TODO: removing this line leaves `ret` uninitialized, which sounds at least like 'undesired behavior' from MIR
}

fn foo() -> i32 {
    let mut x: i32 = 1i32;
    add(&mut x, 2i32);
    x
}
