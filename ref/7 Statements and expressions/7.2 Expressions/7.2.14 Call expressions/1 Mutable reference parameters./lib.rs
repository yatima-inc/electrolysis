fn set(x: &mut i32, y: i32) {
    *x = y
        ; () // FIXME: removing this line leaves `ret` uninitialized, which sounds at least like 'undesired behavior' from MIR
}

fn foo() -> i32 {
    let mut x = 1;
    set(&mut x, 2);
    x
}
