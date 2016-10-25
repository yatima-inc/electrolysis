fn foo(mut x: i32, y: &i32, z: u32, b: bool) {
    -x;
    *y;
    !b;
    !z;
    &x;
    &mut x;
}
