fn foo(mut x: i32, y: &i32, b: bool) {
    -x;
    !x;
    *y;
    !b;
    &x;
    &mut x;
}
