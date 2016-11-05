fn foo(xs: &mut [i32]) -> &mut i32 {
    &mut xs[0]
}

fn bar(xs: &mut [i32]) {
    *foo(xs) = 2;
}
