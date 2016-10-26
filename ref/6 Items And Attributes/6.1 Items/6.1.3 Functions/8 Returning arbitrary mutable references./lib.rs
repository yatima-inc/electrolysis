fn foo<'a>(x: &'a mut i32, y: &'a mut i32) -> &'a mut i32 {
    if *x > 0 { x } else { y }
}
