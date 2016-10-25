fn foo(mut x: (i32, i32)) -> i32 {
    *&mut x.0
}
