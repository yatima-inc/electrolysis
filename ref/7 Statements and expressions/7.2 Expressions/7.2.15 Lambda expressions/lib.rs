fn apply<T, R, F: FnOnce(T) -> R>(f: F, x: T) -> R {
    f(x)
}

fn foo(x: i32, y: i32) -> i32 {
    apply(|x| x + y, x)
}
