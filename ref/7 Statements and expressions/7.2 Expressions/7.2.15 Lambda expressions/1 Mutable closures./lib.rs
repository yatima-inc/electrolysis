fn apply<T, R, F: FnOnce(T) -> R>(f: F, x: T) -> R {
    f(x)
}

fn foo(x: i32, mut y: i32) -> i32 {
    apply(|x| {
        y += 1;
        x + y
    }, x)
}
