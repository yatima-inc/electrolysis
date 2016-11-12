fn apply<T, F: FnMut(T) -> T>(mut f: F, x: T) -> T {
    let y = f(x);
    f(y)
}

fn foo(x: i32, mut y: i32) -> i32 {
    apply(move |x| {
        y += 1;
        x + y
    }, x)
}
