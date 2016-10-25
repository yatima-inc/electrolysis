fn foo() -> i32 {
    ([1, 2, 3, 4])[0]
}

fn bar() -> &'static str {
    let n = 10;
    let y = (["a", "b"])[n]; // panics
    y
}
