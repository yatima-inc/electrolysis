fn foo(mut x: i32) {
    while x != 0 {
        if x == 1 { continue };
        if x == 2 { break; };
        if x == 3 { return; }
        x -= 1;
    }
}
