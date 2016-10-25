struct S { x: [i32; 2] }

fn foo(mut s: S, i: usize) -> S {
    s.x[i] = 2;
    s
}
