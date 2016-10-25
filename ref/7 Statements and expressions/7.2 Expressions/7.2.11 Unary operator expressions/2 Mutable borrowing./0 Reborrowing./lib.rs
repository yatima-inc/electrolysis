struct S { x: [i32; 2] }

fn foo(s: &mut S) -> i32 {
    let p = &mut s.x[0];
    *p
}
