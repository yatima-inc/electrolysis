/*
// would require generalized mutually inductive types
enum List<T> {
    Single(T),
    Cons(T, Box<List<T>>),
}

impl<T> List<T> {
    fn last_mut(&mut self) -> &mut T {
        let mut xs = self;
        loop {
            let tmp = xs;
            xs = match tmp {
                &mut List::Single(ref mut x) => return x,
                &mut List::Cons(_, ref mut b) => &mut *b,
            };
        }
    }
}*/

fn foo(mut xs: &mut [i32]) {
    loop {
        let tmp = xs;
        xs = &mut tmp[2..];
    }
}
