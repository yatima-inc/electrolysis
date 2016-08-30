fn foo<T>(x: &[T]) where T: Default {}

fn main() { foo(&[1, 2]); }
