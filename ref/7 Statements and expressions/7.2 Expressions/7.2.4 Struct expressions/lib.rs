fn main() {
    struct Point { x: i64, y: i64 }
    struct NothingInMe { }
    struct TuplePoint(i64, i64);
    mod game { pub struct User<'a> { pub name: &'a str, pub age: u32, pub score: usize } }
    struct Cookie; fn some_fn<T>(t: T) {}

    Point {x: 10, y: 20};
    NothingInMe {};
    TuplePoint(10, 20);
    let u = game::User {name: "Joe", age: 35, score: 100_000};
    some_fn::<Cookie>(Cookie);
}
