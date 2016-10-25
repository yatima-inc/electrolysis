trait Shape { fn area(&self) -> i64; }
trait Circle : Shape { type Foo; fn radius(&self) -> i64; }

fn radius_times_area<T: Circle>(c: T) -> i64 {
    // `c` is both a Circle and a Shape
    c.radius() * c.area()
}
