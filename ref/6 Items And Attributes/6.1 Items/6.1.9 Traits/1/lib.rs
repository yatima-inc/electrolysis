struct Foo;

trait Shape { fn area(&self) -> i64; }
trait Circle : Shape { fn radius(&self) -> i64; }
impl Shape for Foo {
    fn area(&self) -> i64 {
        1
    }
}
impl Circle for Foo {
    fn radius(&self) -> i64 {
        //println!("calling area: {}", self.area());
        -1
    }
}

fn main() {
    let c = Foo;
    c.radius();
}
