trait Shape {
    fn draw(&self) {}
}
impl Shape for i32 { }

fn main() {
    let mycircle = 0i32;
    // we don't even have `Box` right now
    // let myshape: Box<Shape> = Box::new(mycircle) as Box<Shape>;
    let myshape: &Shape = &mycircle;
    myshape.draw();
}
