trait Shape {
    fn draw(&self) {}
}
impl Shape for i32 { }

fn main() {
    let mycircle = 0i32;
    let myshape: &Shape = &mycircle;
    myshape.draw();
}
