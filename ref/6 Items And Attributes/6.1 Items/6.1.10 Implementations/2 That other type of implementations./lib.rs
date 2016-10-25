struct Point {x: i32, y: i32}

impl Point {
    fn log(&self) {
        //println!("Point is at ({}, {})", self.x, self.y);
    }
}

fn main() {
    let my_point = Point {x: 10, y:11};
    my_point.log();
}
