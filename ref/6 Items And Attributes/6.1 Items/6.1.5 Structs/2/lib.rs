struct Point(i32, i32);

fn main() {
    let p = Point(10, 11);
    let px: i32 = match p { Point(x, _) => x };
}
