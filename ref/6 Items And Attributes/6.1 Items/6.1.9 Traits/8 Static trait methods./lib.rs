trait Num {
    fn from_i32(n: i32) -> Self;
}
impl Num for i64 {
    fn from_i32(n: i32) -> i64 { n as i64 }
}
fn main() {
    let x: i64 = Num::from_i32(42);
}
