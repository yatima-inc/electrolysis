fn main() {
    struct Point { x: i64, y: i64 }
    struct TuplePoint(i64, i64);

    Point {x: 10, y: 20}.x;
    TuplePoint(10, 20).0;
}
