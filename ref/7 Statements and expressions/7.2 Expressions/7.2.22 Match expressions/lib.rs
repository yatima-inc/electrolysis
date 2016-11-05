fn f1(x: i32) -> &'static str {
    match x {
        1 => "one",
        2 => "two",
        3 => "three",
        4 => "four",
        5 => "five",
        _ => "something else",
    }
}

fn f2(x: i32) -> &'static str {
    match x {
        e @ 1 ... 5 => "got a range element",
        _ => "anything",
    }
}

fn f3(x: &i32) {
    let y = match *x { 0 => "zero", _ => "some" };
    let z = match x { &0 => "zero", _ => "some" };
}

fn f4(x: i32) {
    let message = match x {
        0 | 1  => "not many",
        2 ... 9 => "a few",
        _      => "lots"
    };
}

fn f5(x: Option<i32>) -> Option<i32> {
    match x {
        Some(x) if x < 10 => Some(x),
        Some(x) => None,
        None => panic!(),
    }
}
