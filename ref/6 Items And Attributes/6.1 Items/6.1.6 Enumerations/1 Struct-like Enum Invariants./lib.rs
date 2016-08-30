enum Animal {
    Dog (String, u32),
    Cat { name: String, weight: u32 },
}

fn main() {
    let mut a: Animal = Animal::Dog("Cocoa".to_string(), 37);
    a = Animal::Cat { name: "Spotty".to_string(), weight: 2 };
}
