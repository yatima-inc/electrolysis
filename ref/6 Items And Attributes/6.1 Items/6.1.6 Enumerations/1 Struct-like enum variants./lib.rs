struct Name;

enum Animal {
    Dog (Name, u32),
    Cat { name: Name, weight: u32 },
}

fn main() {
    let mut a: Animal = Animal::Dog(Name, 37);
    a = Animal::Cat { name: Name, weight: 2 };
}
