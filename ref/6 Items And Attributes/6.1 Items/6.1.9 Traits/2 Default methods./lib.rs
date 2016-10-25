trait Foo {
    fn bar(&self);
    fn baz(&self) { self.bar() }
}

struct Bar;

impl Foo for Bar {
    fn bar(&self) {}
}
