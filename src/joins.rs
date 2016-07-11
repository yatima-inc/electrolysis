use std::iter;

use itertools::Itertools;

pub trait Join {
    fn join(self, sep: &str) -> String;
}

/*impl<'a, It> Join for (&'a str, It) where It : Iterator<Item=&'a str> {
    fn join(self, sep: &str) -> String {
        iter::once(self.0).chain(self.1).join(sep)
    }
}*/

impl<S, T> Join for (S, T) where S: ToString, T: IntoIterator<Item=String> {
    fn join(self, sep: &str) -> String {
        iter::once(self.0.to_string()).chain(self.1).join(sep)
    }
}

impl<'a> Join for &'a Vec<String> {
    fn join(self, sep: &str) -> String {
        self.iter().join(sep)
    }
}
