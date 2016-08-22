use std::iter;

use itertools::Itertools;

pub trait Join {
    fn join(self, sep: &str) -> String;
}

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

// hackhackhack
pub trait PostJoin {
    fn join(self, sep: &str) -> String;
}

impl<S, T> PostJoin for (T, S) where S: ToString, T: IntoIterator<Item=String> {
    fn join(self, sep: &str) -> String {
        self.0.into_iter().chain(iter::once(self.1.to_string())).join(sep)
    }
}
