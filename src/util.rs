use std::iter;

use itertools::Itertools;

pub trait Join {
    fn join(self, sep: &str) -> String;
}

impl<S, T> Join for (S, T) where S: ToString, T: IntoIterator, T::Item: ToString {
    fn join(self, sep: &str) -> String {
        iter::once(self.0.to_string()).chain(self.1.into_iter().map(|x| x.to_string())).join(sep)
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

// type inference in closures goes bonkers with arbitrary E
type E = String;

pub trait TryIterator<T> {
    fn try(self) -> Result<::std::vec::IntoIter<T>, E>;
}

impl<It, T> TryIterator<T> for It where It: Iterator<Item=Result<T, E>> {
    fn try(self) -> Result<::std::vec::IntoIter<T>, E> {
        Ok(self.collect::<Result<Vec<_>, _>>()?.into_iter())
    }
}

pub trait IteratorExt : Iterator {
    fn try_flat_map<U, F>(self, f: F) -> Result<::std::vec::IntoIter<U::Item>, E>
        where Self: Sized, U: IntoIterator, F: FnMut(Self::Item) -> Result<U, E>;
    fn try_filter_map<B, F>(self, f: F) -> Result<::std::vec::IntoIter<B>, E>
        where Self: Sized, F: FnMut(Self::Item) -> Result<Option<B>, E>;
}

impl<T> IteratorExt for T where T: Iterator {
    fn try_flat_map<U, F>(self, f: F) -> Result<::std::vec::IntoIter<U::Item>, E>
        where Self: Sized, U: IntoIterator, F: FnMut(Self::Item) -> Result<U, E> {
        Ok(self.map(f).try()?.flat_map(|x| x).collect_vec().into_iter())
    }
    fn try_filter_map<B, F>(self, f: F) -> Result<::std::vec::IntoIter<B>, E>
        where Self: Sized, F: FnMut(Self::Item) -> Result<Option<B>, E> {
        Ok(self.map(f).try()?.filter_map(|x| x).collect_vec().into_iter())
    }
}

/*pub trait ResultJoin<E> {
    fn res_join(self, sep: &str) -> Result<String, E>;
}

impl<T, E> ResultJoin<E> for T where T: IntoIterator<Item=Result<String, E>> {
    fn res_join(self, sep: &str) -> Result<String, E> {
        Ok(try_iter!(self.1.into_iter()).map(|x| x.to_string())).join(sep)
    }
}

impl<S, T, E> ResultJoin<E> for (S, T) where S: ToString, T: IntoIterator<Item=Result<String, E>> {
    fn res_join(self, sep: &str) -> Result<String, E> {
        Ok(iter::once(self.0.to_string()).chain(try_iter!(self.1.into_iter()).map(|x| x.to_string())).join(sep))
    }
}
*/
