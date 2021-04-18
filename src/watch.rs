
use crate::{
    clause::alloc::{ClauseRef}
};

use std::vec::Vec;
use std::iter::{IntoIterator};
use std::ops::{Index, IndexMut};

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Watch(ClauseRef);

#[repr(transparent)]
#[derive(Clone, PartialEq, Debug)]
pub struct WatchList(Vec<Watch>);


impl Watch {
    #[inline]
    pub fn new(cref: ClauseRef) -> Self {
	Watch(cref)
    }

    #[inline]
    pub fn clause_ref(self) -> ClauseRef {
	self.0
    }
}


impl WatchList {
    #[inline]
    pub fn add_watch(&mut self, w: Watch) {
	self.0.push(w);
    }

    #[inline]
    pub fn remove_watch(&mut self, idx: usize) {
	self.0.swap_remove(idx);
    }


    /// there will be no allocation
    pub fn new() -> Self {
	WatchList(Vec::new())
    }

    #[inline]
    pub fn len(&self) -> usize {
	self.0.len()
    }

    #[inline]
    pub fn swap(&mut self, i: usize, j: usize) {
	self.0.swap(i, j);
    }

    #[inline]
    pub fn truncate(&mut self, s: usize) {
	self.0.truncate(s);
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
	self.0.is_empty()
    }

}

impl Index<usize> for WatchList {
    type Output = Watch;

    fn index(&self, i: usize) -> &Self::Output {
	&self.0[i]
    }
}

impl IndexMut<usize> for WatchList {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
	&mut self.0[i]
    }
}

impl IntoIterator for WatchList {
    type Item = Watch;
    type IntoIter
	= std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
	self.0.into_iter()
    }
    
}

impl<'a> IntoIterator for &'a WatchList {
    type Item = &'a Watch;
    type IntoIter = std::slice::Iter<'a, Watch>;

    fn into_iter(self) -> Self::IntoIter {
	self.0.iter()
    }

}


#[cfg(test)]
mod tests {

    use super::*;

    fn create_watch(i: usize) -> Watch {
	unsafe { std::mem::transmute(i) }
    }

    #[test]
    fn test_watch_eq() {
	assert_eq!(WatchList(vec![create_watch(1), create_watch(2), create_watch(3)]), WatchList(vec![create_watch(1), create_watch(2), create_watch(3)]));
	assert_ne!(WatchList(vec![create_watch(1), create_watch(2), create_watch(3)]), WatchList(vec![create_watch(3), create_watch(2), create_watch(1)]))
    }
    
}
