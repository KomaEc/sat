
use crate::{
    clause::alloc::{ClauseRef}
};

use std::vec::Vec;
use std::iter::{Iterator, IntoIterator};
use std::ops::{Index, IndexMut};

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq)]
pub struct Watch(ClauseRef);

#[repr(transparent)]
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

    pub fn len(&self) -> usize {
	self.0.len()
    }

    pub fn swap(&mut self, i: usize, j: usize) {
	self.0.swap(i, j);
    }

    pub fn truncate(&mut self, s: usize) {
	self.0.truncate(s);
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

