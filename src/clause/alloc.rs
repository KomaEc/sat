

use crate::{
    clause::{Clause}
};
use std::iter::Iterator;

pub struct Allocator {
    data : Box<[i32]>, // allocator owns all the data

    size : usize, // size of data, size == data.len()
    used : usize, // pointer to first unused data
}

impl Default for Allocator {
    fn default() -> Self {
	let size = 1usize << 30;
	Allocator {
	    data : vec![0; size].into_boxed_slice(),
	    size : size,
	    used : 1,
	}
    }
}


impl Allocator {

    pub fn new() -> Self {
	Allocator::default()
    }

    pub fn small() -> Self {
	let size = 1usize << 10;
	Allocator {
	    data : vec![0; size].into_boxed_slice(),
	    size : size,
	    used : 1,
	}
    }

    /*
    #[inline]
    pub fn allocate_watch_node(&mut self) -> WatchNodeRef {
	let used = self.used;
	self.used += 2;
	WatchNodeRef(used)
    }
     */

    #[inline]
    pub fn allocate_clause(&mut self, lits: &[i32]) -> ClauseRef {
	let used = self.used;
	self.data[self.used] = lits.len() as i32;
	// well, normally speaking, lits.len() cannot exceed range of i32...
	// so it is a safe case here

	self.used += 1;

	for lit in lits.iter() {
	    self.data[self.used] = *lit;
	    self.used += 1;
	    
	}
	// copy lits to the clause

	ClauseRef(used)
    }

    #[inline]
    pub fn get_clause(&self, cref: ClauseRef) -> &Clause {
	unsafe {
	    std::mem::transmute({
		let ptr = self.data.as_ptr().add(cref.0);
		let len = *ptr as usize;
		std::slice::from_raw_parts(ptr, len + 1)
	    })
	}
    }

    #[inline]
    pub fn get_clause_mut(&mut self, cref: ClauseRef) -> &mut Clause {
	unsafe {
	    std::mem::transmute({
		let ptr = self.data.as_mut_ptr().add(cref.0);
		let len = *ptr as usize;
		std::slice::from_raw_parts_mut(ptr, len + 1)
	    })
	}
    }
}

/// Compact representation of clause references
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ClauseRef(usize);

impl ClauseRef {

    pub fn null() -> Self {
	ClauseRef(0)
    }
    
    pub fn is_null(&self) -> bool {
	self.0 == 0
    }
}

/*
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq)]
pub struct WatchNodeRef(usize);

impl WatchNodeRef {
    pub fn is_null(&self) -> bool {
	self.0 == 0
    }
}
 */

/*
impl Iterator for WatchNodeRef {
    type Item = ClauseRef;

    fn next(&mut self) -> Option<Self::Item> {
	if self.is_null() {
	    None
	} else {
	    None
	}
    }
}
 */


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_allocate_clause() {
	let mut allocator = Allocator::new();
	
	let clause_data1 = [3, -3, -1, -2];
	let clause_data2 = [4, -1, -5, 6, 3];
	// -1 is watching both clause1 and clause2
	
	let clause_ref1 = allocator.allocate_clause(&clause_data1[1..]);
	let clause_ref2 = allocator.allocate_clause(&clause_data2[1..]);

	assert_eq!(*allocator.get_clause(clause_ref1).data(), clause_data1);
	assert_eq!(*allocator.get_clause(clause_ref2).data(), clause_data2);
    }
}

