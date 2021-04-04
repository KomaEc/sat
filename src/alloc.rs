

use crate::{
    clause::{Clause}
};

pub struct Allocator {
    data : Box<[i32]>, // allocator owns all the data

    size : usize, // size of data, size == data.len()
    used : usize, // pointer to first unused data
}


impl Allocator {

    pub fn new() -> Self {
	let size = 1usize << 30;
	Allocator {
	    data : vec![0; size].into_boxed_slice(),
	    size : size,
	    used : 1,
	}
    }

    #[inline]
    pub fn is_null(cref: ClauseRef) -> bool {
	cref.0 == 0
    }

    #[inline]
    pub fn allocate_clause(&mut self, lits: &[i32]) -> ClauseRef {
	let used = self.used;
	self.data[self.used] = lits.len() as i32;
	// well, normally speaking, lits.len() cannot exceed range of i32...
	// so it is a safe case here

	self.used += 3;
	// skip watch literals fields
	
	assert!(lits.len() >= 2);
	// this is because, we do not add unary clauses to the database.
	// unary clauses, be it learned or original, are encoded as
	// ground level assertions.

	for lit in lits.iter() {
	    self.data[self.used] = *lit;
	    self.used += 1;
	    
	}
	// copy lits to the clause

	ClauseRef(used)
    }

    #[inline]
    pub fn get_clause(&mut self, cref: ClauseRef) -> &mut Clause {
	unsafe {
	    std::mem::transmute({
		let ptr = self.data.as_mut_ptr().add(cref.0);
		let len = *ptr as usize;
		std::slice::from_raw_parts_mut(ptr, len + 3)
	    })
	}
    }
}

/// Compact representation of clause references
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq)]
pub struct ClauseRef(pub usize);

impl ClauseRef {
    pub fn new(offset: i32) -> Self {
	ClauseRef(offset as usize)
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_allocate_clause() {
	let mut allocator = Allocator::new();
	
	let clause_data1 = [3, 0, 0, -3, -1, -2]; // uninitialized clause data
	let clause_data2 = [4, 0, 0, 1, -4, 6, 3];
	
	let clause_ref1 = allocator.allocate_clause(&clause_data1[3..]);
	let clause_ref2 = allocator.allocate_clause(&clause_data2[3..]);

	assert_eq!(*allocator.get_clause(clause_ref1).data(), clause_data1);
	assert_eq!(*allocator.get_clause(clause_ref2).data(), clause_data2);
    }
}


