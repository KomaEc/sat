

use crate::{
    clause::{Clause},
    lit::Lit,
};

use std::vec::Vec;


pub struct Allocator {
    data : Vec<u32>, // allocator owns all the data
}

impl Default for Allocator {
    fn default() -> Self {
	let size = 1usize << 30;
	Allocator {
	    data : {
		let mut vec = Vec::with_capacity(size);
		vec.push(0);
		vec
	    },
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
	    data : {
		let mut vec = Vec::with_capacity(size);
		vec.push(0);
		vec
	    },
	}
    }


    #[inline]
    pub fn allocate_clause(&mut self, lits: &[Lit]) -> ClauseRef {
	let start_idx = self.data.len();
	
	self.data.push(lits.len() as u32);

	for lit in lits {
	    self.data.push((*lit).into());
	}
	// copy lits to the clause

	ClauseRef(start_idx)
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


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_allocate_clause() {
	let mut allocator = Allocator::new();
	
	let clause_data1 = [3, 3, 1, 2];
	let clause_data2 = [4, 1, 5, 6, 3];
	
	let clause_ref1 = allocator.allocate_clause(&clause_data1[1..].iter().map(|lit| (*lit).into()).collect::<Vec<_>>()[..]);
	let clause_ref2 = allocator.allocate_clause(&clause_data2[1..].iter().map(|lit| (*lit).into()).collect::<Vec<_>>()[..]);

	assert_eq!(allocator.get_clause(clause_ref1).lits(), &clause_data1[1..].iter().map(|lit| (*lit).into()).collect::<Vec<_>>()[..]);
	assert_eq!(allocator.get_clause(clause_ref2).lits(), &clause_data2[1..].iter().map(|lit| (*lit).into()).collect::<Vec<_>>()[..]);
    }
}

