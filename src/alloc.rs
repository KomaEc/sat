

use crate::{
    clause::{Clause}
};

pub struct Allocator {
    data : Box<[i32]>, // allocator owns all the data

    size : usize, // size of data, size == data.len()
    used : usize, // pointer to first unused data
}


impl Allocator {

    fn new() -> Self {
	let size = 1usize << 30;
	let used = 1usize; // the first piece of data is always not for use
	let data = vec![0; size].into_boxed_slice();
	Allocator {
	    data : data,
	    size : 1 << 30,
	    used : 1,
	}
    }

    fn add_clause(&mut self, clause: &[i32]) {
	// well, normally speaking, clause.len() cannot exceed that range...
	// so it is a safe case here
	self.data[self.used] = clause.len() as i32; self.used += 1;

	// this is because, we do not add unary clause to the database.
	
	assert!(clause.len() >= 2);
    }
}

/// Compact representation of clause references
#[repr(transparent)]
pub struct ClauseRef(usize);

/// Compact representation of references to next watch
/// the clauses that is watched by a literal is organized as a linked list.
/// ????? How do we distinguish between fst watch and snd watch
#[repr(transparent)]
pub struct WatchRef(usize);

#[cfg(test)]
mod tests {
    use super::*;
}


