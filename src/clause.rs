

pub mod alloc;

pub use alloc::{ClauseRef};


/// data in Clause:
/// -----------------------------
/// | length of data | literals |
/// -----------------------------
/// invariant: the first two literals of a clause must be its watched literals
#[repr(transparent)]
pub struct Clause {
    data : [i32], 
}

use std::slice;

impl Clause {
    pub fn len(&self) -> usize {
	self.data[0] as usize
    }

    #[inline]
    pub fn lits(&self) -> &[i32] {
	&self.data[1..]
    }

    #[inline]
    pub fn lits_mut(&mut self) -> &mut [i32] {
	&mut self.data[1..]
    }

    pub fn data(&self) -> &[i32] {
	&self.data[..]
    }

    pub fn data_mut(&mut self) -> &mut [i32] {
	&mut self.data[..]
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clause_layout() {
	let data = [3, 1, -2, -4];
	let data_ref = &data;
	let ptr = data_ref.as_ptr();
	let clause: &Clause =
	    unsafe {
		std::mem::transmute(
		    slice::from_raw_parts(ptr, data_ref.len())
		)
	    };
	assert_eq!(clause.len(), data_ref.len()-1);
	assert_eq!(clause.lits(), &data[1..]);
    }
}
