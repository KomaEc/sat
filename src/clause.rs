
/// data in Clause:
/// -------------------------------------------------------------------------
/// | length of data | next watch of fst wl | next watch of snd wl | clause |
/// -------------------------------------------------------------------------
/// invariant: the first two literals of a clause must be its watched literals
///
///
#[repr(transparent)]
pub struct Clause {
    data : [i32], 
}

use std::slice;

impl Clause {
    
    fn len(&self) -> usize {
	self.data[0] as usize
    }

    fn lits(&self) -> &[i32] {
	unsafe {
	    slice::from_raw_parts(self.data.as_ptr().add(3), self.len())
	}
    }

    fn lits_mut(&mut self) -> &mut [i32] {
	unsafe {
	    slice::from_raw_parts_mut(self.data.as_mut_ptr().add(3), self.len())
	}
    }
}


#[cfg(test)]
mod tests {
    use super::*;
}
