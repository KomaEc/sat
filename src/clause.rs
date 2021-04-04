
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

    pub fn len(&self) -> usize {
	self.data[0] as usize
    }

    #[inline]
    pub fn next_watch(&self) -> &[i32] {
	&self.data[1..3]
    }

    #[inline]
    pub fn next_watch_mut(&mut self) -> &mut [i32] {
	&mut self.data[1..3]
    }

    #[inline]
    pub fn lits(&self) -> &[i32] {
	&self.data[3..]
    }

    #[inline]
    pub fn lits_mut(&mut self) -> &mut [i32] {
	&mut self.data[3..]
    }

    pub fn data(&mut self) -> &mut [i32] {
	&mut self.data[..]
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clause_layout() {
	let data = [3, 2, 3, 1, -2, -4];
	let data_ref = &data;
	let ptr = data_ref.as_ptr();
	let clause : &Clause =
	// note: cannot transmute data_ref directly, since data has known size
	// and therefore the pointer has size usize (no need for length)
	    unsafe {
		std::mem::transmute(
		    std::slice::from_raw_parts(ptr, data_ref.len())
		)
	    };
	assert_eq!(clause.len(), data.len() - 3);
	assert_eq!(clause.lits(), &data[3..]);
	unsafe {
	    // &Clause has the same layout as &[i32], 16 bytes long
	    assert_eq!(std::mem::size_of::<&Clause>(), 16);
	    let clause_data = std::mem::transmute::<&Clause, [usize; 2]>(clause);
	    assert_eq!(clause_data[1], data.len());
	}
	assert_eq!(clause.data[0], 3);
	assert_eq!(clause.data, [3, 2, 3, 1, -2, -4]);
    }
}
