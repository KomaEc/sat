pub mod alloc;

use crate::lit::Lit;
pub use alloc::ClauseRef;

/// data in Clause:
/// -----------------------------
/// | length of data | literals |
/// -----------------------------
/// invariant: the first two literals of a clause must be its watched literals
#[repr(transparent)]
pub struct Clause {
    data: [u32],
}

use std::slice;

impl Clause {
    #[inline]
    pub fn lits(&self) -> &[Lit] {
        unsafe {
            let ptr = self.data.as_ptr().add(1) as *const Lit;
            slice::from_raw_parts(ptr, self.data.len() - 1)
        }
        // &self.data[1..]
    }

    #[inline]
    pub fn lits_mut(&mut self) -> &mut [Lit] {
        unsafe {
            let ptr = self.data.as_mut_ptr().add(1) as *mut Lit;
            slice::from_raw_parts_mut(ptr, self.data.len() - 1)
        }
        // &mut self.data[1..]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clause_layout() {
        let data = [3, 1, 2, 4];
        let data_ref = &data;
        let ptr = data_ref.as_ptr();
        let clause: &Clause =
            unsafe { std::mem::transmute(slice::from_raw_parts(ptr, data_ref.len())) };
        // assert_eq!(clause.len(), data_ref.len()-1);
        assert_eq!(
            clause.lits(),
            &data[1..]
                .iter()
                .map(|lit| (*lit).into())
                .collect::<Vec<_>>()[..]
        );
    }
}
