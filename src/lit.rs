

use std::ops::Neg;
use std::convert::From;
use std::fmt;

pub type LitIdx = u32;

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit {
    data: LitIdx,
}

impl Lit {

    pub fn from_dimacs(number: i32) -> Lit {
	Lit {
	    data: if number > 0 {
		(number as u32 - 1) << 1
	    } else { // number < 0
		(-number as u32 - 1) << 1 | 1
	    }
	}
    }

    pub fn to_dimacs(self) -> i32 {
	if (self.data & 1) != 0 {
	    - ((self.data >> 1) as i32)
	} else {
	    (self.data >> 1) as i32
	}
    }

    pub fn idx(self) -> usize {
	self.data as usize
    }
}

impl From<LitIdx> for Lit {
    fn from(idx: LitIdx) -> Self {
	Lit { data: idx }
    }
}

impl Into<LitIdx> for Lit {
    fn into(self) -> LitIdx {
	self.data
    }
}

impl Neg for Lit {
    type Output = Self;

    fn neg(self) -> Self::Output {
	Lit {
	    data: self.data ^ 1
	}
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_dimacs())
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_dimacs() {
	let lit1 = Lit::from_dimacs(3);
	assert_eq!(4, lit1.data);
	let lit2 = Lit::from_dimacs(-4);
	assert_eq!(7, lit2.data);
    }
}
