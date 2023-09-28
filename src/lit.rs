use std::convert::From;
use std::fmt;
use std::ops::Neg;

pub type LitIdx = u32;

#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var {
    data: LitIdx,
}

impl Var {
    pub fn from_dimacs(number: i32) -> Var {
        debug_assert!(number > 0);
        Var {
            data: (number - 1) as u32,
        }
    }

    pub fn to_lit(self) -> Lit {
        Lit::from(self.data << 1)
    }

    pub fn to_neg_lit(self) -> Lit {
        Lit::from(self.data << 1 | 1)
    }

    pub fn idx(self) -> usize {
        self.data as usize
    }
}

impl From<Lit> for Var {
    fn from(lit: Lit) -> Var {
        Var {
            data: lit.data >> 1,
        }
    }
}

impl fmt::Debug for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.idx() + 1)
    }
}

impl fmt::Display for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self, f)
    }
}

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
            } else {
                // number < 0
                (-number as u32 - 1) << 1 | 1
            },
        }
    }

    pub fn to_dimacs(self) -> i32 {
        if (self.data & 1) != 0 {
            -((self.data >> 1) as i32 + 1)
        } else {
            (self.data >> 1) as i32 + 1
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
            data: self.data ^ 1,
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

    use proptest::prelude::*;

    proptest! {
    #[test]
    fn test_from_dimacs_compose_to_dimacs_identity(
        num in (-100i32..101)
        .prop_filter("dimacs literal is non-zero", |num| *num != 0)) {
        assert_eq!(num, Lit::from_dimacs(num).to_dimacs());
    }
    }
    proptest! {
    #[test]
    fn test_to_dimacs_compose_from_dimacs_identity(idx in (0..200u32)) {
        let lit = Lit { data: idx };
        assert_eq!(lit, Lit::from_dimacs(lit.to_dimacs()));
    }
    }
    proptest! {
    #[test]
    fn test_neg(
        num in (-100i32..101)
        .prop_filter("dimacs literal is non-zero", |num| *num != 0)) {
        assert_eq!(-num, (-Lit::from_dimacs(num)).to_dimacs());
    }
    }
    proptest! {
    #[test]
    fn test_neg_neg_identity(idx in (0..200u32)) {
        let lit = Lit { data: idx };
        assert_eq!(--lit, lit);
    }
    }
    proptest! {
    #[test]
    fn test_to_lit_to_var_identity(num in (1..200i32)) {
        let lit = Lit::from_dimacs(num);
        assert_eq!(Var::from(lit).to_lit(), lit);
        assert_eq!(Var::from(lit).to_neg_lit(), -lit);
    }
    }
    proptest! {
    #[test]
    fn test_to_var_to_lit_identity(idx in (0..200u32)) {
        let var = Var { data: idx };
        assert_eq!(Var::from(var.to_lit()), var);
        assert_eq!(Var::from(var.to_neg_lit()), var);
    }
    }
}
