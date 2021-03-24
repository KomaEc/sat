
/*
use crate::{
    clause::{Clause}
};
 */

// use crate::clause::*;

/// The main solver data structure
pub struct Solver {
    n_vars : i32, // number of variables of a SAT instance
    n_clauses : i32, // number of clauses
    mem_max : i32, // maximum memory
    mem_used : i32, // used memory
    n_lemmas : i32, // number of learned clauses
    max_lemmas : i32, // maximum number of learned clauses
    database : Box<[i32]>, // database that stores clauses and lemmas
}


impl Solver {

    /// create a new solver instance, initilize everything
    fn new(n_vars: i32, n_clauses: i32) -> Self {
	Solver {
	    n_vars : n_vars,
	    n_clauses : n_clauses,
	    mem_max : 1i32 << 30,
	    mem_used : 0,
	    n_lemmas : 0,
	    max_lemmas : 2000,
	    database : {
		let vec = vec![0; (1i32 << 30) as usize];
		vec.into_boxed_slice()
	    },
	}
    }
}


#[cfg(test)]
mod tests {
    use super::*;

}
