
use crate::{
    clause::{Clause}
};

use std::vec::Vec;

// use crate::clause::*;

/// The main solver data structure
pub struct Solver<'a> {
    n_vars : u32, // number of variables of a SAT instance
    n_clauses : u32, // number of clauses
    mem_max : u32, // maximum memory
    mem_used : u32, // used memory
    n_lemmas : u32, // number of learned clauses
    max_lemmas : u32, // maximum number of learned clauses
    antecedant : Vec<Option<&'a Clause>>, // the reason clause for an implication
    decision : Vec<i32>, // decision stack
    database : Box<[i32]>, // database that stores clauses and lemmas
}

/// Data Structures
/// 1. decision stack. A stack holding literals in the current assignment.
///   1.1 two indices [`assigned`], [`processed`] of the decision stack.
/// 2. watched literals. For each literal, we store a 'linked list' of
///    that it watches. A big array `first[lit]` is used to store the
///    head of that list.





/// Main routines
/// - [x] The main solve loop
/// ```rust
/// fn solve() {
///   loop {
///     if not propagate() {
///       analyze();
///     } else if not decide() {
///       return SAT;
///     }
///   }
/// }
/// ```
///
/// - [x] propagate()
/// ```rust
/// fn propagate() -> bool {
///   loop {
///     if processed == assigned {
///       break;
///     }
///     // else processed < assigned
///     let cur_lit = decision[++processed];
///     let conflict_flag = false;
///     let clause;
///     for clause in watch[cur_lit] {
///       if is_unit(clause) {
///         decision[++assigned] = lit_implied_by(clause);
///       } else if conflict(clause) {
///         conflict_flag = true;
///         break;
///       }
///     }
///     // handling conflict
///     if conflict_flag {
///       // clause is now conflict clause
///       TODO
///       return false;
///     }
///     return true;
///   }
/// }
/// ```
impl<'a> Solver<'a> {

    /*
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
     */
    
    fn add_clause(&mut self, clause: &Clause) {
	
    }
}


#[cfg(test)]
mod tests {
    use super::*;

}
