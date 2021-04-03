
use crate::{
    clause::{Clause},
    alloc::{Allocator, ClauseRef}
};

use std::vec::Vec;

// use crate::clause::*;

#[repr(u8)]
enum Assignment {
    Decided,
    Implied,
    Unassigned,
}

/// The main solver data structure
pub struct Solver {
    n_vars : u32, // number of variables of a SAT instance
    n_clauses : u32, // number of clauses
    n_lemmas : u32, // number of learned clauses
    max_lemmas : u32, // maximum number of learned clauses
    
    antecedant : Box<[ClauseRef]>, // the reason clause for an implication
    // length = 2 * n_vars + 1
    decision : Vec<i32>, // decision stack, holds literals
    // length = n_vars
    assignment : Box<[Assignment]>, // the false stack, should not be vec!
    // length = 2 * n_vars + 1
    first : Box<[ClauseRef]>, // the first clause watched by a literal
    // length = 2 * n_vars + 1
    // initially set to 0
    

    allocator : Allocator,
}

/// Data Structures
/// 1. decision stack. A stack holding literals in the current
///    assignment.
///   1.1 two indices [`assigned`], [`processed`] of the decision
///       stack.
///   1.2 a false stack is maintained to hold status (Decided, etc.)
/// 2. watched literals. For each literal, we store a 'linked list'
///    of that it watches. A big array `first[lit]` is used to store
///    the head of that list.
/// 3. Decision level. There will be no explicit decision levels.
///    The assignment is organized as a stack like structure, with
///    the following form:
///    |     ...     |
///    | ?   Implied |
///    | xk  Implied | @ level (l+1)
///    | ?   Implied |
///    | xi  Decided | @ level (l+1)
///    | ?   Implied |
///    | ?   Implied |
///    | ~xj Decided | @ level l
///    |     ...     |


/// Learnt clauses are implied by the original set of clauses.
/// Starting from one original clause (the conflict clause),
/// a learnt clause is constructed by multip steps of resolusion
/// of this clause with other clauses.

/// Backtrack level: the second highest decision level in the
/// learnt clause.

/// Stop criteria: resolusion stops when current clause contains
/// the negation of the first Unique Implication Point (UIP) as
/// the [only] literal that is at current decision level.
/// This criteria provides the [lowest] decision level. The reason
/// is pretty simple: resolusion only eliminates literals at
/// current assignment, so further resolusion will not affects
/// other literals other than the first UIP, and will only
/// introduce other literals with possibly higher decision level.


/// It might be a bit hard to depict why CDCL can find UNSAT.
/// Here is my thought, imagine that after a long and winding
/// search, there are a lot of ground level implications that is
/// produced by backtracking.


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
///     let clause;
///
///     for clause in watch[cur_lit] {
///       if is_unit(clause) {
///         let implied_lit = lit_implied_by(clause)
///         decision[++assigned] = implied_lit;
///         antecedant[lit] = clause;
///       } else if conflict(clause) {
///         store current clause in buffer;
///         return false;
///       }
///     }
///
///   } // end of outer loop
///   return true;
/// }
/// ```
///
/// - [x] analyze()
/// // current conflict clause is already stored in the buffer
/// fn analyze() {
///   
/// }
impl Solver {


    /// Allocate a new clause containing literals in [`lits`], set
    /// up two watched literals scheme
    fn add_clause(&mut self, lits: &[i32]) {
	let clause_ref = self.allocator.allocate_clause(lits);
	let clause = self.allocator.get_clause(clause_ref);

	// set up 2 watched literals schemes
	let fstw_idx = (clause.lits()[0] + self.n_vars as i32) as usize;
	let sndw_idx = (clause.lits()[1] + self.n_vars as i32) as usize;
	// compute indices into the first array
	
	let next_watches = clause.next_watch();
	next_watches[0] = self.first[fstw_idx].0 as i32;
	next_watches[1] = self.first[sndw_idx].0 as i32;

	self.first[fstw_idx] = clause_ref;
	self.first[sndw_idx] = clause_ref;
    }

    fn propagate(&mut self) -> bool {

	unimplemented!("not yet implemented");
	false
    }

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
}


#[cfg(test)]
mod tests {
    use super::*;

}
