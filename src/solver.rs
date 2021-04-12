

use crate::{
    clause::{Clause},
    clause::alloc::{Allocator, ClauseRef},
    watch::{Watch, WatchList}
};

use std::vec::Vec;
use std::cell::UnsafeCell;

// use crate::clause::*;

/// Calculate the index of a literal into arrays like [`first`]
macro_rules! cal_idx {
    ($lit: expr, $n_vars: expr) => { ($lit + ($n_vars as i32)) as usize }
}

#[repr(u8)]
#[derive(Clone, Copy, PartialEq)]
enum Assignment {
    Decided,
    Implied,
    Unassigned,
}

#[derive(Clone, Copy, PartialEq)]
enum ClauseStatus {
    Unit(i32),
    Conflict,
    Delayed,
    Satisfied,
}

/// The main solver data structure
pub struct Solver {
    n_vars : usize, // number of variables of a SAT instance
    n_clauses : usize, // number of clauses
    n_lemmas : usize, // number of learned clauses
    max_lemmas : usize, // maximum number of learned clauses
    
    reason : Box<[ClauseRef]>, // the reason clause for an implication
    // length = 2 * n_vars + 1
    decision : Vec<i32>, // decision stack, holds literals that is assigned to be false
    // length = n_vars
    assignment : Box<[Assignment]>, // assignment info
    // length = 2 * n_vars + 1
    watches : Box<[WatchList]>, // clauses watched by a literal
    // length = 2 * n_vars + 1

    processed : usize,
    // an index into decision stack. Invariant: processed < decision.len()
    


    buffer : Box<[i32]>, // a buffer to contain conflict clauses
    // length = n_vars
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
///    Invariant: At any time, the two watch literals of a clause
///               must be non-false at levels lower than current level.
///               After [`propagation()`], they must be non-false
///               regardless of levels.
///    Why `two` watches not one? After all, one watch is enough for
///    checking clause status. The answer is one watch may loss
///    arc consistency. Consider the following scenario: a clause is
///    watched by a literal, which is unassigned at this point, and
///    after current decision and implications, all other literals
///    are assigned to be false. Since the watch literal is left
///    untouched in this round, the solver will never check this clause.
///    Therefore, arc consistency is lost.
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


    /// Add [`lit`] as a watch literal to the clause
    fn add_watch(&mut self,
		 clause_ref: ClauseRef,
		 lit: i32) {
	self.watches[cal_idx!(lit, self.n_vars)].add_watch(Watch::new(clause_ref));
    }


    /// Allocate a new clause containing literals in [`lits`], set
    /// up two watched literals scheme
    fn add_clause(&mut self,
		  lits: &[i32]) {
	let clause_ref = self.allocator.allocate_clause(lits);

	assert!(lits.len() >= 2);
	// this is because, we do not add unary clauses to the database.
	// unary clauses, be it learned or original, are encoded as
	// ground level assertions.

	self.add_watch(clause_ref, lits[0]);
	self.add_watch(clause_ref, lits[1]);


    }

    /// Assign [`lit`] to be false, set reason clause if it
    /// is implied
    fn assign(&mut self, lit: i32, reason: Option<ClauseRef>) {
	self.decision.push(lit);
	let lit_idx = cal_idx!(lit, self.n_vars);
	match reason {
	    Some(cref) => {
		self.assignment[lit_idx] = Assignment::Implied;
		self.reason[lit_idx] = cref;
		// FIXME: lit or neg_lit??
	    },
	    None => {
		self.assignment[lit_idx] = Assignment::Decided;
	    }
	}
	
    }


    /// Force the variant of two watch literals scheme.
    /// Precondition: [`watch_lit`] is a watch literal of
    /// clause [`clause_ref`], and it is assigned to be false
    /// in current decision level
    /// return [`Unit(lit)`] if the clause is a unit clause, and
    /// [`lit`] is negation of the only unassigned literal in this clause.
    /// For example, under partial assignment [x1 -> true, x2 -> false]
    /// the status of clause ~x1 \/ x2 \/ ~x3 is Unit(x3), it implies that
    /// x3 should be false
    fn force_clause_status(&mut self,
			   wlit: i32,
			   clause_ref: ClauseRef) -> ClauseStatus {
	let clause = self.allocator.get_clause(clause_ref);
	let ith = (wlit == clause.lits()[1]) as usize;

	// at this point, the another watch is unassigned w.r.t.
	// current decision stack up tp [`wlit`]

	let mut unassigned_idx: Option<usize> = None;

	for (i, lit) in clause.lits().iter().enumerate() {
	    let lit_idx = cal_idx!(*lit, self.n_vars);
	    if let Assignment::Unassigned = self.assignment[lit_idx] {
		// [`lit`] is non-false
		unassigned_idx = Some(i); break;
	    }
	}

	match unassigned_idx {
	    Some(i) => {
		// assert_eq!(wlit, clause.lits()[ith]);
		let lit = clause.lits_mut()[i];
		clause.lits_mut()[ith] = lit;
		clause.lits_mut()[i] = wlit;
		// swap literals
		
		self.add_watch(clause_ref, lit);
		// add new watch

		ClauseStatus::Delayed
	    },
	    None => {
		// the clause is either unit or conflict
		let wlit2 = clause.lits()[1-ith];
		let wlit2_idx = cal_idx!(wlit2, self.n_vars);
		let neg_wlit2_idx = cal_idx!(-wlit2, self.n_vars);

		if let Assignment::Unassigned = self.assignment[neg_wlit2_idx] {
		    if let Assignment::Unassigned = self.assignment[wlit2_idx] {
			// unit clause found, implies [`-wlit2`] is false
			ClauseStatus::Unit(-wlit2)
		    } else {
			// conflict found
			ClauseStatus::Conflict
		    }
		} else {
		    // else wlit2 is satisfied, do nothing
		    ClauseStatus::Satisfied
		}
	    },
	}
	
    }



    /// Boolean unit propagation
    fn propagate(&mut self) -> bool {
	
	'loop_unprocessed: loop {
	    if self.processed == self.decision.len() - 1 { break; }
	    // else processed < decided

	    self.processed += 1; let cur_lit = self.decision[self.processed];
	    // get current unprocessed decision literal that is assigned
	    // to be false
	    let cur_lit_idx = cal_idx!(cur_lit, self.n_vars);

	    let mut watch_list = WatchList::new();
	    std::mem::swap(&mut self.watches[cur_lit_idx], &mut watch_list);
	    // take ownership

	    let mut conflict = false;
	    let mut j = watch_list.len(); let mut i = 0;
	    while i < j {

		let clause_ref = watch_list[i].clause_ref();

		// FIXME: check [`i`], [`j`] invariant!
		match self.force_clause_status(cur_lit, clause_ref) {
		    ClauseStatus::Unit(implied_lit) => {
			self.assign(implied_lit, Some(clause_ref));
			i += 1;
		    },
		    ClauseStatus::Conflict => {
			self.buffer[..]
			    .clone_from_slice(self
					      .allocator
					      .get_clause(clause_ref)
					      .lits());
			// copy conflict clause into buffer
			conflict = true;
			break;
			// conflict found
		    },
		    ClauseStatus::Satisfied => {
			i += 1;
		    },
		    ClauseStatus::Delayed => {
			// in this case, [`cur_lit`] no longer watches
			// [`clause_ref`], delete it
			// replace watch positioned at [`i`] with that of [`j-1`]
			watch_list.swap(i, j-1);
			j -= 1;
		    }
		}
	    }

	    watch_list.truncate(j);
	    std::mem::swap(&mut self.watches[cur_lit_idx], &mut watch_list);
	    // write back updated watch list

	    if conflict { return false; }
	    
	}

	true // propagation done, no conflict found
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
