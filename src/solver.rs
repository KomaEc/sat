

use crate::{
    clause::{Clause},
    clause::alloc::{Allocator, ClauseRef},
    watch::{Watch, WatchList}
};
use std::vec::Vec;
use std::ops::Add;


/// Calculate the index of a literal into arrays like [`assignment`]
macro_rules! cal_idx {
    ($lit: expr, $n_vars: expr) => { ($lit + ($n_vars as i32)) as usize }
}

/*
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct Level(u16);

impl Level {
    fn ground_level() -> Self {
	Level(0)
    }

    fn incr(&mut self) {
	self.0 += 1;
    }
}
 */


// #[repr(u8)]
#[derive(Clone, Copy, PartialEq, Debug)]
enum Assignment {
    Decided,
    Implied(ClauseRef),
    Unassigned,
}

/// [`Delayed`] clause can be either unit or unresolved or satisfed
#[derive(Clone, Copy, PartialEq, Debug)]
enum ClauseStatus {
    Unit(i32),
    Conflict,
    Delayed, /// lazy clause status. If we can be lazy, we can be lazier :)
    Satisfied,
}

/// The main solver data structure
pub struct Solver {
    n_vars : usize, /// number of variables of a SAT instance
    n_clauses : usize, /// number of clauses
    n_lemmas : usize, /// number of learned clauses
    max_lemmas : usize, /// maximum number of learned clauses
    
    // reason : Box<[ClauseRef]>, // the reason clause for an implication
    // length = 2 * n_vars + 1

    
    false_stack : Vec<i32>, /// false_stack stack, holds literals that is assigned to be false
    /// length = n_vars
    assignment : Box<[Assignment]>, /// assignment info
    /// length = 2 * n_vars + 1
    watches : Box<[WatchList]>, /// clauses watched by a literal
    /// length = 2 * n_vars + 1
    marked : Box<[bool]>,
    /// length = 2 * n_vars + 1

    processed : usize,
    /// an index into false_stack stack. Invariant: processed <= false_stack.len()
    /// it points to the first unprocessed false_stack

    // level: Level,
    // decision level
    


    buffer : Box<[i32]>, // a buffer to contain conflict clauses
    /// the first [`i32`] is used to store the length of the data
    /// length of total buffer = n_vars + 1
    allocator : Allocator,
}


/// Data Structures
/// 1. false_stack stack. A stack holding literals in the current assignment.
///   1.1 two indices [`assigned`], [`processed`] of the false_stack stack.
///   1.2 a false stack is maintained to hold status (Decided, etc.)
/// 2. watched literals. For each literal, we store a 'linked list' of that it watches. A big array `first[lit]` is used to store
///    the head of that list.
///    Invariant: At any time, the two watch literals of a clause  must be non-false at levels lower than current level.
///               After [`propagation()`], they must be non-false regardless of levels.
///    Why `two` watches not one? After all, one watch is enough for checking clause status. The answer is one watch may loss
///    arc consistency. Consider the following scenario: a clause is watched by a literal, which is unassigned at this point, and
///    after current false_stack and implications, all other literals are assigned to be false. Since the watch literal is left
///    untouched in this round, the solver will never check this clause. Therefore, arc consistency is lost.
/// 3. False_Stack level. There will be no explicit false_stack levels. The assignment is organized as a stack like structure, with
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
///    Gound level assertions are represented as implied literals with reason clauses set to be [`null`]
/// 4. 


/// Learnt clauses are implied by the original set of clauses. Starting from one original clause (the conflict clause),
/// a learnt clause is constructed by multip steps of resolusion of this clause with other clauses.

/// Backtrack level: the second highest false_stack level in the learnt clause.

/// Stop criteria: resolusion stops when current clause contains the negation of the first Unique Implication Point (UIP) as
/// the [only] literal that is at current false_stack level. This criteria provides the [lowest] false_stack level. The reason
/// is pretty simple: resolusion only eliminates literals at current assignment, so further resolusion will not affects
/// other literals other than the first UIP, and will only introduce other literals with possibly higher false_stack level.


/// It might be a bit hard to understand why CDCL can find UNSAT. Here is my thought, imagine that after a long and winding
/// search, there are a lot of ground level implications that is produced by backtracking.


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
///     let cur_lit = false_stack[++processed];
///     let clause;
///
///     for clause in watch[cur_lit] {
///       if is_unit(clause) {
///         let implied_lit = lit_implied_by(clause)
///         false_stack[++assigned] = implied_lit;
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
/// - [ ] analyze()
/// // current conflict clause is already stored in the buffer
/// fn analyze() {
///   while !stop_criterion_met {
///     let lit = last assigned literal in current conflict;
///     let reason_cls = reason[lit];
///     conflict_cls = resolve(lit, conflict_cls, reason_cls);
///   }
///   
/// }
impl Solver {
	
    fn from_sat_instance(n_vars: usize,
			 n_clauses: usize,
			 clauses: Vec<Vec<i32>>,
			 small: bool) -> Self {
	let mut solver =
	    Solver {
		n_vars : n_vars,
		n_clauses : n_clauses,
		n_lemmas : 0,
		max_lemmas : 2000,
		// reason : vec![ClauseRef::null(); 2*n_vars+1].into_boxed_slice(),
		false_stack : Vec::with_capacity(n_vars),
		assignment : vec![Assignment::Unassigned; 2*n_vars+1].into_boxed_slice(),
		watches : vec![WatchList::new(); 2*n_vars+1].into_boxed_slice(),
		marked : vec![false; 2*n_vars+1].into_boxed_slice(),
		processed : 0,
		// level : Level::ground_level(),
		buffer : vec![0i32; n_vars+1].into_boxed_slice(),
		allocator : if small {
		    Allocator::small()
		} else {
		    Allocator::new()
		},
	    };

	for lits in clauses {
	    solver.add_clause(&lits);
	}

	solver
    }

    /// Add [`lit`] as a watch literal to the clause
    fn add_watch(&mut self,
		 clause_ref: ClauseRef,
		 lit: i32) {
	self.watches[cal_idx!(lit, self.n_vars)]
	    .add_watch(Watch::new(clause_ref));
    }


    /// Allocate a new clause containing literals in [`lits`], set up two watched literals scheme
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

    /// Assign [`lit`] to be [`false`], set reason clause
    fn assign(&mut self, lit: i32, reason: Option<ClauseRef>) {
	self.false_stack.push(lit);
	let lit_idx = cal_idx!(lit, self.n_vars);
	match reason {
	    Some(cref) => {

		// FIXME: remove
		// println!("literal {} is implied", lit);

		
		self.assignment[lit_idx] = Assignment::Implied(cref);
		// self.reason[lit_idx] = cref;
		// FIXME: lit or neg_lit??
	    },
	    None => {
		self.assignment[lit_idx] = Assignment::Decided;
	    }
	}
	
    }

    fn unassign(&mut self, lit: i32) {
	unimplemented!("unassign");
    }

    /// naive false_stack
    fn naive_decide(&mut self) -> bool {
	
	for var in 1..(self.n_vars as i32 + 1) {
	    if self.assignment[cal_idx!(var, self.n_vars)] == Assignment::Unassigned
		&& self.assignment[cal_idx!(-var, self.n_vars)] == Assignment::Unassigned {
		    self.assign(var, None);
		    
		    // self.level.incr();
		    // increment decision level
		return true;
	    }
	}

	return false;
    }


    /// Force the variant of two watch literals scheme.
    /// Precondition: [`watch_lit`] is a watch literal of clause [`clause_ref`], and it is assigned to be false.
    /// Return [`Unit(lit)`] if the clause is a unit clause, and [`lit`] is negation of the only unassigned literal in this clause.
    /// For example, under partial assignment [x1 -> true, x2 -> false] the status of clause ~x1 \/ x2 \/ ~x3 is Unit(x3), it implies
    /// that x3 should be false
    /// Note that it will never touch [`self.watches[wlit]`]
    fn force_clause_status(&mut self,
			   wlit: i32,
			   clause_ref: ClauseRef) -> ClauseStatus {

	// FIXME: remove
	if self.assignment[cal_idx!(wlit, self.n_vars)] == Assignment::Unassigned {
	    panic!("should not call force_clause_status with unassigned literal");
	}
	
	let clause = self.allocator.get_clause_mut(clause_ref);
	let (first_two, rest) = clause.lits_mut().split_at_mut(2);

	// ensure another watch is placed before [`wlit`]
	if wlit != first_two[1] {
	    first_two[0] = first_two[1];
	}

	// now, first_two[1] is meaningless

	// at this point, the another watch is unassigned w.r.t.
	// current false_stack stack up tp [`wlit`]

	let mut unassigned_idx: Option<usize> = None;

	for (i, lit) in rest.iter().enumerate() {
	    let lit_idx = cal_idx!(*lit, self.n_vars);
	    if let Assignment::Unassigned = self.assignment[lit_idx] {
		// [`lit`] is non-false
		unassigned_idx = Some(i); break;
	    }
	}

	match unassigned_idx {
	    Some(i) => {
		let lit = rest[i];
		first_two[1] = lit;
		rest[i] = wlit;
		// swap literals
		
		self.add_watch(clause_ref, lit);
		// add new watch

		ClauseStatus::Delayed
	    },
	    None => {

		first_two[1] = wlit;
		// place watch here
		
		// the clause is either unit or conflict
		let wlit2 = first_two[0];
		let wlit2_idx = cal_idx!(wlit2, self.n_vars);
		let neg_wlit2_idx = cal_idx!(-wlit2, self.n_vars);

		if let Assignment::Unassigned = self.assignment[neg_wlit2_idx] {
		    if let Assignment::Unassigned = self.assignment[wlit2_idx] {
			// unit clause found, implying [`-wlit2`] to be false
			ClauseStatus::Unit(-wlit2)
		    } else {
			// conflict found
			ClauseStatus::Conflict
		    }
		} else {
		    // else wlit2 is satisfied
		    ClauseStatus::Satisfied
		}
	    },
	}
	
    }



    /// Boolean unit propagation
    fn propagate(&mut self) -> bool {
	
	'loop_unprocessed: loop {
	    if self.processed == self.false_stack.len() { break; }
	    // else processed <= decided

	    let cur_lit = self.false_stack[self.processed]; self.processed += 1; 
	    // get current unprocessed false_stack literal that is assigned
	    // to be false
	    let cur_lit_idx = cal_idx!(cur_lit, self.n_vars);

	    let mut watch_list = WatchList::new();
	    std::mem::swap(&mut self.watches[cur_lit_idx], &mut watch_list);
	    // take ownership

	    let mut conflict = false;
	    let mut j = watch_list.len(); let mut i = 0;
	    while i < j {

		let clause_ref = watch_list[i].clause_ref();

		// FIXME: remove
		// println!("visiting literal {} and clause {:?}", cur_lit, clause_ref);

		match self.force_clause_status(cur_lit, clause_ref) {
		    ClauseStatus::Unit(implied_lit) => {
			self.assign(implied_lit, Some(clause_ref));
			i += 1;
		    },
		    ClauseStatus::Conflict => {
			let lits = self.allocator
			    .get_clause(clause_ref)
			    .lits();
			self.buffer[0] = lits.len() as i32;
			self.buffer[1..lits.len()+1]
			    .clone_from_slice(lits);
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

	    // FIXME: remove
	    // assert!(self.watches[cur_lit_idx].is_empty());

	    watch_list.truncate(j);
	    std::mem::swap(&mut self.watches[cur_lit_idx], &mut watch_list);
	    // write back updated watch list

	    if conflict { return false; }
	    
	}

	true // propagation done, no conflict found
    }


    fn analyze_conflict(&mut self) -> bool {

	/*
	if self.level == Level::ground_level() {
	    return false;
	}
	// root level conflict found, UNSAT
	 */

	unsafe { std::ptr::write_bytes(self.marked.as_mut_ptr(), 0, self.n_vars); }
	// memset [`mark`] array to all false

	let mut len = self.buffer[0] as usize;
	// let mut conflict_clause = &mut self.buffer[1..];

	for lit in &self.buffer[1..len+1] {
	    self.marked[cal_idx!(lit, self.n_vars)] = true;
	}
	// now all two or more literals at current level are marked

	// FIXME: remove
	assert_eq!(self.processed, self.false_stack.len());
	
	self.processed -= 1;
	// set [`processed`] to point to the last assigned element

	while let Assignment::Implied(cref)
	    = self.assignment[cal_idx!(self.false_stack[self.processed],
				       self.n_vars)] {

		// FIXME: remove
		assert_ne!(self.assignment[cal_idx!(self.false_stack[self.processed], self.n_vars)], Assignment::Unassigned);
	
		if cref.is_null() {
		    // ground level conflict
		    return false;
		}

		let reason = self.allocator.get_clause(cref);
		for lit in reason.lits() {
		    let lit_idx = cal_idx!(lit, self.n_vars);
		    if !self.marked[lit_idx] {
			self.marked[lit_idx] = true;
		    }
		}
		// mark literals in reason clause

		let check: usize = self.processed - 1;
		let no_further_marked = false;
		

		
		self.processed -= 1;
	}
	// loop over all implied literal
	// Post invariant: [`processed`] points to the UIP
	

	
	unimplemented!("analyze");

    }


    pub fn solve(&mut self) -> bool {

	loop {
	    if !self.propagate() {
		if !self.analyze_conflict() { return false; }
	    } else if !self.naive_decide() {
		return true;
	    }
	}
    }

}


#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;
    use proptest::collection::{hash_set, vec};



    impl Solver {
	fn print_all_clauses(&self) {
	    let mut occurs = std::collections::HashMap::new();
	    for lit in -(self.n_vars as i32)..(self.n_vars as i32 + 1) {
		if lit == 0 { continue; }
		for watch in &self.watches[cal_idx!(lit, self.n_vars)] {
		    if !occurs.contains_key(watch) {
			let clause = self.allocator.get_clause(watch.clause_ref()).lits().to_vec();
			occurs.insert(watch, clause);
			// let clause = self.allocator.get_clause(watch.clause_ref());
			// println!("{:?}: {:?}", watch.clause_ref(), clause.lits());
		    }
		}
	    }

	    let mut res = occurs
		.iter()
		.collect::<Vec<(_, _)>>();
	    res.sort_by(|(w1, _), (w2, _)| {
		w1.cmp(w2)
	    });

	    for (w, cls) in res {
		println!("{:?}: {:?}", w.clause_ref(), cls);
	    }
	}


	fn print_watch(&self) {
	    for lit in -(self.n_vars as i32)..(self.n_vars as i32 + 1) {
		if lit == 0 { continue; }
		println!("literal {} is watching:", lit);
		println!("{}", (&self.watches[cal_idx!(lit, self.n_vars)])
			 .into_iter()
			 .map(|x| format!("{:?}", x.clause_ref()))
			 .collect::<Vec<String>>()
			 .join(" "));
	    }
	}
    }



    prop_compose! {
	fn clause(n_vars: usize)
	    (length in 2usize..n_vars+1)
	    (signs in vec(any::<bool>(), length),
	     vars in hash_set(1..n_vars as i32 +1, length))
	     -> Vec<i32> {
		let mut vars: Vec<_> = vars.into_iter().collect();
		for (i, var) in vars.iter_mut().enumerate() {
		    if !signs[i] { *var = -*var; }
		}
		vars
	    }
    }


    /// generate small SAT instances with number of varibales ranges
    /// from 3 to 6, number of clauses ranges from 5 to 14
    fn sat_instance() -> impl Strategy<Value = (usize, usize, Vec<Vec<i32>>)> {
	(3usize..7,
	 5usize..15)
	    .prop_flat_map(|(n_vars, n_clauses)| {
		vec(clause(n_vars), n_clauses)
		    .prop_map(move |clauses| (n_vars, n_clauses, clauses))
	    })
    }


    /*
    proptest! {
    #![proptest_config(ProptestConfig{
	    max_shrink_iters : 0,
	    ..ProptestConfig::default()
	})]
	#[test]
	fn test_gen((n_vars, n_clauses, clauses) in sat_instance()) {
	    println!("n_vars: {}", n_vars);
	    println!("n_clauses: {}", n_clauses);
	    for lits in clauses {
		println!("{}",
			 lits
			 .into_iter()
			 .map(|lit| format!("{}", lit))
			 .collect::<Vec<String>>()
			 .join(" "));
	    }

	    assert!(false);
	}
    }
     */


    proptest! {
	#![proptest_config(ProptestConfig{
	    max_shrink_iters : 0,
	    ..ProptestConfig::default()
	})]
	#[test]
	fn test_solver_initialize((n_vars, n_clauses, mut clauses) in sat_instance()) {
	    let mut solver = Solver::from_sat_instance(n_vars, n_clauses, clauses.clone(), true);

	    // watch clause should comes from the original sat instance
	    for lit in -(n_vars as i32)..(n_vars as i32 + 1) {
		if lit == 0 { continue; }
		for watch in &solver.watches[cal_idx!(lit, n_vars)] {
		    let clause = solver.allocator.get_clause(watch.clause_ref());
		    assert!(lit == clause.lits()[0] || lit == clause.lits()[1]);
		    assert!(clauses.contains(&clause.lits().to_vec()));
		}
	    }


	    // simulate a false_stack
	    solver.assign(1, None);
	    // solver.level.incr();
	    solver.propagate();

	    let mut num = 0;

	    for lit in -(n_vars as i32)..(n_vars as i32 + 1) {
		if lit == 0 { continue; }
		num += solver.watches[cal_idx!(lit, n_vars)].len();
	    }


	    assert_eq!(clauses.len() * 2, num);
	    
	}
    }

    #[test]
    fn test_propagate() {
	let mut solver
	    = Solver::from_sat_instance(
		3, 9,
		vec![vec![-3, -1, 2],
		     vec![3, 2],
		     vec![-1, -3],
		     vec![-2, 1],
		     vec![-2, -1],
		     vec![-2, 1, 3],
		     vec![1, -3],
		     vec![-2, -1, -3],
		     vec![1, 2, 3]], true);

	solver.print_all_clauses();
	solver.print_watch();

	// simlute a decision
	println!("assign literal 1 to be false");
	solver.assign(1, None);
	// solver.level.incr();
	let propagation_result = solver.propagate();

	assert!(!propagation_result); // conflict should be found
	assert_eq!(solver.buffer[1..(solver.buffer[0] as usize + 1)], [3, 2]);

	println!("propagation result: {}", propagation_result);

	solver.print_watch();

	
    }

}
