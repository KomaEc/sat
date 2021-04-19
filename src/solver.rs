

use crate::{
    clause::alloc::{Allocator, ClauseRef},
    watch::{Watch, WatchList}
};
use std::vec::Vec;


/// Calculate the index of a literal into arrays like [`assignment`]
macro_rules! cal_idx {
    ($lit: expr, $n_vars: expr) => {
	($lit + ($n_vars as i32)) as usize
    }
}

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


// #[repr(u8)]
#[derive(Clone, Copy, PartialEq, Debug)]
enum Assignment {
    Assigned(Level),
    Unassigned,
}

impl Assignment {
    fn level(&self) -> Level {
	match self {
	    Assignment::Assigned(l) => { *l },
	    Assignment::Unassigned => { Level(u16::MAX) },
	}
    }
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
    
    reason : Box<[ClauseRef]>, /// the reason clause for an implication
    /// length = 2 * n_vars + 1

    
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

    level: Level,
    /// decision level
    


    buffer : Vec<i32>, // a buffer to contain conflict clauses
    /// capacity of total buffer = n_vars
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
		reason : vec![ClauseRef::null(); 2*n_vars+1].into_boxed_slice(),
		false_stack : Vec::with_capacity(n_vars),
		assignment : vec![Assignment::Unassigned; 2*n_vars+1].into_boxed_slice(),
		watches : vec![WatchList::new(); 2*n_vars+1].into_boxed_slice(),
		marked : vec![false; 2*n_vars+1].into_boxed_slice(),
		processed : 0,
		level : Level::ground_level(),
		buffer : vec![0i32; n_vars],
		allocator : if small {
		    Allocator::small()
		} else {
		    Allocator::new()
		},
	    };

	for lits in clauses {
	    if lits.len() == 1 {
		solver.assign(-lits[0], ClauseRef::null());
	    } else {
		solver.add_clause(&lits);
	    }
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
		  lits: &[i32]) -> ClauseRef {
	let clause_ref = self.allocator.allocate_clause(lits);

	
	debug_assert!(lits.len() >= 2);
	// this is because, we do not add unary clauses to the database.
	// unary clauses, be it learned or original, are encoded as
	// ground level assertions.

	self.add_watch(clause_ref, lits[0]);
	self.add_watch(clause_ref, lits[1]);

	clause_ref
    }

    /// add lemma that is located in buffer
    fn add_lemma_in_buffer(&mut self) -> ClauseRef {
	if self.buffer.len() == 1 { return ClauseRef::null(); }
	
	let clause_ref = self.allocator.allocate_clause(&self.buffer[..]);

	self.add_watch(clause_ref, self.buffer[0]);
	self.add_watch(clause_ref, self.buffer[1]);
	
	clause_ref
    }

    /// Assign [`lit`] to be [`false`], set reason clause
    /// TODO: move push logic outside of [`assign()`]
    fn assign(&mut self, lit: i32, reason: ClauseRef) {
	self.false_stack.push(lit);
	let lit_idx = cal_idx!(lit, self.n_vars);

	self.assignment[lit_idx] = Assignment::Assigned(self.level);
	self.reason[lit_idx] = reason;

	#[cfg(debug_assertions)]
	if reason.is_null() {
	    println!("literal {} is assigned to be false at level {}", lit, self.level.0);
	} else {
	    println!("literal {} is implied to be false at level {}", lit, self.level.0);
	}
	
    }

    fn unassign(&mut self, lit: i32) {
	let lit_idx = cal_idx!(lit, self.n_vars);
	self.assignment[lit_idx] = Assignment::Unassigned;
    }

    /// naive false_stack
    fn naive_decide(&mut self) -> bool {
	self.level.incr();
	// increment decision level
	
	for var in 1..(self.n_vars as i32 + 1) {
	    if self.assignment[cal_idx!(var, self.n_vars)] == Assignment::Unassigned
		&& self.assignment[cal_idx!(-var, self.n_vars)] == Assignment::Unassigned {
		    self.assign(var, ClauseRef::null());
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
	#[cfg(debug_assertions)]
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
	
	loop {
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
		#[cfg(debug_assertions)]
		println!("visiting literal {} and clause {:?}", cur_lit, clause_ref);

		match self.force_clause_status(cur_lit, clause_ref) {
		    ClauseStatus::Unit(implied_lit) => {
			self.assign(implied_lit, clause_ref);
			i += 1;
		    },
		    ClauseStatus::Conflict => {
			let lits = self.allocator
			    .get_clause(clause_ref)
			    .lits();
			self.buffer.truncate(0);
			self.buffer.extend_from_slice(lits);
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
	    debug_assert!(self.watches[cur_lit_idx].is_empty());

	    watch_list.truncate(j);
	    std::mem::swap(&mut self.watches[cur_lit_idx], &mut watch_list);
	    // write back updated watch list

	    if conflict { return false; }
	    
	}

	true // propagation done, no conflict found
    }


    fn analyze_conflict(&mut self) -> bool {

	#[cfg(debug_assertions)]
	println!("conflict found: {}", self.buffer.iter().map(|x| format!("{:?}", *x)).collect::<Vec<String>>().join(" "));

	if self.level == Level::ground_level() { return false; } // root level conflict found, UNSAT

	unsafe { std::ptr::write_bytes(self.marked.as_mut_ptr(), 0, 2 * self.n_vars + 1); } // memset [`mark`] array to all false

	for lit in &self.buffer { // mark all literals in conflict clause
	    self.marked[cal_idx!(*lit, self.n_vars)] = true;
	}

	debug_assert!(self.false_stack.len() >= 1);

	self.processed = self.false_stack.len()-1;
	while !self.marked[cal_idx!(self.false_stack[self.processed], self.n_vars)] {
	    self.unassign(self.false_stack[self.processed]);
	    self.processed -= 1;
	}
	// now [`processed`] points to the last decision literal that is marked

	let mut snd_marked;
	{
	    let mut i = self.processed-1;
	    while !self.marked[cal_idx!(self.false_stack[i], self.n_vars)] { i -= 1; }
	    snd_marked = i;
	}
	// snd_marked is the last literal different from [`processed`] but is also marked

	debug_assert!(snd_marked < self.processed); // snd_marked must be properly initialized


	// in the following, maintain the variant:
	// all marked literals below and include [`processed`] form a separating cut to the conflict node
	// snd_marked <= processed and equality holds if and only if there is no further marked literal, and hence processed
	// is the first UIP

	loop {
	    let lit = self.false_stack[self.processed]; let lit_idx = cal_idx!(lit, self.n_vars);

	    #[cfg(debug_assertions)]
	    println!("resolving {}", lit);
	    #[cfg(debug_assertions)]
	    println!("reason: {:?}", self.reason[lit_idx]);
	    debug_assert!(self.marked[lit_idx]);
	    
	    
	    let reason_cls = self.allocator.get_clause(self.reason[lit_idx]);
	    self.buffer.swap_remove(self.buffer.iter().position(|lit2| *lit2 == lit).unwrap());
	    // let old_len = self.buffer.len();
	    // remove [`lit`] in original conflict clause
	    for lit2 in reason_cls.lits() {
		let lit2_idx = cal_idx!(*lit2, self.n_vars);
		if *lit2 == -lit { continue; }
		if !self.marked[lit2_idx] {
		    self.marked[lit2_idx] = true;
		    self.buffer.push(*lit2);
		}
	    }
	    // first, resolve conflict clause with the reason clause of [`processed`]

	    #[cfg(debug_assertions)]
	    println!("resolvent: {}", self.buffer.iter().map(|x| format!("{:?}", *x)).collect::<Vec<String>>().join(" "));
	    debug_assert!(!self.buffer.contains(&lit)); debug_assert!(!self.buffer.contains(&(-lit)));


	    while self.processed > snd_marked {
		self.unassign(self.false_stack[self.processed]);
		self.processed -= 1;
	    }
	    // set [`processed`] to be [`snd_marked`]

	    {
		let mut i = snd_marked;
		loop {
		    if self.reason[cal_idx!(self.false_stack[i], self.n_vars)].is_null() { break; }
		    // decision reached, no further marked, UIP found
		    i -= 1;
		    if self.marked[cal_idx!(self.false_stack[i], self.n_vars)] {
			snd_marked = i; break;
		    }
		}
	    }
	    // find snd_marked
	    
	    if snd_marked == self.processed { break; }
	    // first UIP found

	    /*
	    for lit2 in &self.buffer[old_len..] {
		self.marked[cal_idx!(*lit2, self.n_vars)] = true;
	    }
	     */
	    // else mark all literals in the previous reason clause
	}
	// Post invariant: [`processed`] points to the first UIP. Literals above [`processed`] are unassigned

	let first_uip = self.false_stack[self.processed];

	#[cfg(debug_assertions)]
	println!("uip found: {}", first_uip);
	#[cfg(debug_assertions)]
	println!("clause learned: {}", self.buffer.iter().map(|x| format!("{:?}", *x)).collect::<Vec<String>>().join(" "));
	debug_assert!(self.buffer.contains(&self.false_stack[self.processed])); // conflict clause contains the negation of the first UIP
	// since this solver is false-based, it contains the UIP

	let mut snd_highest_level = self.buffer
	    .iter()
	    .fold(Level::ground_level(),
		  |acc, lit| {
		      let level = self.assignment[cal_idx!(*lit, self.n_vars)].level();
		      if level < self.level { std::cmp::max(acc, level) }
		      else                  { acc }
		  });

	loop {
	    let lit = self.false_stack[self.processed];
	    let level = self.assignment[cal_idx!(lit, self.n_vars)].level();
	    if level == snd_highest_level { self.processed += 1; break; }
	    self.unassign(lit);
	    if self.processed == 0 { break; } // deal with corner case where there is no ground assertion and solver learns an unary clause
	    self.processed -= 1;
	}
	// after this loop, [`processed`] is set to be the correct decision length
	

	self.false_stack.truncate(self.processed); // undo false stack
	self.level = snd_highest_level; // set backtrack level
	let cref = self.add_lemma_in_buffer();
	self.assign(-first_uip, cref);

	#[cfg(debug_assertions)]
	println!("backtracking to level {}", self.level.0);

	true
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


	fn verify(&self) -> bool {
	    for lit in -(self.n_vars as i32)..(self.n_vars as i32 + 1) {
		if lit == 0 { continue; }
		for watch in &self.watches[cal_idx!(lit, self.n_vars)] {
		    let lits = self.allocator.get_clause(watch.clause_ref()).lits();
		    let mut satisfied = false;
		    for lit2 in lits {
			if let Assignment::Assigned(_) = self.assignment[cal_idx!(-lit2, self.n_vars)] {
			    satisfied = true;
			}
		    }
		    if !satisfied { return false; }
		}
	    }
	    true
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
    /// from 3 to 7, number of clauses ranges from 5 to 20
    fn sat_instance() -> impl Strategy<Value = (usize, usize, Vec<Vec<i32>>)> {
	(3usize..8,
	 5usize..21)
	    .prop_flat_map(|(n_vars, n_clauses)| {
		vec(clause(n_vars), n_clauses)
		    .prop_map(move |clauses| (n_vars, n_clauses, clauses))
	    })
    }


    proptest! {
	#![proptest_config(ProptestConfig{
	    max_shrink_iters : 0,
	    ..ProptestConfig::default()
	})]
	#[test]
	fn test_solver_initialize((n_vars, n_clauses, clauses) in sat_instance()) {
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
	    solver.assign(1, ClauseRef::null());
	    solver.level.incr();
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

	// solver.print_all_clauses();
	// solver.print_watch();

	// simlute a decision
	// println!("assign literal 1 to be false");
	solver.assign(1, ClauseRef::null());
	solver.level.incr();
	let propagation_result = solver.propagate();

	assert!(!propagation_result); // conflict should be found
	assert_eq!(solver.buffer, vec![3, 2]);

	// println!("propagation result: {}", propagation_result);

	solver.print_watch();

	solver.analyze_conflict();

	// assert!(false);
    }

    #[test]
    fn test_solver_multiple_backtrack_nontrivial_uip() {
	let mut solver
	    = Solver::from_sat_instance(
		5, 12, vec![vec![-5, 2, 1, -4, -3],
			    vec![-1, 2],
			    vec![4, 5, 1, 3, 2],
			    vec![-3, -4, -1, -5],
			    vec![-2, -5, 3],
			    vec![3, 2, -4, -1, -5],
			    vec![5, 4, 1],
			    vec![-4, 5],
			    vec![3, -5],
			    vec![-4, -2, 1, -3],
			    vec![-1, 5, 4],
			    vec![-3, -5]], true);
	// solver.print_all_clauses();
	if solver.solve() {
	    println!("SAT");
	} else {
	    println!("UNSAT");
	}
    }

    #[test]
    fn test_solver_memset_marked() {
	let mut solver
	    = Solver::from_sat_instance(
		3, 7, vec![vec![3, 2, 1],
			   vec![1, -3, 2],
			   vec![-3, -2],
			   vec![2, -1, -3],
			   vec![3, -2],
			   vec![-3, -1, -2],
			   vec![-2, 3, -1]], true);
	// solver.print_all_clauses();
	if solver.solve() {
	    println!("SAT");
	} else {
	    println!("UNSAT");
	}
    }

    #[test]
    fn test_unsat1() {
	let mut solver
	    = Solver::from_sat_instance(
		4, 18, vec![vec![1, 3, -4, 2],
			    vec![4, 3, 1, 2],
			    vec![-4, -3, -2, 1],
			    vec![-3, 2],
			    vec![-4, 2, 3, -1],
			    vec![-1, -4, 3],
			    vec![3, -4, 1],
			    vec![4, -1, 3],
			    vec![-1, 2, 4, -3],
			    vec![3, 1, 2, -4],
			    vec![-1, -4, -3, -2],
			    vec![-2, 4, 1],
			    vec![4, -2],
			    vec![-2, 1],
			    vec![-4, 3],
			    vec![3, 2, 4],
			    vec![-2, 3],
			    vec![-3, 1, 2]], true);

	solver.print_all_clauses();
	assert!(!solver.solve());
    }

    #[test]
    fn test_unsat2() {
	let mut solver
	    = Solver::from_sat_instance(
		2, 3, vec![vec![1, -2],
			   vec![-1],
			   vec![2]], true);

	// solver.print_all_clauses();
	assert!(!solver.solve());
    }

    #[test]
    fn test_unsat3() {
	let mut solver
	    = Solver::from_sat_instance(
		8, 12, vec![vec![6, 2],
			    vec![-6, 2],
			    vec![-2, 1],
			    vec![-1],
			    vec![-6, 8],
			    vec![6, -8],
			    vec![2, 4],
			    vec![-4, 5],
			    vec![7, 5],
			    vec![-7, 5],
			    vec![-5, 3],
			    vec![-3]], true);

	// solver.print_all_clauses();
	assert!(!solver.solve());	
    }


    proptest! {
	#![proptest_config(ProptestConfig{
	    max_shrink_iters : 0,
	    ..ProptestConfig::default()
	})]
	#[test]
	fn test_solver_not_fail((n_vars, n_clauses, clauses) in sat_instance()) {
	    let mut solver = Solver::from_sat_instance(n_vars, n_clauses, clauses.clone(), true);
	    // solver.print_all_clauses();
	    if solver.solve() {
		println!("SAT");
	    } else {
		println!("UNSAT");
	    }
	    println!("");
	}
    }

    proptest! {
	#![proptest_config(ProptestConfig{
	    max_shrink_iters : 0,
	    ..ProptestConfig::default()
	})]
	#[test]
	fn test_solver_soundness((n_vars, n_clauses, clauses) in sat_instance()) {
	    let mut solver = Solver::from_sat_instance(n_vars, n_clauses, clauses.clone(), true);
	    if solver.solve() {
		assert!(solver.verify());
	    }
	    println!("");
	}
    }


    /*
    proptest! {
	#![proptest_config(ProptestConfig{
	    max_shrink_iters : 0,
	    ..ProptestConfig::default()
	})]
	#[test]
	fn find_unsat((n_vars, n_clauses, clauses) in sat_instance()) {
	    let mut solver = Solver::from_sat_instance(n_vars, n_clauses, clauses.clone(), true);
	    solver.print_all_clauses();
	    assert!(solver.solve());
	    println!("");
	}
    }
     */
    
}
