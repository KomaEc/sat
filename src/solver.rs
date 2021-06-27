use crate::{
    clause::alloc::{Allocator, ClauseRef},
    evsids::EVSIDS,
    lit::{Lit, Var},
    watch::{Watch, WatchList},
};
use std::vec::Vec;

/// Decision level. Assignment to a literal is also represented by its level. A literal is not assigned if and if only its level
/// is `u32::MAX`. This is reasonable, because we can treat implications with lower levels as more reliable. Ground level implications
/// are just assertions.
#[repr(transparent)]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
struct Level(u32);

impl Level {
    const GROUND: Self = Level(0);
    const ABSURD: Self = Level(u32::MAX);

    fn not_assigned(self) -> bool {
        self.0 == u32::MAX
    }
}

impl std::ops::AddAssign<u32> for Level {
    fn add_assign(&mut self, other: u32) {
        self.0 += other;
    }
}

/// `Delayed` clause can be either unit or unresolved or satisfed
#[derive(Clone, Copy, PartialEq, Debug)]
enum ClauseStatus {
    Unit(Lit),
    Conflict,
    Delayed,
    /// lazy clause status. If we can be lazy, we can be lazier :)
    Satisfied,
}

/// The main solver data structure
pub struct Solver {
    n_vars: usize,
    /// number of variables of a SAT instance
    n_clauses: usize,
    /// number of clauses
    n_lemmas: usize,
    /// number of learned clauses
    max_lemmas: usize,
    /// maximum number of learned clauses
    reason: Box<[ClauseRef]>,
    /// the reason clause for an implication
    /// length = 2 * n_vars
    false_stack: Vec<Lit>,
    /// false_stack stack, holds literals that is assigned to be false
    /// length = n_vars
    assignment: Box<[Level]>,
    /// assignment info
    /// length = 2 * n_vars
    watches: Box<[WatchList]>,
    /// clauses watching a literal
    /// length = 2 * n_vars
    marked: Box<[bool]>,
    /// we can treat is as the resolvent during the analyzing process
    /// length = 2 * n_vars
    processed: usize,
    /// a pointer into the false stack for processing literals
    /// Invariant: processed = false_stack.len() after succesful propagation and false_stack.len()-1 after analyze
    level: Level,
    /// decision level
    buffer: Vec<Lit>, // a buffer to contain conflict clauses
    /// capacity of total buffer = n_vars
    database: Allocator,

    decision_heuristic: EVSIDS,
}

/// Data Structures
/// 1. false stack. A stack holding literals in the current assignment (assigned to be false).
/// 2. Two watched literals scheme
///    Invariant: At any time, the two watched literals of a clause  must be non-false at levels lower than current level.
///    After [`propagation()`], they must be non-false regardless of levels.
///    Why `two` watches not one? After all, one watch is enough for checking clause status. The answer is one watch may loss
///    arc consistency. Consider the following scenario: a clause is watched by a literal, which is unassigned at this point, and
///    after current false_stack and implications, all other literals are assigned to be false. Since the watch literal is left
///    untouched in this round, the solver will never check this clause. Therefore, arc consistency is lost.
/// 3. Decided and Implied. The reason clause reference of a decided literal is null, while that of a implied literal is not.

/// Learnt clauses are implied by the original set of clauses. Starting from one original clause (the conflict clause),
/// a learnt clause is constructed by multiple steps of resolusion of this clause with other clauses.

/// Backtrack level: the second highest level in the learnt clause.

/// Stop criteria: resolusion stops when current clause contains the negation of the first Unique Implication Point (UIP) as
/// the [only] literal that is at current false_stack level. This criteria provides the [lowest] false_stack level. The reason
/// is pretty simple: resolusion only eliminates literals at current assignment, so further resolusion will not affects
/// other literals other than the first UIP, and will only introduce other literals with possibly higher levels.

impl Solver {
    pub fn from_dimacs(dimacs: (usize, usize, Vec<Vec<i32>>)) -> Self {
        let (n_vars, n_clauses, clauses) = dimacs;
        let mut solver = Solver {
            n_vars,
            n_clauses,
            n_lemmas: 0,
            max_lemmas: 2000,
            reason: vec![ClauseRef::null(); 2 * n_vars].into_boxed_slice(),
            false_stack: Vec::with_capacity(n_vars),
            assignment: vec![Level::ABSURD; 2 * n_vars].into_boxed_slice(),
            watches: vec![WatchList::new(); 2 * n_vars].into_boxed_slice(),
            marked: vec![false; 2 * n_vars].into_boxed_slice(),
            processed: 0,
            level: Level::GROUND,
            buffer: vec![Lit::from(0); n_vars],
            database: if cfg!(debug_assertions) {
                Allocator::small()
            } else {
                Allocator::new()
            },
            decision_heuristic: EVSIDS::new(n_vars),
        };

        for lits in clauses {
            if lits.len() == 1 {
                solver.n_clauses -= 1;
                solver.assign(-Lit::from_dimacs(lits[0]), ClauseRef::null());
            } else {
                solver.add_clause(&lits.into_iter().map(Lit::from_dimacs).collect::<Vec<_>>()[..]);
            }
        }

        solver
    }

    /// Add [`lit`] as a watch literal to the clause
    fn add_watch(&mut self, clause_ref: ClauseRef, lit: Lit) {
        self.watches[lit.idx()].add_watch(Watch::new(clause_ref));
    }

    /// Allocate a new clause containing literals in `lits`, set up two watched literals scheme
    fn add_clause(&mut self, lits: &[Lit]) -> ClauseRef {
        let clause_ref = self.database.allocate_clause(lits);

        debug_assert!(lits.len() >= 2);
        // this is because, we do not add unary clauses to the database.
        // unary clauses, be it learned or original, are encoded as
        // ground level assertions.

        self.add_watch(clause_ref, lits[0]);
        self.add_watch(clause_ref, lits[1]);

        clause_ref
    }

    /// Assign `lit` to be `false`, set reason clause
    /// TODO: move push logic outside of `assign()`
    fn assign(&mut self, lit: Lit, reason: ClauseRef) {
        self.false_stack.push(lit);

        self.assignment[lit.idx()] = self.level;
        self.reason[lit.idx()] = reason;

        #[cfg(debug_assertions)]
        {
            if reason.is_null() {
                println!(
                    "literal {} is assigned to be false at level {}",
                    lit, self.level.0
                );
            } else {
                println!(
                    "literal {} is implied to be false at level {}",
                    lit, self.level.0
                );
            }
        }
    }

    fn unassign(&mut self, lit: Lit) {
        self.assignment[lit.idx()] = Level::ABSURD;
    }

    /// Force the variant of two watch literals scheme.
    /// Precondition: `watch_lit` is a watch literal of clause `clause_ref`, and it is assigned to be false.
    /// Return `Unit(lit)` if the clause is a unit clause, and `lit` is negation of the only unassigned literal in this clause.
    /// For example, under partial assignment `[x1 -> true, x2 -> false]` the status of clause `~x1 \/ x2 \/ ~x3` is `Unit(x3)`,
    /// it implies that x3 should be false.
    /// Note that it will never touch `self.watches[wlit]`
    fn force_clause_status(&mut self, wlit: Lit, clause_ref: ClauseRef) -> ClauseStatus {
        debug_assert!(!self.assignment[wlit.idx()].not_assigned());

        let clause = self.database.get_clause_mut(clause_ref);
        let (first_two, rest) = clause.lits_mut().split_at_mut(2);

        // ensure another watch is placed before `wlit`
        if wlit != first_two[1] {
            first_two[0] = first_two[1];
        }

        // now, first_two[1] is meaningless

        // at this point, the another watch is unassigned w.r.t.
        // current false_stack stack up tp `wlit`

        let non_false = rest.iter().position({
            let assignment = &self.assignment;
            move |lit| assignment[lit.idx()].not_assigned()
        });
        // use move keyword to capture assignment by move

        match non_false {
            Some(i) => {
                let lit = rest[i];
                first_two[1] = lit;
                rest[i] = wlit;
                // swap literals

                self.add_watch(clause_ref, lit);
                // add new watch

                ClauseStatus::Delayed
            }
            None => {
                first_two[1] = wlit;
                // place watch here

                // the clause is either unit or conflict
                let wlit2 = first_two[0];

                if self.assignment[(-wlit2).idx()].not_assigned() {
                    if self.assignment[wlit2.idx()].not_assigned() {
                        // unit clause found, implying `-wlit2` to be false
                        ClauseStatus::Unit(-wlit2)
                    } else {
                        // conflict found
                        ClauseStatus::Conflict
                    }
                } else {
                    // else wlit2 is satisfied
                    ClauseStatus::Satisfied
                }
            }
        }
    }

    /// Boolean unit propagation
    fn propagate(&mut self) -> bool {
        loop {
            if self.processed == self.false_stack.len() {
                break;
            }
            // else processed <= decided
            let cur_lit = self.false_stack[self.processed];
            self.processed += 1;
            // get current unprocessed false_stack literal that is assigned
            // to be false

            let mut conflict = false;
            let mut j = self.watches[cur_lit.idx()].len();
            let mut i = 0;
            while i < j {
                let clause_ref = self.watches[cur_lit.idx()][i].clause_ref();

                #[cfg(debug_assertions)]
                {
                    println!("visiting literal {} and clause {:?}", cur_lit, clause_ref);
                }

                match self.force_clause_status(cur_lit, clause_ref) {
                    ClauseStatus::Unit(implied_lit) => {
                        self.assign(implied_lit, clause_ref);
                        i += 1;
                    }
                    ClauseStatus::Conflict => {
                        let lits = self.database.get_clause(clause_ref).lits();
                        self.buffer.truncate(0);
                        self.buffer.extend_from_slice(lits);
                        // copy conflict clause into buffer
                        conflict = true;
                        break;
                        // conflict found
                    }
                    ClauseStatus::Satisfied => {
                        i += 1;
                    }
                    ClauseStatus::Delayed => {
                        // in this case, `cur_lit` no longer watches `clause_ref`, delete it replace watch positioned
                        // at `i` with that of `j-1`
                        self.watches[cur_lit.idx()].swap(i, j - 1);
                        j -= 1;
                    }
                }
            }

            self.watches[cur_lit.idx()].truncate(j);

            if conflict {
                return false;
            }
        }

        true // propagation done, no conflict found
    }

    fn analyze_conflict(&mut self) -> bool {
        self.decision_heuristic.decay(); // new conflict, decay

        #[cfg(debug_assertions)]
        {
            println!(
                "conflict found: {}",
                self.buffer
                    .iter()
                    .map(|x| format!("{}", *x))
                    .collect::<Vec<String>>()
                    .join(" ")
            );
        }

        if self.level == Level::GROUND {
            return false;
        } // root level conflict found, UNSAT

        unsafe {
            // memset `mark` array to all false
            std::ptr::write_bytes(self.marked.as_mut_ptr(), 0, 2 * self.n_vars);
        }

        for lit in &self.buffer {
            // mark all literals in conflict clause
            self.marked[(*lit).idx()] = true;
            self.decision_heuristic.update_score(Var::from(*lit));
            // update score
        }
        self.buffer.truncate(0);

        debug_assert!(self.false_stack.len() >= 1);

        self.processed = self.false_stack.len() - 1;
        while !self.marked[self.false_stack[self.processed].idx()] {
            self.unassign(self.false_stack[self.processed]);
            self.processed -= 1;
        }
        // now `processed` points to the last decision literal that is marked

        // Pre Invariant: lit is not the uip
        loop {
            let lit = self.false_stack[self.processed];

            #[cfg(debug_assertions)]
            {
                println!("resolving {}", lit);
                println!("reason: {:?}", self.reason[lit.idx()]);
                debug_assert!(self.marked[lit.idx()]);
            }

            let reason_cls = self.database.get_clause(self.reason[lit.idx()]);
            for lit in reason_cls.lits() {
                self.marked[lit.idx()] = true;
                self.decision_heuristic.update_score(Var::from(*lit));
                // update score
            }
            // mark all literals in reason clause (resolve conflict clause with it)

            self.unassign(self.false_stack[self.processed]);
            self.processed -= 1;
            // unassign resolution variable

            while !self.marked[self.false_stack[self.processed].idx()] {
                self.unassign(self.false_stack[self.processed]);
                self.processed -= 1;
            }
            // find next marked

            let mut is_uip = true;
            {
                let mut check = self.processed;
                while !self.reason[self.false_stack[check].idx()].is_null() {
                    check -= 1;
                    if self.marked[self.false_stack[check].idx()] {
                        is_uip = false;
                        break;
                    }
                }
            }

            if is_uip {
                break;
            }
        }
        // Post invariant: `processed` points to the first UIP. Literals above `processed` are unassigned

        let first_uip = self.false_stack[self.processed];
        {
            let assign_idx = self.processed;
            self.processed += 1;
            while self.processed > 0 {
                let lit = self.false_stack[self.processed - 1];
                if self.assignment[lit.idx()] == Level::GROUND {
                    break;
                } // ground level assertions are ruled out
                if self.marked[lit.idx()] {
                    // self.decision_heuristic.update_score(Var::from(lit));
                    // update score
                    self.buffer.push(lit);
                }
                self.processed -= 1;
            }
            self.processed = assign_idx;
        }
        // build conflict clause

        #[cfg(debug_assertions)]
        {
            println!("uip found: {}", first_uip);
            println!(
                "clause learned: {}",
                self.buffer
                    .iter()
                    .map(|x| format!("{}", *x))
                    .collect::<Vec<String>>()
                    .join(" ")
            );
            debug_assert!(self.buffer.contains(&first_uip));
            // since this solver is false-based, it contains the UIP
            debug_assert_eq!(
                1,
                self.buffer.iter().fold(0, |acc, lit| {
                    acc + if self.assignment[(*lit).idx()] < self.level {
                        0
                    } else {
                        1
                    }
                })
            );
            debug_assert!(self
                .buffer
                .iter()
                .all(|lit| !self.assignment[(*lit).idx()].not_assigned()));
        }

        let snd_highest_level = self.buffer.iter().fold(Level::GROUND, |acc, lit| {
            let level = self.assignment[(*lit).idx()];
            if level < self.level {
                std::cmp::max(acc, level)
            } else {
                acc
            }
        });

        self.processed += 1;
        while self.processed > 0 {
            let lit = self.false_stack[self.processed - 1];
            let level = self.assignment[lit.idx()];
            if level == snd_highest_level {
                break;
            }
            self.unassign(lit);
            self.processed -= 1;
        }
        // after this loop, `processed` is set to be the correct decision length

        self.false_stack.truncate(self.processed); // undo false stack
        self.level = snd_highest_level; // set backtrack level
        if self.buffer.len() > 1 {
            let mut place_holder = Vec::new();
            std::mem::swap(&mut self.buffer, &mut place_holder);
            // take ownership
            self.n_lemmas += 1;
            let cref = self.add_clause(&place_holder[..]);
            self.assign(-first_uip, cref);
            std::mem::swap(&mut self.buffer, &mut place_holder);
            // write back buffer
        } else {
            // unary clause found
            self.assign(-first_uip, ClauseRef::null());
        }

        #[cfg(debug_assertions)]
        {
            println!("backtracking to level {}", self.level.0);
        }

        true
    }

    #[allow(dead_code)]
    fn naive_decide(&mut self) -> bool {
        self.level += 1;
        // increment decision level

        for var in 1..(self.n_vars as i32 + 1) {
            if self.assignment[Lit::from_dimacs(var).idx()].not_assigned()
                && self.assignment[Lit::from_dimacs(-var).idx()].not_assigned()
            {
                self.assign(Lit::from_dimacs(var), ClauseRef::null());
                return true;
            }
        }

        false
    }

    fn decide(&mut self) -> bool {
        self.level += 1;

        let start_idx = match self.decision_heuristic.last_chosen {
            None => {
                self.decision_heuristic.rank();
                0
            }
            Some(idx) => idx + 1,
        };
        let decision_list = self.decision_heuristic.decision_list();
        let mut decision_var = None;
        let mut new_start_idx = start_idx;
        for (i, var) in (&decision_list[start_idx..]).iter().enumerate() {
            if self.assignment[var.to_lit().idx()].not_assigned()
                && self.assignment[var.to_neg_lit().idx()].not_assigned()
            {
                decision_var = Some(*var);
                new_start_idx += i;
                break;
            }
        }
        match decision_var {
            Some(var) => {
                self.assign(var.to_lit(), ClauseRef::null());
                self.decision_heuristic.last_chosen = Some(new_start_idx);
                true
            }
            None => false,
        }
    }

    pub fn solve(&mut self) -> bool {
        loop {
            if !self.propagate() {
                if !self.analyze_conflict() {
                    return false;
                }
            } else if !self.decide() {
                return true;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::collection::{hash_set, vec};
    use proptest::prelude::*;

    proptest! {
    #[test]
    fn test_level(l in (0..u32::MAX)) {
        assert!(!Level(l).not_assigned());
        assert!(Level::ABSURD.not_assigned());
    }
    }

    /// utility functions and properties to be tested
    impl Solver {
        fn print_all_clauses(&self) {
            let mut occurs = std::collections::HashMap::new();
            for lit in -(self.n_vars as i32)..(self.n_vars as i32 + 1) {
                if lit == 0 {
                    continue;
                }
                let lit = Lit::from_dimacs(lit);
                for watch in &self.watches[lit.idx()] {
                    if !occurs.contains_key(watch) {
                        let clause = self
                            .database
                            .get_clause(watch.clause_ref())
                            .lits()
                            .iter()
                            .map(|lit| (*lit).to_dimacs())
                            .collect::<Vec<_>>();
                        occurs.insert(watch, clause);
                    }
                }
            }

            let mut res = occurs.iter().collect::<Vec<(_, _)>>();
            res.sort_by(|(w1, _), (w2, _)| w1.cmp(w2));

            for (w, cls) in res {
                println!("{:?}: {:?}", w.clause_ref(), cls);
            }
        }

        fn print_watch(&self) {
            for lit in -(self.n_vars as i32)..(self.n_vars as i32 + 1) {
                if lit == 0 {
                    continue;
                }
                let lit = Lit::from_dimacs(lit);
                println!("literal {} is watching:", lit);
                println!(
                    "{}",
                    (&self.watches[lit.idx()])
                        .into_iter()
                        .map(|x| format!("{:?}", x.clause_ref()))
                        .collect::<Vec<String>>()
                        .join(" ")
                );
            }
        }

        fn watched_lits_positioned_at_first_two(&self) -> bool {
            for lit in -(self.n_vars as i32)..(self.n_vars as i32 + 1) {
                if lit == 0 {
                    continue;
                }
                let lit = Lit::from_dimacs(lit);
                for watch in &self.watches[lit.idx()] {
                    let lits = self.database.get_clause(watch.clause_ref()).lits();
                    if lit != lits[0] && lit != lits[1] {
                        return false;
                    }
                }
            }
            true
        }

        fn watch_scheme_invariant(&self) -> bool {
            for lit in -(self.n_vars as i32)..(self.n_vars as i32 + 1) {
                if lit == 0 {
                    continue;
                }
                let lit = Lit::from_dimacs(lit);
                for watch in &self.watches[lit.idx()] {
                    if !(self.assignment[lit.idx()].not_assigned()) {
                        // if [`lit`] is falsified, then another watch must be satisfied
                        let lits = self.database.get_clause(watch.clause_ref()).lits();
                        let lit2 = {
                            if lit == lits[0] {
                                lits[1]
                            } else {
                                lits[0]
                            }
                        };
                        if self.assignment[(-lit2).idx()].not_assigned() {
                            return false;
                        }
                    }
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
        (3usize..8, 5usize..31).prop_flat_map(|(n_vars, n_clauses)| {
            vec(clause(n_vars), n_clauses).prop_map(move |clauses| (n_vars, n_clauses, clauses))
        })
    }

    #[test]
    fn test_solver_multiple_backtrack_nontrivial_uip() -> std::io::Result<()> {
        use crate::parser as dimacs_parser;
        use std::fs::File;
        use std::io::BufReader;

        let file = File::open("data/debug.cnf")?;
        let sat_instance = dimacs_parser::dimacs_parser(BufReader::new(file))?;
        println!(
            "Solving SAT instance with {} variables and {} clauses",
            sat_instance.0, sat_instance.1
        );
        let mut solver = Solver::from_dimacs(sat_instance);
        assert!(solver.solve());
        Ok(())
    }

    proptest! {
    #[test]
    fn test_watch_scheme_invariant(dimacs in sat_instance()) {
        let mut solver = Solver::from_dimacs(dimacs);
        loop {
        assert!(solver.watched_lits_positioned_at_first_two());
        if !solver.propagate() {
            if !solver.analyze_conflict() { break; }
        } else {
            // assert!(solver.watch_lits_positioned_at_first_two());
            assert!(solver.watch_scheme_invariant());
            if !solver.naive_decide() {
            break;
            }
        }
        }
    }
    }
}
