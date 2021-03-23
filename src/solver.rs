

use crate::{
    clause::{Clause}
};

pub struct Solver {
    nVars : int, // number of variables of a SAT instance
    nClauses : int, // number of clauses
    nLemmas : int, // number of learned clauses
    database : &'static [int], // database that stores clauses and lemmas
}
