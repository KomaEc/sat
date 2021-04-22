

mod clause;
mod solver;
mod parser;
mod watch;
mod lit;

use crate::{
    solver::Solver,
    parser as dimacs_parser,
};
use std::fs::File;
use std::io::BufReader;
use std::env;

fn main() -> std::io::Result<()> {
    
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
	println!("expect one file");
	return Ok(());
    }
    let file = File::open(&args[1])?;
    let sat_instance = dimacs_parser::dimacs_parser(BufReader::new(file))?;
    println!("Solving SAT instance with {} variables and {} clauses", sat_instance.0, sat_instance.1);
    let mut solver = Solver::from_dimacs(sat_instance);
    // solver.print_all_clauses();
    if solver.solve() {
	println!("SAT");
    } else {
	println!("UNSAT");
    }
    Ok(())
}
