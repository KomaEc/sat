mod clause;
mod evsids;
mod lit;
mod parser;
mod solver;
mod watch;

use crate::{parser as dimacs_parser, solver::Solver};
use std::env;
use std::fs::File;
use std::io::BufReader;
use std::time::Instant;

fn main() -> std::io::Result<()> {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        println!("expect one file");
        return Ok(());
    }
    let file = File::open(&args[1])?;
    let sat_instance = dimacs_parser::dimacs_parser(BufReader::new(file))?;
    println!(
        "Solving SAT instance with {} variables and {} clauses",
        sat_instance.0, sat_instance.1
    );
    let mut solver = Solver::from_dimacs(sat_instance);
    // solver.print_all_clauses();

    let start = Instant::now();

    if solver.solve() {
        println!("SAT");
    } else {
        println!("UNSAT");
    }

    let duration = start.elapsed();
    println!("finished in time {:?}", duration);

    Ok(())
}
