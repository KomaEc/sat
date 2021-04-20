
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
    let mut solver = Solver::from_dimacs(dimacs_parser::dimacs_parser(BufReader::new(file))?);
    if solver.solve() {
	println!("SAT");
    } else {
	println!("UNSAT");
    }
    Ok(())
}
