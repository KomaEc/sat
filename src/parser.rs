
use std::io::prelude::*;
use std::io;
use std::io::{Read, BufReader};
use std::vec::Vec;


pub fn dimacs_parser<R>(br: BufReader<R>)
	    -> io::Result<(usize, usize, Vec<Vec<i32>>)>
where R : Read {

    // parse comment

    let n_vars;      
    let n_clauses;
    let mut clauses: Vec<Vec<i32>>  = Vec::new();


    let mut lines = br.lines().skip_while(
	|line| {
	    if let Ok(ref line) = line {
		if !line.starts_with('c') { return false; }
	    }
	    true
	}
    );


    let mut line: String = lines.next().expect("expect problem definition").expect("expect problem definition");
    // assert!(line.starts_with('p'));
    let problem: Vec<&str> = line.split_whitespace().collect();
    if problem.len() != 4 || problem[0] != "p" || problem[1] != "cnf" {
	panic!("expect problem definition");
    }
    n_vars = problem[2].parse::<usize>().expect("expect number of variables");
    n_clauses = problem[3].parse::<usize>().expect("expect number of clauses");


    for _ in 0..n_clauses {
	let mut dimacs_clause = Vec::new();
	loop {
	    line = lines.next().expect(&format!("expect {} clauses", n_clauses)).expect(&format!("expect {} clauses", n_clauses));
	    let nums: Vec<&str> = line.split_whitespace().collect();
	    let (last, previous) = &nums[..].split_last().expect("clause");
	    dimacs_clause.extend_from_slice(
		&previous.iter().map(|s| s.parse::<i32>().expect("literal")).collect::<Vec<_>>()[..]
	    );
	    let last_num = last.parse::<i32>().expect("number");
	    if last_num == 0 { break; }
	    dimacs_clause.push(last_num);
	}
	clauses.push(dimacs_clause);
    }

    Ok((n_vars, n_clauses, clauses))

}

#[allow(dead_code)]
pub fn dimacs_printer(n_vars: usize, n_clauses: usize, clauses: &Vec<Vec<i32>>)
		  -> String {
    let mut res = String::new();

    res.push_str(&format!("p cnf {} {}\n", n_vars, n_clauses));

    for clause in clauses {
	let cl_str = clause
	    .iter()
	    .map(|lit| format!("{}", *lit))
	    .collect::<Vec<String>>()
	    .join(" ");
	res.push_str(&cl_str);
	res.push_str(" 0\n");
    }

    res
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;
    use proptest::collection::{vec};

    #[test]
    fn test_parse_specialized() -> std::result::Result<(), std::io::Error> {

	let problem
	    = "c this is a SAT instance from the book\nc Decision Procedure\np cnf 6 8\n-1 2 0\n-1 3 5 0\n-2 4 0\n-3 -4 0\n1 5 -2 0\n2 3 0\n2 -3 0\n6 -5 0";

	let clauses_ground_truth
	    = vec![
		vec![-1, 2],
		vec![-1, 3, 5],
		vec![-2, 4],
		vec![-3, -4],
		vec![1, 5, -2],
		vec![2, 3],
		vec![2, -3],
		vec![6, -5]
	    ];

	let (n_vars, n_clauses, clauses) = dimacs_parser(BufReader::new(problem.as_bytes()))?;
	
	assert_eq!(n_vars, 6);
	assert_eq!(n_clauses, 8);
	assert_eq!(clauses, clauses_ground_truth);

	let problem_gen = dimacs_printer(6, 8, &clauses_ground_truth);

	assert_eq!(format!("c this is a SAT instance from the book\nc Decision Procedure\n{}", problem_gen), format!("{}\n", problem));
	
	
	Ok(())
    }

    prop_compose! {

	fn clause(n_vars: usize)
	    (v in vec(-(n_vars as i32+1)..n_vars as i32+1, 3usize..n_vars+1))
	     -> Vec<i32> {
		v
	    }
    }

    fn sat_instance() -> impl Strategy<Value = (usize, usize, Vec<Vec<i32>>)> {
	(3usize..16,
	 5usize..40)
	    .prop_flat_map(|(n_vars, n_clauses)| {
		vec(clause(n_vars), n_clauses)
		    .prop_map(move |clauses| (n_vars, n_clauses, clauses))
	    })
    }

    proptest! {
	/// print; parse = identity
	#[test]
	fn test_parser_backward_round_tripping((n_vars, n_clauses, clauses) in sat_instance()) {
	    let str_repr = dimacs_printer(n_vars, n_clauses, &clauses);
	    let parse_result = dimacs_parser(BufReader::new(str_repr.as_bytes())).expect("io error");
	    assert_eq!((n_vars, n_clauses, clauses), parse_result);
	}
    }

}
