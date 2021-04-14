
use std::fs::File;
use std::io::prelude::*;
use std::io;
use std::io::{Read, BufReader};
use std::vec::*;
use std::error::Error;


/// return n_vars, n_clauses, and all clause
fn parse_from_file(filename: &str)
		   -> io::Result<(usize, usize, Vec<Vec<i32>>)> {
    let file = File::open(filename)?;
    dimacs_parser(BufReader::new(file))
}


fn dimacs_parser<R>(mut br: BufReader<R>)
	    -> io::Result<(usize, usize, Vec<Vec<i32>>)>
where R : Read {

    // parse comment

    let mut n_vars = 0;
    let mut n_clauses = 0;
    let mut clauses: Vec<Vec<i32>>  = Vec::new();


    let mut lines = br.lines().skip_while(
	|line| {
	    let mut skip_flag = true;
	    if let Ok(ref line) = line {
		// println!("{}", line);
		// println!("does it starts with c? {}", line.starts_with('c'));
		if !line.starts_with('c') { skip_flag = false; }
	    }
	    skip_flag
	}
    );

    {
	let mut line = lines.next();

	if let Ok(ref line) = line.expect("expect problem definition") {
	    // assert!(line.starts_with('p'));
	    let problem: Vec<&str> = line.split(' ').collect();
	    assert_eq!(problem.len(), 4, "expect problem definition");
	    assert_eq!(problem[0], "p", "expect problem definition");
	    assert_eq!(problem[1], "cnf", "expect cnf");
	    n_vars = problem[2].parse::<usize>().expect("expect number of variables");
	    n_clauses = problem[3].parse::<usize>().expect("expect number of clauses");
	}
    }

    for line in lines {
	if let Ok(ref line) = line {
	    let clause: Vec<i32> = line.split(' ')
		.map(|x| x.parse::<i32>().expect("literal"))
		.collect();
	    clauses.push(clause);
	}
    }

    Ok((n_vars, n_clauses, clauses))

}

fn dimacs_printer(n_vars: usize, n_clauses: usize, clauses: &Vec<Vec<i32>>)
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
	res.push_str("\n");
    }

    res
}

#[cfg(test)]
mod tests {
    use super::*;

    use proptest::prelude::*;
    use proptest::collection::{hash_set, vec};

    #[test]
    fn test_parse_specialized() -> std::result::Result<(), std::io::Error> {

	let problem
	    = "c this is a SAT instance from the book\nc Decision Procedure\np cnf 6 8\n-1 2\n-1 3 5\n-2 4\n-3 -4\n1 5 -2\n2 3\n2 -3\n6 -5";

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
	
	println!("n_vars: {}", n_vars);
	assert_eq!(n_vars, 6);
	println!("n_clauses: {}", n_clauses);
	assert_eq!(n_clauses, 8);
	for clause in &clauses {
	    println!("{:?}", clause);
	}
	assert_eq!(clauses, clauses_ground_truth);


	let problem_gen = dimacs_printer(6, 8, &clauses_ground_truth);

	assert_eq!(format!("c this is a SAT instance from the book\nc Decision Procedure\n{}", problem_gen), format!("{}\n", problem));
	
	
	Ok(())
    }

    prop_compose! {
	fn lit(n_vars: usize)
	    (sign in any::<bool>(),
	     var in 1..n_vars+1)
	     -> i32 {
		let var = var as i32;
		if sign { var } else { -var }
	    }
    }

    prop_compose! {

	fn clause(n_vars: usize)
	    (v in vec(-(n_vars as i32)..n_vars as i32, 3usize..n_vars+1))
	     -> Vec<i32> {
		v
	    }
    }


    /*
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
     */

    fn sat_instance() -> impl Strategy<Value = (usize, usize, Vec<Vec<i32>>)> {
	(3usize..16,
	 5usize..40)
	    .prop_flat_map(|(n_vars, n_clauses)| {
		vec(clause(n_vars), n_clauses)
		    .prop_map(move |clauses| (n_vars, n_clauses, clauses))
	    })
    }

    proptest! {
	#[test]
	fn test_parse((n_vars, n_clauses, clauses) in sat_instance()) {
	    let str_repr = dimacs_printer(n_vars, n_clauses, &clauses);
	    if let Ok(parse_result) = dimacs_parser(BufReader::new(str_repr.as_bytes())) {
		assert_eq!((n_vars, n_clauses, clauses), parse_result);
	    } else {
		panic!("io error");
	    }
	}
    }

}
