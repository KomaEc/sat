
use std::fs::File;
use std::io::prelude::*;
use std::io;
use std::vec::*;

fn parse(filename: String) -> io::Result<Vec<Vec<i32>>> {

    let file = File::open(filename)?;
    
    Err(io::Error::new(io::ErrorKind::Other, "not implemented"))
}
