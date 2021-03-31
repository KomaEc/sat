
/// data in Clause:
/// -------------------------------------------------------------------------
/// | length of data | next watch of fst wl | next watch of snd wl | clause |
/// -------------------------------------------------------------------------
///
///
///
#[repr(C)]
pub struct Clause {
    data : [i32], 
}

impl Clause {
    
}


#[cfg(test)]
mod tests {
    use super::*;
}
