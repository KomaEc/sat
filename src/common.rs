

use std::vec::Vec;
use std::result::Result;

pub fn do_stuff_retain<T, F>(v: &mut Vec<T>, mut f: F) -> Result<(), ()>
where F: FnMut(&mut T) -> Result<bool, ()> {
    let mut j = v.len(); let mut i = 0;
    let mut fail_flag = Ok(());

    while i < j {
	match f(&mut v[i]) {
	    Ok(true) => { i += 1; },
	    Ok(false) => { v.swap(i, j-1); },
	    Err(_) => { fail_flag = Err(()); break; },
	}
    }

    v.truncate(j);

    fail_flag
}



#[repr(transparent)]
pub struct Wrapper<T: ?Sized>(T);

use std::ops::{Index, IndexMut};

impl<T> Wrapper<T> {
    pub fn cast(ptr: &T) -> &Wrapper<T> {
	unsafe { &*(ptr as * const T as * const Wrapper<T>) }
    }
}

impl<T> Index<i32> for Wrapper<[T]> {
    type Output = T;

    fn index(&self, i: i32) -> &Self::Output {
	let ptr = self.0.as_ptr();
	unsafe {
	    ptr.offset(i as isize).as_ref().unwrap()
	}
    }
}

impl<T> IndexMut<i32> for Wrapper<[T]> {

    fn index_mut(&mut self, i: i32) -> &mut Self::Output {
	let ptr = self.0.as_mut_ptr();
	unsafe {
	    ptr.offset(i as isize).as_mut().unwrap()
	}
    }
}


#[cfg(test)]
mod tests {
    use super::*;


    #[test]
    fn test_wrapper_slice() {
	const size : usize = 20;
	let mut heap = [0i32; 2 * size + 1];
	for (i, x) in heap.iter_mut().enumerate() {
	    *x = i as i32;
	}
	let mut ptr = heap.as_ptr();
	let mut heap_ref : &Wrapper<[i32]> =
	    unsafe {
		std::mem::transmute({
		    let mut ptr = ptr.offset(size as isize).as_ref().unwrap();
		    std::slice::from_raw_parts(ptr, size)
		})};
	assert_eq!(heap_ref[-20], 0);
	assert_eq!(heap_ref[-19], 1);
	assert_eq!(heap_ref[-17], 3);
	assert_eq!(heap_ref[13], 33);
	
    }
}
