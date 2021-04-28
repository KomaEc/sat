
use crate::{
    lit::{Var},
};

pub struct EVSIDS {
    scores: Box<[f64]>,
    order: Vec<Var>,
    inc: f64,
    pub last_chosen: Option<usize>,
}

impl EVSIDS {
    const VAR_DECAY: f64 = 1.2;
    const THRESHOLD: f64 = 10e200;

    pub fn new(n_vars: usize) -> Self {
	EVSIDS {
	    scores : vec![0.0; n_vars].into_boxed_slice(),
	    order : (1..n_vars as i32 + 1).map(|num| Var::from_dimacs(num)).collect(),
	    inc : 1.0,
	    last_chosen : None,
	}
    }

    fn rescore(&mut self) {
	for score in self.scores.iter_mut() {
	    *score /= Self::THRESHOLD;
	}
	self.inc /= Self::THRESHOLD;
    }

    pub fn decay(&mut self) {
	self.inc *= Self::VAR_DECAY;
	if self.inc > Self::THRESHOLD {
	    self.rescore();
	}
    }

    pub fn update_score(&mut self, var: Var) {
	self.scores[var.idx()] += self.inc;
	self.last_chosen = None;
    }

    pub fn rank(&mut self) {
	self.order.sort_by({
	    let scores = &self.scores;
	    move |v1, v2| scores[v2.idx()].partial_cmp(&scores[v1.idx()]).unwrap()
	});
    }

    pub fn decision_list(&self) -> &[Var] {
	&self.order[..]
    }
}
