# A Simple CDCL SAT Solver

## Design Principles of simplesat
Simplesat is a _conflict driven clause learning_ SAT solver written in Rust. It will feature several optimization strategies employed by most modern CDCL SAT solvers.
- [x] Two watched literals scheme
- [x] No intermediate allocation
- [ ] Variable state independent decaying sum (VSIDS)
- [ ] Lemma deletion
- [ ] Restart

It is documented and _property-based tested_. The properties that are tested:
* Invariants of the two watched literals scheme
* Solver soundness


## TODO
- [ ] Refactor `Assignment` struct


## Discussion
I want to discuss several problems I met when implementing this algorithm in Rust.

### Termination Property
The termination property of the CDCL algorithm is not that obvious (at least to me). It is hypothetical that some paths may be repeatedly reached, since the backjump mechanism does not systematically explore the search space.

To prove termination, we aim at the following theorem.

> It is never the case that the solver enters decision level `dl` again with the same state.

At first glance, it seems that learned clauses may help. Indeed, a learned clause prevent the solver from entering the path that results in a backjump and generating itself. However, realistic solver appeals to forget learned clauses at certain points. Keeping all learned clauses not only leads to high time consumption of the propagation process, but also makes computer memory explode: in worst case, the number of learned clauses can reach O(2^n).

In fact, the solver terminates even if we do not keep learned clauses at all! The reason lies in the immediate implication of the learned asserting clause. Suppose the solver is currently at decision level `dl`, and will return back to `dl` again. Assume `dl'` is the lowest level the solver should reach in this period. Of course, `dl' <= dl`. Since `dl'` is the lowest, the solver can only backjump to this level. Each time the solver reaches `dl'`, a literal is immediately asserted by the learned clause at level `dl'`. So even if learned clauses are discarded right away, when the solver returns back to `dl`, it is with a different partial assignment.

### Interprocedural Borrow Conflicts
Please refer to this [article](http://smallcultfollowing.com/babysteps/blog/2018/11/01/after-nll-interprocedural-conflicts/) for the concept of _interprocedural borrow conflicts_ in Rust. I was not quite haunted by it, but it indeed happened.


### Watch Clause Removal