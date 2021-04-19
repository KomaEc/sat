# A Simple CDCL SAT Solver

## Design Principles of simplesat
Simplesat will feature several optimization strategies employed by most modern CDCL SAT solvers.
- [x] Two watched literals scheme
- [ ] VISD
- [ ] Lemma deletion
- [ ] Restart

It is documented and **property-based tested**. The properties that are tested:
* Invariants of the two watched literals scheme
* Solver soundness


## Termination Property
The termination property of the CDCL algorithm is not that obvious (at least to me). It is hypothetical that some paths may be repeatedly reached, since the backjump mechanism does not systematically explore the search space.

To prove termination, we aim at the following theorem.

> It is never the case that the solver enters decision level `dl` again with the same state.

At first glance, it seems that learned clauses may help. Indeed, a learned clause prevent the solver from entering the path that results in a backjump and generating itself. However, realistic solver appeals to forget learned clauses at certain points. Keeping all learned clauses not only leads to high time consumption of the propagation process, but also makes computer memory explode: in worst case, the number of learned clauses can reach O(2^n).

In fact, the solver terminates even if we do not keep learned clauses at all! The reason lies in the immediate implication of the learned asserting clause. Suppose the solver is currently at decision level *dl*, and will return back to `dl` again. Assume `dl'` is the lowest level the solver should reach in this period. Of course, `dl' <= dl`. Since `dl'` is the lowest, the solver can only backjump to this level. Each time the solver reaches `dl'`, a literal is immediately asserted by the learned clause at level `dl'`. So even if learned clauses are discarded right away, when the solver returns back to `dl`, it is with a different partial assignment.