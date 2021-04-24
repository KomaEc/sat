# A Simple CDCL SAT Solver
Simplesat is a __conflict driven clause learning__ SAT solver. It features the two watched literals optimization scheme. It can solve some SAT problems with thousands of variables (`data/QG/qg5-13.cnf`). It is property-based tested.

## TODO
- [ ] Smarter allocator
- [ ] Heuristics (VSIDS, LBD)

## Discussion
Problems I met when implementing this algorithm

### Termination Property
The termination property of the CDCL algorithm is not that obvious (at least to me). It is hypothetical that some paths may be repeatedly reached, since the backjump mechanism does not systematically explore the search space.

To prove termination, we aim at the following theorem.

> It is never the case that the solver enters decision level `dl` again with the same state.

At first glance, it seems that learned clauses may help. Indeed, a learned clause prevent the solver from entering the path that results in a backjump and generating itself. However, realistic solver appeals to forget learned clauses at certain points. Keeping all learned clauses not only leads to high time consumption of the propagation process, but also makes computer memory explode: in worst case, the number of learned clauses can reach O(2^n).

In fact, the solver terminates even if we do not keep learned clauses at all! The reason lies in the immediate implication of the learned asserting clause. Suppose the solver is currently at decision level `dl`, and will return back to `dl` again. Assume `dl'` is the lowest level the solver should reach in this period. Of course, `dl' <= dl`. Since `dl'` is the lowest, the solver can only backjump to this level. Each time the solver reaches `dl'`, a literal is immediately asserted by the learned clause at level `dl'`. So even if learned clauses are discarded right away, when the solver returns back to `dl`, it is with a different partial assignment.


## Reference
I find these books, slides and codes very useful.
* Decision Procedure, 2nd Edition
* [SAT Solving and CDCL(T)](https://sat-smt-ws.gitlab.io/2019/assets/slides/matesatsmt.pdf)
* [SAT@Mandi 2019, Lecture 4: CDCL - optimizations](https://www.cse.iitb.ac.in/~akg/courses/2019-sat-mandi/lec-04-cdcl-opt.pdf)
* [microsat](https://github.com/marijnheule/microsat)
* [varisat](https://github.com/jix/varisat)
