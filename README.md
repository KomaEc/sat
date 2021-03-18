# CDCL SAT SOLVER

## Termination Property
The termination property of the CDCL algorithm is not obvious (at least to me). Since the backjump mechanism does not systematically explore the search space, it is hypothetical that some paths may be repeatedly reached.

To prove termination, we aim at the following theorem.
**Theorem** It is never the case that the solver enters decision level *dl* again with the same state.

At first glance, it seems that learned clauses may help. Indeed, a learned clause prevent the solver from entering the path that results in a backjump and generating the clause itself. However, realistic solver appeals to forget learned clauses at certain points. Keeping all learned clauses not only leads to high time consumption of the propagation process, but also makes computer memory explode: in worst case, the number of learned clauses can reach O(2^n).

In fact, the solver terminates even if we do not keep learned clauses at all! It is useful to treat backjump and the subsequent propagation as a whole: each backjump generates a direct implication by propagation. Now consider a partial assignment *P* at decision level *dl*, and assume that later the solver backjumps to decision level *dl'* with *dl'* < *dl* and partial assignment *P'*. Apparently *P* subsumes *P'*. Note that an implication at *dl'* is made immediately due to the backjump, augmenting *P'* to be *P''*. This implication must negate the assignment of a literal that is the decision or implication at level *dl* or higher, therefore, *P* does not subsume *P''*. If the solver progresses to decision level *dl* again without further backjumps, it is with a different partial assignment. Note that as long as the solver does not backjump to decision level lower than *dl'*, the above implication remains there. Therefore, we have
**Lemma** If the solver progresses to decision level *dl* again without further backjumps to levels lower than *dl'*, it is with a different partial assignment.

We are closer to the theorem. Now the obstacle seems to be that what if the solver backjumps to a level lower than *dl'*? Note that even if the immediate implication is implied by *P*, it is with a different decision level. Therefore, the next time it reaches *dl*, it is with a different state.