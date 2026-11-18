# A dependent third objective in multi-objective Max-Cut benchmarks

_18 November 2026_

In [1], multi-objective Max-Cut is studied with K = 3 objectives, each the weight of the cut edges under its own edge weights, and all three are maximized: a cut z dominates z′ "if f_k(z) ≥ f_k(z′) for all k ∈ [K] and F(z) ≠ F(z′)" [1, Definition 2]. The generated instances with n ∈ {20, 100, 200}, on complete graphs and on random graphs with edge probability 0.5, give every edge the weights w1 = c1 + 5, w2 = c2 + 5 and w3 = −0.5 w1 − 5 w2 for random integers c1, c2 [1, Appendix C.5.1]. As noted there, this gives f3(z) = −0.5 f1(z) − 5 f2(z) for every cut z. Methods are compared by the percentage of hypervolume (%HV) relative to the exact front at n = 20 and to the best observed final hypervolume at n = 100 and 200.

## Result

**No cut dominates another.** Let w3 = −a w1 − b w2 on every edge with a, b > 0, and let all three objectives be maximized. If two cuts z and z′ satisfy f_k(z) ≥ f_k(z′) for k = 1, 2, 3, then their value vectors are equal. So every distinct value vector of a cut is Pareto-optimal, and the Pareto front is the set of all value vectors of cuts.

*Proof.* The value f3 is linear in the edge weights, so f3 = −a f1 − b f2 for every cut. Then f3(z) ≥ f3(z′) gives a (f1(z) − f1(z′)) + b (f2(z) − f2(z′)) ≤ 0. Both terms are nonnegative, so both are zero, and a, b > 0 gives f1(z) = f1(z′) and f2(z) = f2(z′).

Brute force over all cuts, with the weights drawn as in [1]:

| Graph | n | Edges | Cuts (one side fixed) | Distinct value vectors | Pareto-optimal |
|---|---|---|---|---|---|
| random, edge probability 0.5 | 20 | 102 | 524 288 | 251 700 | all |
| complete | 20 | 190 | 524 288 | 231 555 | all |
| random, edge probability 0.5 | 12 to 16 (10 instances) | 33 to 71 | 2 048 to 32 768 | 2 021 to 29 754 | all |

This hints at a possible gap in the design of these instances as an optimization benchmark. Every cut is Pareto-optimal, and at n = 20 about half of all cuts have distinct value vectors, so the Pareto front grows with the number of distinct cut values. A %HV comparison on these instances then measures how much of the set of all value vectors a method covers. This fits the archives of about 3 · 10⁷ non-dominated points reported in [1] at n = 100 and 200 after bit-flip refinement, and the low Pareto recall at n = 20 of methods that return one maximizer per scalarization.

Instances with independently drawn weights, as in the 42-node benchmark of [2], do not have this property.

## Lean

`lean/NegCombination/Basic.lean`, with real weights on any type of edges and the cut edges of a cut given as a finite set:

- `eq_of_weak_dom`: on the plane y3 = −a y1 − b y2 with a, b > 0, weak dominance in all three coordinates forces equality.
- `sum_neg_comb`: the w3 value of an edge set is −a times its w1 value minus b times its w2 value.
- `no_domination`: if one edge set is at least as good as another in all three values, the two value vectors are equal.
- `no_domination_half_five`: the case a = 1/2, b = 5 of [1].

These use only the standard axioms (`lean/axioms.txt`). The weight generator of [1] is checked by `sim/degenerate_check.py`, which asserts that all distinct value vectors in the table are non-dominated.

## Files

- `sim/degenerate_check.py`: the brute-force check of the table.
- `lean/`: the Lean files. Build with `lake exe cache get` and then `lake build`; `lake env lean Axioms.lean` prints the axioms.

## References

1. J. Huang, C.-H. Huang, A. Velasquez, R. Wang, J. Liu, I. Alkhouri. Parallelizable gradient-based optimization for multi-objective MaxCut. arXiv:2608.25098.
2. A. Kotil, E. Pelofske, S. Riedmüller, D. J. Egger, S. Eidenbenz, T. Koch, S. Woerner. Quantum approximate multi-objective optimization. Nature Computational Science (2025). arXiv:2503.22797.
