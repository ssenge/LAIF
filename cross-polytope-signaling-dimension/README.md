# Signaling dimension of the cross-polytope in dimensions 6 and 7

Written 11 Nov 2026.

## Problem

The signaling dimension of a state space K is the least r such that every input-output correlation of K can be simulated by classical communication of r symbols with shared randomness. For the cross-polytope ⋄_d = {x ∈ R^d : |x₁| + ⋯ + |x_d| ≤ 1}, the values for d = 1, …, 5 are 2, 2, 3, 3, 3 [1, 2]. Reference [2] posed the general case. Reference [1] proves

⌈log₂(d + 2)⌉ ≤ sign. dim ⋄_d ≤ ⌊(d + 3)/2⌋  and  sign. dim ⋄_d ≤ max{4, ⌈log₂ d⌉} + 2 [1, Theorems 2.2 to 2.4],

so d = 6 and d = 7 were the first dimensions where the value was not known: 3 or 4 for d = 6, and 4 or 5 for d = 7.

## Result

**Theorem.** sign. dim ⋄₆ = 3 and sign. dim ⋄₇ = 4.

So the lower bound ⌈log₂(d + 2)⌉ of [1, Theorem 2.2] is the exact value for every d ≤ 7. The lower bounds are [1, Theorem 2.2]. The upper bounds are a finite computation, checked in exact rational arithmetic.

## Method

By [1, Section 2], a primitive measurement on ⋄_d is given by a function f : {−1, 1}^d → [0, 1] whose sum over every facet of the cube is 1 and whose support T is affinely independent. Equivalently, T is an affinely independent set of cube vertices with 0 in the relative interior of its convex hull, and f is twice the vector of barycentric weights of 0. By [1, Proposition 2.1] and [1, Remark 1.7], sign. dim ⋄_d ≤ r if and only if, for every such f, some probability distribution F on the r-subsets of T satisfies

Σ_{X ∩ S = ∅} F(X) ≤ 1 − f(S) for every S ⊆ T that lies in a facet of the cube. (†)

The group of the cube (coordinate permutations and sign changes, of order 2^d · d!) acts on these data, so one f per orbit suffices. The script:
1. Lists all affinely independent sets of vertices of {−1, 1}^d up to symmetry, adding one vertex at a time and keeping one canonical form per orbit. The canonical form is the least sorted image over a set of group elements chosen by invariants (a vertex of least distance profile is sent to (1, …, 1), then the coordinates are sorted by a coordinate invariant).
2. Keeps those with 0 in the relative interior of the convex hull. On the last level (d + 1 points) only such sets are kept, so this filter is applied before the canonical form is computed.
3. For each, computes f exactly in rationals and finds F by linear programming. It then rounds F to a rational vector with small denominator and verifies (†) exactly. If no rounding passes (16 cases for d = 7), it takes a vertex of the LP, solves its active constraints exactly in rationals, and verifies (†) for that solution. Supports with at most r points need no computation (F = {T}).

| d | r | primitive measurements up to symmetry | by support size 2, 4, 5, …, d + 1 | not r-simulable |
|---|---|---|---|---|
| 6 | 3 | 55 | 1, 3, 2, 12, 37 | 0 |
| 7 | 4 | 2168 | 1, 4, 3, 33, 179, 1948 | 0 |

(No primitive support has 3 points.)

With [1, Theorem 2.2] this gives the theorem.

Completeness of the list does not depend on the canonical form: every affinely independent set of k + 1 vertices contains one of k vertices, whose orbit representative is extended by every vertex. A weaker canonical form could only produce repeated orbits.

**Checks of the enumeration.**
- For d = 2, 3, 4, 5 the same code gives 2, 3, 3, 3 (r − 1 fails and r passes), as known.
- For d = 3, 4, 5 and 6, a brute force over all vertex sets containing a fixed vertex finds exactly as many primitive supports as the orbit list, counted with orbit sizes (75852 for d = 6). So for these d the list has neither gaps nor repeats. For d = 7 the brute force is too large; completeness there rests on the argument above.

## Check

`python sim/signdim.py d r [cores]` (numpy and scipy) prints the orbit counts, the LP results and the exact certificates: under a minute for d = 6, about 3 minutes for d = 7 on 10 cores. `python sim/signdim.py --brute d` runs the brute-force count (a few minutes on 8 cores for d = 6). The output of all runs is in `sim/out.txt`.

## References

1. T. Bencze, P. E. Frenkel. On the signaling dimension of the cross-polytope. arXiv:2610.05924 (2026).
2. S. Kai, M. Dall'Arno. The signaling dimension of two-dimensional and polytopic systems. Quantum Inf. Comput. 24 (2024), 932-944.
