# Bandwidth in polynomial space with a quantum algorithm

Written 22 Nov 2026.

Input: a graph G on n vertices. Question: the bandwidth of G, the minimum over all orderings π: V → {1, …, n} of the maximum of |π(u) − π(v)| over the edges uv.

**Theorem 1.** Bandwidth has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, in time O(10^{n/2}) ⊆ O(3.1623^n).

Status: Claim. Assuming the bucket-assignment method of [1] as restated in [2, Section 4.1], and using quantum search [3] and reversible simulation [4] as stated. The reduction is checked against brute force and the exponent by an exact script.

## Before and after

| Model | Previous best bound | After |
|---|---|---|
| Classical, polynomial space | O(9.363^n) [5] | |
| Classical, any space | O*(20^{n/2}) = O(4.4721^n), with space O*(20^{n/2}) [6]; O(4.83^n) with space O*(4^n) [7] | |
| Quantum, polynomial space, no quantum random access memory | | **O(10^{n/2}) = O(3.1623^n)** |
| Quantum, exponential space with quantum random access memory | O*(2.946^n) [2, Theorem 6] | |

Theorem 1 is below every classical bound above, including those with exponential space.

## 1. The algorithm

**Bucket assignments** [1], as restated in [2, Section 4.1]. Fix b and split the positions 1, …, n into k = ⌈n/(b + 1)⌉ buckets of b + 1 consecutive positions. An ordering of bandwidth at most b puts the endpoints of every edge into the same or adjacent buckets. Fix a spanning tree with root r. A bucket assignment σ is given by the bucket of r and an offset in {−1, 0, +1} between each other vertex and its parent, so there are at most k · 3^{n−1} of them. For a fixed σ with the right bucket sizes and no edge across two or more buckets, the positions are filled in rounds, one position per bucket in each round, and an ordering of bandwidth at most b exists if and only if there is a sequence of balanced sets ∅ = S₀ ⊂ S₁ ⊂ … ⊂ S_n = V, each adding a vertex v of the bucket of the next position such that v has no neighbour in S in the previous bucket and all its neighbours in the next bucket are in S. A set S on such a sequence is valid for σ: if the parent p of v is in S and v lies one bucket above p, then v ∈ S, and if p ∉ S and v lies one bucket below p, then v ∉ S. Given whether its parent is in S, each vertex has 5 of the 6 combinations of offset and membership, so there are exactly 2k · 5^{n−1} pairs (σ, S) with S valid for σ [2, Section 4.1].

**Halving recursion.** A sequence from A to B exists if and only if there is a balanced set C with A ⊆ C ⊆ B and |C \ A| = ⌊|B \ A|/2⌋ such that sequences from A to C and from C to B exist.

**Nested search.** The top level searches the pairs (σ, S), with S valid for σ, by quantum search [3]. Their index is a choice of the root bucket, root membership and one of 5 combinations per vertex in the order of the tree, so it is computed in polynomial time. The search marks a pair if σ has the right bucket sizes and no edge across two buckets, S is balanced with |S| = ⌊n/2⌋, and sequences from ∅ to S and from S to V exist. The levels l = 1, …, D − 1 search the middle sets C of their interval among all subsets of B \ A of the right size, at most 2^{n/2^l} of them. At depth D the call decides the sequence classically by the same halving recursion, in time 4^m · m^{O(log m)} for an interval of m = n/2^D vertices and polynomial space, run reversibly [4] in time (4^m · m^{O(log m)})^{1+ε} and polynomial space. Each subcall is repeated in L = O(n) parallel copies with a majority vote, and its work is uncomputed, so the workspace of a call is at most 2L times that of a subcall plus poly(n), which is poly(n) over the constant depth D.

## 2. Analysis

The square roots of the search spaces multiply along a path of calls, and the two subcalls at each level and the copies contribute a factor (2L · O(n))^D = poly(n). The time is therefore

√(2k · 5^n) · ∏_{l=1}^{D−1} 2^{n/2^{l+1}} · 4^{(1+ε) n/2^D} · 2^{O(log² n)} = 10^{n/2} · 2^{(1+2ε) n/2^D} · 2^{O(log² n)},

since the exponents of the middle levels sum to n(1/2 − 1/2^D). With D = 17 and ε = 1/10, √10 · 2^{(1+2ε)/2^D} < 3.1623, so the time is O(3.1623^n), where the strict inequality absorbs the subexponential factors. As D grows the bound tends to 10^{n/2}. The binary search over b adds a factor O(log n). The space is polynomial.

## 3. Measurements

`sim/bandwidth.py`:
- implements the bucket-assignment reduction of Section 1 with the halving recursion and compares the bandwidth it finds with brute force over all orderings on 137 random connected graphs with 2 to 7 vertices;
- checks that each vertex has exactly 5 locally valid combinations;
- checks √10 · 2^{(1+2ε)/2^D} < 3.1623 for D = 17 and ε = 1/10 in exact rational arithmetic, with ln 2 < 0.6932 and 2^x ≤ 1/(1 − x ln 2).

Run it with `python bandwidth.py` in `sim/`. It exits nonzero on a failed check.

## 4. Limits

- The reduction of [1] is used as restated in [2]; the script checks it on small graphs only.
- The bound counts all 2k · 5^{n−1} valid pairs at the top level and all subsets of the right size below it, with no gate count.
- The polynomial factors and the constant 2^{O(D)} are not evaluated.

## References

1. M. Cygan, M. Pilipczuk. Faster exact bandwidth. WG 2008.
2. A. Ambainis, K. Balodis, J. Iraids, M. Kokainis, K. Prūsis, J. Vihrovs. Quantum speedups for exponential-time dynamic programming algorithms. arXiv:1807.05209.
3. L. K. Grover. A fast quantum mechanical algorithm for database search. STOC 1996.
4. C. H. Bennett. Time/space trade-offs for reversible computation. SIAM Journal on Computing 18(4), 1989.
5. M. Cygan, M. Pilipczuk. Bandwidth and distortion revisited. arXiv:1004.5012.
6. M. Cygan, M. Pilipczuk. Exact and approximate bandwidth. ICALP 2009.
7. M. Cygan, M. Pilipczuk. Even faster exact bandwidth. arXiv:0902.1661.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check the analysis, to write the simulation script, and to draft the text.
