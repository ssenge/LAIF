# Largest empty squares, rectangles and segments with quantum queries

Written 11 Nov 2026.

**Setting.** The input is a map f : {0, …, n − 1} × {0, …, n − 1} → {0, 1}, and a query returns one value f(i, j). A rectangle of d rows and h columns is a set [r, r + d) × [c, c + h) inside the grid. It is *empty* if f is 0 on all of its cells, and its area is its number of cells, as in the proof of Theorem 10 of [1]. The problems are those of [1]: the largest empty square (LSQR), the empty rectangle with d rows and the most columns, for a fixed d (LRECW), and the empty rectangle of largest area, with at least a given number of rows and columns (LREC).

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Is there an empty d × h rectangle? (any fixed d, h) | O(n √min(d, h) log n log log n), implied by [1] | O(n log² n), and Ω(n) for every d and h | Claim; checked by script; lemmas in Lean |
| Thm 2 | Largest empty square (LSQR) | O(n^{1.5} log n log log n), Ω(n) [1] | O(n log³ n), so Θ̃(n) | Claim; checked by script; lemmas in Lean |
| Thm 3 | Largest empty rectangle with d rows (LRECW) | O(n √d log n log log n), Ω(√(nd)) [1] | O(n log³ n) and Ω(n) for every d, so Θ̃(n) | Claim; checked by script; lemmas in Lean |
| Thm 4 | Largest empty rectangle by area (LREC) | Ω(n) quantum; no quantum speedup over the classical Θ(n²) known [1] | O(n log⁴ n), so Θ̃(n) | Claim; checked by script; lemmas in Lean |
| Thm 5 | Longest empty segment in a string of n bits (LSEG), longest run of identical characters (LSIC), longest increasing substring (LISST) | LSIC and LISST: O(√(n log n)) [6]; LSEG: O(√(n log n)), implied by [6], and O(√n log n log log n) [1]; Ω(√n) | O(√n log log n) | Claim; checked by script |

Classically, LSQR and LREC need Ω(n²) queries and LRECW needs Ω(nd) queries [1]. For d up to a polylogarithm in n, the bound of [1] for LRECW is already Õ(n). The algorithms also return an optimal rectangle.

## 1. Lattice cells and windows

**Lemma 1.** Every rectangle of d rows and h columns contains exactly one *lattice cell*, a cell (i, j) with i divisible by d and j divisible by h.

*Proof.* Among d consecutive integers exactly one is divisible by d, and the same holds for the columns. ∎

So there is an empty d × h rectangle iff, for some lattice cell (p, q), there is an empty one containing (p, q). These rectangles have top-left corner (p − a, q − b) with *offset* (a, b) in [0, d) × [0, h), and they lie in the *window* of cells (p + x, q + y) with |x| < d and |y| < h.

**Lemma 2.** A 1 at (p + x, q + y) in the window lies in the rectangle with offset (a, b) iff a ≤ d − 1 − x when x ≥ 0 and a ≥ −x when x < 0, and in the same way for b, y and h.

So each 1 of the window rules out a box of offsets at one corner of [0, d) × [0, h). The corner depends on the signs of x and y, and the box shrinks as |x| or |y| grows. Split the window into four quadrants by these signs. Within a quadrant, a 1 at distances (|x|, |y|) rules out a subset of what a 1 at smaller or equal distances in both coordinates rules out. So only the *front* of the quadrant matters: the 1-cells with no other 1-cell at smaller or equal distances in both coordinates. The window has an empty rectangle through (p, q) iff the boxes of the four fronts do not cover all offsets (a, b) whose rectangle fits in the grid. Once the fronts are known, this needs no further queries.

## 2. Learning a front

**Lemma 3.** The front of the 1-cells in a region of d′ rows and h′ columns can be learned with at most min(d′, h′)(⌈log₂ d′⌉ + 1) minimum findings, each erring with probability at most δ, using O(√(d′h′) log(d′ + 1) log(1/δ)) queries in total. These bounds hold on every run, also when a finding errs.

*Proof.* Split the rows into halves. Minimum finding [3] over the cells of the upper half returns a 1-cell of least column m, or reports that there is none. It is stopped after a constant times √(cells) queries, its answer is checked with one query, and O(log(1/δ)) repetitions keep the least checked column, so it errs with probability at most δ and uses O(√(cells) log(1/δ)) queries on every run. The front of the upper half is the front of the region in the upper rows, and it lies in the columns from m on. A 1-cell of the lower half is on the front iff its column is below m and it is on the front of the lower half restricted to these columns. So the algorithm recurses on the upper half with columns [m, h′) and on the lower half with columns [0, m), and stops on regions without a 1-cell or with one row.

At each depth the regions have at most d′ rows and h′ columns in total, since the column ranges of the two halves are disjoint. So the cost at one depth is at most a constant times log(1/δ) times Σ√(rᵢwᵢ) ≤ √(Σrᵢ · Σwᵢ) ≤ √(d′h′). There are ⌈log₂ d′⌉ + 1 depths. Whatever the findings return, the regions at one depth have disjoint row ranges and disjoint column ranges, so at most min(d′, h′) of them have at least one row and one column, and only these need a minimum finding. So the number of queries is bounded on every input, and with intermediate measurements deferred the learner can run coherently. ∎

## 3. The algorithms

**Theorem 1.** For any d and h, deciding whether f has an empty d × h rectangle, and finding one, takes O(n log² n) quantum queries.

*Proof.* The window test learns the four fronts of a window by Lemma 3 with δ = 1/(40 min(d, h)(⌈log₂ d⌉ + 1)), so with at most 4 min(d, h)(⌈log₂ d⌉ + 1) minimum findings and error at most 1/10, in O(√(dh) log² n) queries, and decides by Lemmas 1 and 2. A search over the at most ⌈n/d⌉⌈n/h⌉ ≤ 4n²/(dh) lattice cells with this bounded-error test [4] uses O(n/√(dh)) tests, so O(n log² n) queries. This is below the bound implied by [1] when min(d, h) is larger than about (log n / log log n)².

For the lower bound, take a = ⌊(n + 1)/(d + 1)⌋ by b = ⌊(n + 1)/(h + 1)⌋ blocks of d × h cells, with a row of ones after each block row, a column of ones after each block column, and ones in all remaining cells. Whatever the blocks contain, f has an empty d × h rectangle iff some block is all zero, since d consecutive rows and h consecutive columns that avoid the ones form a block. Since ad ≥ (n + 1)/4 and bh ≥ (n + 1)/4, this is OR over ab blocks of AND over dh values with ab · dh ≥ n²/16, which needs Ω(n) queries [5]. ∎

Theorems 2 to 4 search over classes of shapes. A *shape* is a pair (d, h) of a number of rows and a number of columns, and the class of (D, H), for powers of two D and H, holds the shapes with D ≤ d < 2D and H ≤ h < 2H.

**Lemma 4.** Let D and H be powers of two and S a set of shapes in the class of (D, H). With O(n log² n) quantum queries, an empty rectangle of largest area with shape in S can be found with probability at least 0.9 − O(1/n). Except with probability O(1/n), every rectangle the algorithm returns is empty.

*Proof.* A rectangle with shape in S has at least D rows and at least H columns, so by the argument of Lemma 1 it contains a lattice cell (p, q) of spacing (D, H), and it lies in the cells (p + x, q + y) with |x| < 2D and |y| < 2H. Lemma 2 holds for every number of rows and columns, so, as in Section 1, a 1-cell of a quadrant rules out every rectangle through (p, q) that a 1-cell at greater or equal distances in both coordinates rules out. So the four fronts of this window, at distances below 2D and 2H, determine which rectangles through (p, q) with shape in S are empty, and the largest of them follows with no further queries. Lemma 3 learns the fronts with O(min(D, H) log n) minimum findings at error δ = 1/n⁶ each, so with O(√(DH) log² n) queries and error at most 1/n⁴. The evaluation makes a fixed number of queries on every input, so it can be computed, copied and uncomputed coherently, and each such call moves the state by O(√(n⁻⁴)) = O(n⁻²) in norm. Maximum finding [3] over the at most 4n²/(DH) lattice cells with this evaluation uses O(n/√(DH)) evaluations, so O(n log² n) queries. With exact evaluations it succeeds with probability at least 0.9 after a constant number of repetitions that keep the largest result, and the errors of the O(n) calls change the final state by O(1/n) in norm, which changes the probabilities of all outcomes by O(1/n). The evaluation decides emptiness for every shape in S, so the same holds for any objective g(d, h) in place of the area. ∎

**Theorem 2.** The largest empty square can be found with O(n log³ n) quantum queries.

*Proof.* Run Lemma 4 for the O(log n) classes of (D, D) with the square shapes, and return the largest result. The run for the class of an optimal square succeeds with probability at least 0.9 − O(1/n), and except with probability O(log n / n) no run returns a rectangle that is not empty, so the result is optimal with probability at least 2/3 for large n. ∎

**Theorem 3.** For every d, the empty rectangle with d rows and the most columns can be found with O(n log³ n) quantum queries, and Ω(n) queries are needed.

*Proof.* For the upper bound, take the lattice with spacing (d, H) and the shapes (d, h) with H ≤ h < 2H. Lemma 4 and its proof hold with D replaced by d and the window rows restricted to |x| < d, and the O(log n) values of H give the bound as in Theorem 2. For the lower bound, take a = ⌊(n + 1)/(d + 1)⌋ blocks of d rows, with a row of ones after each block and ones in all remaining rows. Whatever the blocks contain, a rectangle with d rows and n columns is empty iff some block is all zero, since every d consecutive rows that avoid the rows of ones form a block. This is OR over a blocks of AND over dn values, which needs Ω(√(a · dn)) = Ω(n) queries [5]. ∎

**Theorem 4.** The empty rectangle of largest area, with at least w rows and at least h₀ columns, can be found with O(n log⁴ n) quantum queries. So LREC takes Θ̃(n) quantum queries.

*Proof.* Run Lemma 4 for the O(log² n) classes of (D, H), each with the shapes (d, h) of the class with d ≥ w and h ≥ h₀, and return the largest result, as in Theorem 2. The lower bound Ω(n) is from [1]. By the last sentence of Lemma 4, the same bound holds for the size (d − 1)(h − 1) of the formal definition in [1]. ∎

## 4. One dimension

In one dimension the input is f : {0, …, n − 1} → {0, 1}, and LSEG asks for a longest *empty segment*, a longest run of consecutive positions where f is 0 [1]. LSIC asks for a longest run of consecutive positions with the same character, for f with values in a finite alphabet, and LISST for a longest run of consecutive positions on which an integer array increases [6]. For LISST, the runs are the runs of ones of the bits [a_i < a_{i+1}], each of which costs two queries, plus one position. Write L for the length of a longest run, of zeros for LSEG and of any character for LSIC. The algorithm below works the same way for both.

The run through a position p is found by two searches for the first position to the right of p, and the last position to the left of p, whose value differs from the run. Restricted to a window of w positions on each side, these are minimum findings over w positions with O(√w) queries [3], stopped after a constant times √w queries so that they have a fixed length and a constant error.

**Lemma 5.** Let K ≥ 1.
1. There is a run of length at least K iff the run through some multiple p of K has length at least K. Whether the run through p has length at least K depends only on the positions within distance K − 1 of p.
2. If K ≤ L, then L is the largest length of a run through a multiple of K. If moreover L < 2K, the length of the run through any position p depends only on the positions within distance 2K of p.

*Proof.* K consecutive integers contain a multiple of K. The run through p has length at least K iff K consecutive positions containing p belong to it, and these lie within distance K − 1 of p. If every run is shorter than 2K, both ends of the run through p lie within distance 2K of p. ∎

**Theorem 5.** LSEG, LSIC and LISST can be solved with O(√n log log n) quantum queries, and the algorithms return a longest run.

*Proof.* For a power of two K, decide whether there is a run of length at least K by a search over the at most ⌈n/K⌉ multiples of K with the bounded-error test of Lemma 5.1, which costs O(√K) queries. Search with a bounded-error test [4] uses O(√(n/K)) tests, so O(√n) queries, with error at most 1/3. The answer is monotone in K, so a binary search over the ⌊log₂ n⌋ + 1 powers of two that tolerates errors [8] finds the power of two K with K ≤ L < 2K, or that L = 0, with O(log log n) such decisions and error at most 1/10, so with O(√n log log n) queries. Then compare two multiples p and q of K by the lengths of their runs within distance 2K, with O(√K) queries and error at most 1/4. Minimum finding with a bounded-error comparison oracle, which may leave garbage, uses O(√N) comparisons for N items [7], so a multiple of K with a longest run is found with O(√(n/K) · √K) = O(√n) queries. By Lemma 5.2 its run is a longest run. This succeeds with probability at least 1/2. Repeating the whole algorithm a constant number of times, finding the run through each returned position with O(√n) queries, and keeping the longest raises the success probability to 2/3. ∎

All three problems need Ω(√n) queries, since a string of n zeros and a string with a single 1 differ in L [1].

## Lean

`lean/EmptyRect/`, built against Mathlib, standard axioms only (`lean/axioms.txt`):

- `Window.lean`: Lemma 1 (`lattice_unique`), its form for the shape classes (`lattice_exists`), Lemma 2 (`mem_rect_iff`), that every 1-cell of a quadrant lies at greater or equal distances than a point of its front (`exists_front_le`), the split of a front used in Lemma 3 (`front_split`), and that d consecutive rows avoiding the rows of ones of the lower-bound grids form a block (`block_start`).
- `Cost.lean`: the cost at one depth in Lemma 3, Σ√(rᵢwᵢ) ≤ √(RW) when Σrᵢ ≤ R and Σwᵢ ≤ W (`level_cost`), ⌈n/d⌉ · d ≤ 2n (`ceil_mul_le`), and the cost of the outer search, √(AB) · √(dh) ≤ 2n when Ad ≤ 2n and Bh ≤ 2n (`outer_cost`).

**Not formalized:** minimum finding [3], search with a bounded-error test [4], the lower bound for composed functions [5], the decision of the window test from the four fronts, and the maximum searches of Lemma 4 and Theorems 2 to 4.

## Scripts

`sim/check_window.py` checks, against brute force:
- Lemma 1 for small d;
- the window test with the four fronts, on 1500 random grids of up to 14 × 14 cells, for random d and h;
- that the divide-and-conquer learner returns exactly the front, and that its cost at each depth is at most √(dh) per quadrant;
- the largest square by binary search, on 400 random grids;
- the lower-bound instances of Theorem 3, for all n ≤ 12, all d and all choices of zero blocks;
- the lower-bound instances of Theorem 1, for all n ≤ 10 and all d and h, with all choices of zero blocks when there are at most 10 blocks and 300 random choices otherwise, and random positions of the 1 in the other blocks.

`sim/check_area.py` checks that the largest value over all classes and lattice cells in Lemma 4, computed from the four fronts only, equals the largest empty rectangle found by brute force, on 1200 random grids of up to 13 × 13 cells, some with rows of ones, for random lower limits w and h₀ on the rows and columns, and that the front learner costs at most √(4DH) per depth and quadrant.

`sim/check_segment.py` checks Lemma 5 against brute force: the scale test and the largest window value over the multiples of K, for LSEG, LSIC and LISST, on 3000 random strings and arrays of each kind of up to 40 positions and on all binary strings of up to 14 positions.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the Lean files and the check scripts, and to draft the text.

## References

1. K. Khadiev et al. Quantum algorithm for searching for the longest segment and the largest empty rectangle. arXiv:2512.03788, 2025.
2. M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschr. Phys. 46, 1998. arXiv:quant-ph/9605034.
3. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014, 1996.
4. P. Høyer, M. Mosca, R. de Wolf. Quantum search on bounded-error inputs. ICALP 2003. arXiv:quant-ph/0304052.
5. B. W. Reichardt. Reflections for quantum query algorithms. SODA 2011. arXiv:1005.1601.
6. J. Allcock, J. Bao, A. Belovs, T. Lee, M. Santha. On the quantum time complexity of divide and conquer. ICALP 2025. arXiv:2311.16401.
7. Q. Wang, M. Ying. Quantum algorithm for lexicographically minimal string rotation. arXiv:2012.09376.
8. U. Feige, P. Raghavan, D. Peleg, E. Upfal. Computing with noisy information. SIAM J. Comput. 23(5), 1994.
