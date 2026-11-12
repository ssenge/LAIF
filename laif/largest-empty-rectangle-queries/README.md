# Largest empty squares, rectangles and segments with quantum queries

Written 11 Nov 2026.

**Setting.** The input is a map f : {0, …, n − 1} × {0, …, n − 1} → {0, 1}, and a query returns one value f(i, j). A rectangle of d rows and h columns is a set [r, r + d) × [c, c + h) inside the grid. It is *empty* if f is 0 on all of its cells, and its area is its number of cells, as in the proof of Theorem 10 of [1]. The problems are those of [1]: the largest empty square (LSQR), the empty rectangle with d rows and the most columns, for a fixed d (LRECW), and the empty rectangle of largest area, with at least a given number of rows and columns (LREC).

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Is there an empty d × h rectangle? (any fixed d, h) | O(n √min(d, h) log n log log n), implied by [1] | O(n (1 + log min(d, h))), and Ω(n) for every d and h | Claim; checked by script; lemmas in Lean |
| Thm 2 | Largest empty square (LSQR) | O(n^{1.5} log n log log n), Ω(n) [1] | O(n log n), so Θ̃(n) | Claim; checked by script; lemmas in Lean |
| Thm 3 | Largest empty rectangle with d rows (LRECW) | O(n √d log n log log n), Ω(√(nd)) [1] | O(n (1 + log d)) and Ω(n) for every d, so Θ(n) for bounded d | Claim; checked by script; lemmas in Lean |
| Thm 4 | Largest empty rectangle by area (LREC) | Ω(n) quantum; no quantum speedup over the classical Θ(n²) known [1] | O(n log² n), so Θ̃(n) | Claim; checked by script; lemmas in Lean |
| Thm 5 | Longest empty segment in a string of n bits (LSEG), longest run of identical characters (LSIC), longest increasing substring (LISST) | LSIC and LISST: O(√(n log n)) [6]; LSEG: O(√(n log n)), implied by [6], and O(√n log n log log n) [1]; Ω(√n) | O(√n), so Θ(√n) | Claim; checked by script |

Classically, LSQR and LREC need Ω(n²) queries and LRECW needs Ω(nd) queries [1]. For d up to a polylogarithm in n, the bound of [1] for LRECW is already Õ(n). The algorithms also return an optimal rectangle.

## 1. Lattice cells and windows

**Lemma 1.** Every rectangle of d rows and h columns contains exactly one *lattice cell*, a cell (i, j) with i divisible by d and j divisible by h.

*Proof.* Among d consecutive integers exactly one is divisible by d, and the same holds for the columns. ∎

So there is an empty d × h rectangle iff, for some lattice cell (p, q), there is an empty one containing (p, q). These rectangles have top-left corner (p − a, q − b) with *offset* (a, b) in [0, d) × [0, h), and they lie in the *window* of cells (p + x, q + y) with |x| < d and |y| < h.

**Lemma 2.** A 1 at (p + x, q + y) in the window lies in the rectangle with offset (a, b) iff a ≤ d − 1 − x when x ≥ 0 and a ≥ −x when x < 0, and in the same way for b, y and h.

So each 1 of the window rules out a box of offsets at one corner of [0, d) × [0, h). The corner depends on the signs of x and y, and the box shrinks as |x| or |y| grows. Split the window into four quadrants by these signs. Within a quadrant, a 1 at distances (|x|, |y|) rules out a subset of what a 1 at smaller or equal distances in both coordinates rules out. So only the *front* of the quadrant matters: the 1-cells with no other 1-cell at smaller or equal distances in both coordinates. The window has an empty rectangle through (p, q) iff the boxes of the four fronts do not cover all offsets (a, b) whose rectangle fits in the grid. Once the fronts are known, this needs no further queries.

## 2. Learning a front

The filtered γ₂ program and its sequential and functional composition, used from Lemma 3′ on, are recalled in Section 4.

**Lemma 3.** The front of the 1-cells in a region of d′ rows and h′ columns can be learned with at most min(d′, h′)(⌈log₂ d′⌉ + 1) minimum findings, each erring with probability at most δ, using O(√(d′h′) log(d′ + 1) log(1/δ)) queries in total. These bounds hold on every run, also when a finding errs.

*Proof.* Split the rows into halves. Minimum finding [3] over the cells of the upper half returns a 1-cell of least column m, or reports that there is none. It is stopped after a constant times √(cells) queries, its answer is checked with one query, and O(log(1/δ)) repetitions keep the least checked column, so it errs with probability at most δ and uses O(√(cells) log(1/δ)) queries on every run. The front of the upper half is the front of the region in the upper rows, and it lies in the columns from m on. A 1-cell of the lower half is on the front iff its column is below m and it is on the front of the lower half restricted to these columns. So the algorithm recurses on the upper half with columns [m, h′) and on the lower half with columns [0, m), and stops on regions without a 1-cell or with one row.

At each depth the regions have at most d′ rows and h′ columns in total, since the column ranges of the two halves are disjoint. So the cost at one depth is at most a constant times log(1/δ) times Σ√(rᵢwᵢ) ≤ √(Σrᵢ · Σwᵢ) ≤ √(d′h′). There are ⌈log₂ d′⌉ + 1 depths. Whatever the findings return, the regions at one depth have disjoint row ranges and disjoint column ranges, so at most min(d′, h′) of them have at least one row and one column, and only these need a minimum finding. So the number of queries is bounded on every input, and with intermediate measurements deferred the learner can run coherently. ∎

**Lemma 3′.** Splitting the shorter side, the front of a region of d′ rows and h′ columns, as a function of the region, has a solution of the filtered γ₂ program (Section 4) with cost O(√(d′h′) (1 + log min(d′, h′))) at every input. So it is computed with that many queries and bounded error, and any function of the front, such as the window test of Section 1, has a solution of the same cost.

*Proof.* The learner of Lemma 3 runs the minimum findings one after the other, and which regions it searches depends only on the earlier answers. A minimum finding over c cells, as a function of the region, has bounded-error query complexity O(√c) [3], so it has a solution of cost O(√c) at every input. By the sequential composition of Section 4, the whole sequence has a solution whose cost at each input is the sum of the costs of the findings made on that input, which is O(√(d′h′)) per depth by the proof of Lemma 3, over 1 + ⌈log₂ min(d′, h′)⌉ depths. No error reduction is needed. This cost bound is the same at every input with d′ rows and h′ columns, so any function of the front, which is computed with the same queries, has a solution of cost O(√(d′h′) (1 + log min(d′, h′))) at every input by the adversary bound. ∎

## 3. The algorithms

**Theorem 1.** For any d and h, deciding whether f has an empty d × h rectangle, and finding one, takes O(n (1 + log min(d, h))) quantum queries.

*Proof.* By Lemma 3′, the window test of a lattice cell, which learns the four fronts of its window and decides by Lemmas 1 and 2, has a solution of cost c = O(√(dh) (1 + log min(d, h))) at every input. The answer is the OR of the window tests over the M ≤ 4n²/(dh) lattice cells, and the first lattice cell, in a fixed order, whose window has an empty rectangle is the find-first-one function of the tests. Both outer functions have solutions of largest cost O(√M) [10, Theorem 6], so by the functional composition of Section 4 the composed functions have solutions of cost O(√M · c) = O(n (1 + log min(d, h))), and so does the rectangle found in that window. This is below the bound implied by [1] for every d and h.

For the lower bound, take a = ⌊(n + 1)/(d + 1)⌋ by b = ⌊(n + 1)/(h + 1)⌋ blocks of d × h cells, with a row of ones after each block row, a column of ones after each block column, and ones in all remaining cells. Whatever the blocks contain, f has an empty d × h rectangle iff some block is all zero, since d consecutive rows and h consecutive columns that avoid the ones form a block. Since ad ≥ (n + 1)/4 and bh ≥ (n + 1)/4, this is OR over ab blocks of AND over dh values with ab · dh ≥ n²/16, which needs Ω(n) queries [5]. ∎

Theorems 2 to 4 search over classes of shapes. A *shape* is a pair (d, h) of a number of rows and a number of columns, and the class of (D, H), for powers of two D and H, holds the shapes with D ≤ d < 2D and H ≤ h < 2H.

**Lemma 4.** Let D and H be powers of two and S a set of shapes in the class of (D, H). An empty rectangle of largest area with shape in S, chosen by a fixed rule among the largest ones, can be found with O(n (1 + log min(D, H))) quantum queries and bounded error.

*Proof.* A rectangle with shape in S has at least D rows and at least H columns, so by the argument of Lemma 1 it contains a lattice cell (p, q) of spacing (D, H), and it lies in the cells (p + x, q + y) with |x| < 2D and |y| < 2H. Lemma 2 holds for every number of rows and columns, so, as in Section 1, a 1-cell of a quadrant rules out every rectangle through (p, q) that a 1-cell at greater or equal distances in both coordinates rules out. So the four fronts of this window, at distances below 2D and 2H, determine which rectangles through (p, q) with shape in S are empty, and the largest of them follows with no further queries. By Lemma 3′ this evaluation is computed with O(√(DH) (1 + log min(D, H))) queries and bounded error. Maximum finding with a bounded-error comparison [7, Lemma 3.4] over the at most 4n²/(DH) lattice cells, comparing the area and then the position, uses O(n/√(DH)) comparisons. Each comparison runs two evaluations, each amplified to error at most 1/6, so it is correct with probability at least 2/3. The evaluation decides emptiness for every shape in S, so the same holds for any objective g(d, h) in place of the area. ∎

**Theorem 2.** The largest empty square can be found with O(n log n) quantum queries.

*Proof.* Let L be the side of a largest empty square, and for D = 2^i ≤ n let E_i = 1 iff L ≥ D. By Lemma 1, E_i is the OR, over the lattice cells of spacing (D, D), of the window test of Theorem 1 for the D × D square, and each test has a solution of cost c_i = O(D (1 + log D)) by Lemma 3′. There are M_i ≤ 4n²/D² lattice cells. If L ≥ D, an empty L × L square contains at least ⌊L/D⌋² ≥ L²/(4D²) lattice cells, and each of them passes its test. With the OR solution of Section 4 and the functional composition, E_i has a solution of cost O(√M_i c_i) = O(n (1 + log n)) if L < D, and O(√M_i c_i · D²/L²) = O(n (1 + log D) D²/L²) if L ≥ D. The string (E_0, E_1, …) is 1^b 0^{…}, and by the boundary solution of Section 4, b has a solution of cost O(n log n + Σ_{D ≤ L} n (1 + log D) D²/L²) = O(n log n). If b = 0, there is no empty square and the output is none. Otherwise, run Lemma 4 for the class of (2^{b−1}, 2^{b−1}) with the square shapes. By the sequential composition of Section 4 the total cost is O(n log n). ∎

**Theorem 3.** For every d, the empty rectangle with d rows and the most columns can be found with O(n (1 + log d)) quantum queries, and Ω(n) queries are needed.

*Proof.* For the upper bound, let L be the largest number of columns of an empty rectangle with d rows, and for H = 2^i ≤ n let E_i = 1 iff L ≥ H. Take the lattice with spacing (d, H), with M_i ≤ 4n²/(dH) cells, and the window test of Theorem 1 for the d × H rectangle, with cost c_i = O(√(dH) (1 + log d)). An empty rectangle with d rows and L ≥ H columns contains a lattice row and at least ⌊L/H⌋ ≥ L/(2H) lattice cells of it, and each of them passes its test. As in Theorem 2, E_i has a solution of cost O(n (1 + log d)) if L < H and O(n (1 + log d) H/L) if L ≥ H, so b has a solution of cost O(n (1 + log d)), since the terms for H ≤ L sum to O(n (1 + log d)). If b = 0, there is no empty rectangle with d rows and the output is none. Otherwise, Lemma 4 with D replaced by d (its proof does not use that D is a power of two), the window rows restricted to |x| < d and the shapes (d, h) with 2^{b−1} ≤ h < 2^b finds the rectangle, with O(n (1 + log d)) queries. For the lower bound, take a = ⌊(n + 1)/(d + 1)⌋ blocks of d rows, with a row of ones after each block and ones in all remaining rows. Whatever the blocks contain, a rectangle with d rows and n columns is empty iff some block is all zero, since every d consecutive rows that avoid the rows of ones form a block. This is OR over a blocks of AND over dn values, which needs Ω(√(a · dn)) = Ω(n) queries [5]. ∎

**Theorem 4.** The empty rectangle of largest area, with at least w rows and at least h₀ columns, can be found with O(n log² n) quantum queries. So LREC takes Θ̃(n) quantum queries.

*Proof.* Maximum finding with a bounded-error comparison [7, Lemma 3.4] over the O(log² n) classes of (D, H), each evaluated by Lemma 4 with the shapes (d, h) of the class with d ≥ w and h ≥ h₀, uses O(log n) evaluations of O(n log n) queries each. The lower bound Ω(n) is from [1]. By the last sentence of Lemma 4, the same bound holds for the size (d − 1)(h − 1) of the formal definition in [1]. ∎

## 4. One dimension

In one dimension the input is f : {0, …, n − 1} → {0, 1}, and LSEG asks for a longest *empty segment*, a longest run of consecutive positions where f is 0 [1]. LSIC asks for a longest run of consecutive positions with the same character, for f with values in a finite alphabet, and LISST for a longest run of consecutive positions on which an integer array increases [6]. For LISST, the runs are the runs of ones of the bits [a_i < a_{i+1}], each of which costs two queries, plus one position. Write L for the length of a longest run, of zeros for LSEG and of any character for LSIC. The algorithm below works the same way for both.

The run through a position p is found by two searches for the first position to the right of p, and the last position to the left of p, whose value differs from the run. Restricted to a window of w positions on each side, these are minimum findings over w positions with O(√w) queries [3], stopped after a constant times √w queries so that they have a fixed length and a constant error.

**Lemma 5.** Let K ≥ 1.
1. There is a run of length at least K iff the run through some multiple p of K has length at least K. Whether the run through p has length at least K depends only on the positions within distance K − 1 of p.
2. If K ≤ L, then L is the largest length of a run through a multiple of K. If moreover L < 2K, the length of the run through any position p depends only on the positions within distance 2K of p.

*Proof.* K consecutive integers contain a multiple of K. The run through p has length at least K iff K consecutive positions containing p belong to it, and these lie within distance K − 1 of p. If every run is shorter than 2K, both ends of the run through p lie within distance 2K of p. ∎

**Theorem 5.** LSEG, LSIC and LISST can be solved with O(√n) quantum queries, and the algorithms return a longest run. So all three take Θ(√n) queries.

The proof works with the dual of the general adversary bound, in the form of the filtered γ₂ program [9, 10]. For a function g on a set D of inputs, a *solution* is a family of vectors u_{x,j}, v_{x,j}, for x ∈ D and positions j, with

Σ_{j : x_j ≠ y_j} ⟨u_{x,j}, v_{y,j}⟩ = [g(x) ≠ g(y)] for all x, y ∈ D,

and its *cost* at x is c(x) = max(Σ_j ‖u_{x,j}‖², Σ_j ‖v_{x,j}‖²). The bounded-error query complexity of g is, up to a constant factor, the least value of max_x c(x) over all solutions [9, 11]. This holds for inputs over any finite set of values and on any domain D, with constants that do not depend on them, and the composition statements below do not use the set of values either. Solutions compose with the costs kept per input:

1. *Sequential* [10, Theorems 4 and 5]. If g has a solution with costs c, and for each value e of g the function h restricted to the inputs with g(x) = e has a solution with costs c_e, then x ↦ (g(x), h(x)) has a solution with costs at most c(x) + c_{g(x)}(x).
2. *Functional.* Let g_1, …, g_M be Boolean functions on D with solutions u^i, v^i of costs c_i, and let f be a function on a set Z that contains every z(x) = (g_1(x), …, g_M(x)), with a solution a_{z,i}, b_{z,i}. Then u_{x,j} = ⊕_i a_{z(x),i} ⊗ u^i_{x,j}, and v_{x,j} in the same way from b and v^i, is a solution for x ↦ f(z(x)) with cost at most max(Σ_i ‖a_{z(x),i}‖² c_i(x), Σ_i ‖b_{z(x),i}‖² c_i(x)) at x. Indeed, Σ_{j : x_j ≠ y_j} ⟨u_{x,j}, v_{y,j}⟩ = Σ_i ⟨a_{z(x),i}, b_{z(y),i}⟩ [g_i(x) ≠ g_i(y)], which is the constraint of f at z(x) and z(y). The g_i may read overlapping parts of the input. This is the composition argument of [9], with the cost kept for each input.

Two scalar solutions with a = b serve as outer functions.
- *OR of M bits.* a_{0,i} = M^{−1/4}, and for z with t ≥ 1 ones, a_{z,i} = M^{1/4}/t on the ones of z and 0 elsewhere. The cost is √M at z = 0 and √M/t at z with t ones. Two nonzero strings differ only at positions where one of them has value 0.
- *Boundary of a monotone string.* On the strings z = 1^b 0^{m+1−b}, with b from 0 to m + 1, the function z ↦ b has the solution a_{z,i} = 1 for i ≤ b and 0 for i > b. Two such strings with b < b′ differ at the positions b, …, b′ − 1, and only position b has nonzero values in both. With costs c_i for the bits, the cost of the composition is c_b + Σ_{i<b} c_i, with c_{m+1} = 0.

*Proof of Theorem 5.* Let m = ⌊log₂ n⌋, K_i = 2^i and M_i = ⌈n/K_i⌉. For a multiple p of K_i, let T_{i,p} be 1 iff the run through p has length at least K_i. By Lemma 5.1 it depends on the positions within distance K_i − 1 of p, so two minimum findings compute it with O(√K_i) queries [3], and it has a solution with cost O(√K_i) at every input [9]. Let D_i be the OR of the T_{i,p} over the M_i multiples p; by Lemma 5.1, D_i = 1 iff L ≥ K_i. By the functional composition with the OR solution, D_i has a solution with cost c_i = O(√(M_i K_i)) = O(√n) if L < K_i. If L ≥ K_i, a longest run contains at least ⌊L/K_i⌋ ≥ L/(2K_i) multiples of K_i, all with T_{i,p} = 1, so c_i = O(√n K_i/L).

The string (D_0, …, D_m) is 1^b 0^{m+1−b}, where b is the number of i with K_i ≤ L. By the functional composition with the boundary solution, x ↦ b has a solution with cost O(√n + Σ_{i<b} √n K_i/L) = O(√n), since Σ_{i<b} K_i < 2^b ≤ 2L.

If b = 0, then L = 0. Otherwise K = 2^{b−1} satisfies K ≤ L < 2K, and by Lemma 5.2 L is the largest length of a run through a multiple of K, which depends only on the positions within distance 2K of the multiple. Let p be the leftmost multiple of K at which this largest length is attained. Minimum finding with a bounded-error comparison [7, Lemma 3.4] over the ⌈n/K⌉ multiples, with comparisons in O(√K) queries, followed by two minimum findings for the ends of the run through p, computes p and its run with O(√n) queries on the inputs with this value of b. So for each value of b this has a solution with cost O(√n) [9], and by the sequential composition, x ↦ (b, p, run through p) has a solution with cost O(√n) at every input. By [9], it is computed with O(√n) queries and bounded error. For LSIC the same proof applies to the runs of identical characters, over any finite alphabet. For LISST it applies to the runs of ones of the bits [a_i < a_{i+1}], with the length of a run plus one, over any finite set of integers. ∎

All three problems need Ω(√n) queries, since a string of n zeros and a string with a single 1 differ in L [1].

## Lean

`lean/EmptyRect/`, built against Mathlib, standard axioms only (`lean/axioms.txt`):

- `Window.lean`: Lemma 1 (`lattice_unique`), its form for the shape classes (`lattice_exists`), Lemma 2 (`mem_rect_iff`), that every 1-cell of a quadrant lies at greater or equal distances than a point of its front (`exists_front_le`), the split of a front used in Lemma 3 (`front_split`), and that d consecutive rows avoiding the rows of ones of the lower-bound grids form a block (`block_start`).
- `Decide.lean`: the window test from the four fronts. The rectangle with offset (a, b) contains no 1-cell of the window iff no front point of the four quadrants lies in it (`empty_iff_fronts`, and `rect_empty_iff_fronts` for the window of a grid), since a cell of a quadrant at smaller or equal distances than a cell of the rectangle lies in it too (`inRect_of_le`).
- `Cost.lean`: the cost at one depth in Lemma 3, Σ√(rᵢwᵢ) ≤ √(RW) when Σrᵢ ≤ R and Σwᵢ ≤ W (`level_cost`), ⌈n/d⌉ · d ≤ 2n (`ceil_mul_le`), and the cost of the outer search, √(AB) · √(dh) ≤ 2n when Ad ≤ 2n and Bh ≤ 2n (`outer_cost`).

**Not formalized:** minimum finding [3], search with a bounded-error test [4], the lower bound for composed functions [5], and the maximum searches of Lemma 4 and Theorems 2 to 4.

## Scripts

`sim/check_window.py` checks, against brute force:
- Lemma 1 for small d;
- the window test with the four fronts, on 1500 random grids of up to 14 × 14 cells, for random d and h;
- that the divide-and-conquer learner returns exactly the front, and that its cost at each depth is at most √(dh) per quadrant;
- the largest square by binary search, on 400 random grids;
- the lower-bound instances of Theorem 3, for all n ≤ 12, all d and all choices of zero blocks;
- the lower-bound instances of Theorem 1, for all n ≤ 10 and all d and h, with all choices of zero blocks when there are at most 10 blocks and 300 random choices otherwise, and random positions of the 1 in the other blocks.

`sim/check_area.py` checks that the largest value over all classes and lattice cells in Lemma 4, computed from the four fronts only, equals the largest empty rectangle found by brute force, on 1200 random grids of up to 13 × 13 cells, some with rows of ones, for random lower limits w and h₀ on the rows and columns, and that the front learner costs at most √(4DH) per depth and quadrant.

`sim/check_dual.py` checks the two outer solutions of Theorem 5 against their constraints on all strings of up to 7 bits, the functional composition with overlapping ORs as inner functions on all inputs of up to 6 bits, and the cost of the search for b, at most 5√(2n), on all strings of up to 14 bits and on 3000 random strings of up to 3000 bits.

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
9. T. Lee, R. Mittal, B. W. Reichardt, R. Špalek, M. Szegedy. Quantum query complexity of state conversion. FOCS 2011. arXiv:1011.3020.
10. R. Kothari. An optimal quantum algorithm for the oracle identification problem. STACS 2014. arXiv:1311.7685.
11. P. Høyer, T. Lee, R. Špalek. Negative weights make adversaries stronger. STOC 2007. arXiv:quant-ph/0611054.
