# Largest empty squares and rectangles with quantum queries

Written 11 Nov 2026.

**Setting.** The input is a map f : {0, …, n − 1} × {0, …, n − 1} → {0, 1}, and a query returns one value f(i, j). A rectangle of d rows and h columns is a set [r, r + d) × [c, c + h) inside the grid. It is *empty* if f is 0 on all of its cells, and its area is its number of cells, as in the proof of Theorem 10 of [1]. The problems are those of [1]: the largest empty square (LSQR), the empty rectangle with d rows and the most columns, for a fixed d (LRECW), and the empty rectangle of largest area, with at least a given number of rows and columns (LREC).

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Is there an empty d × h rectangle? (any fixed d, h) | O(n √min(d, h) log n log log n), implied by [1] | O(n log² n), and Ω(n) for every d and h | Claim; checked by script |
| Thm 2 | Largest empty square (LSQR) | O(n^{1.5} log n log log n), Ω(n) [1] | O(n log³ n log log n), so Θ̃(n) | Claim; checked by script |
| Thm 3 | Largest empty rectangle with d rows (LRECW) | O(n √d log n log log n), Ω(√(nd)) [1] | O(n log³ n log log n) and Ω(n) for every d, so Θ̃(n) | Claim; checked by script |
| Thm 4 | Largest empty rectangle by area (LREC) | Ω(n) quantum; no quantum speedup over the classical Θ(n²) known [1] | O(n^{1.5} log⁴ n) | Claim |

Classically, LSQR and LREC need Ω(n²) queries and LRECW needs Ω(nd) queries [1]. For d up to a polylogarithm in n, the bound of [1] for LRECW is already Õ(n). The algorithms also return an optimal rectangle.

## 1. Lattice cells and windows

**Lemma 1.** Every rectangle of d rows and h columns contains exactly one *lattice cell*, a cell (i, j) with i divisible by d and j divisible by h.

*Proof.* Among d consecutive integers exactly one is divisible by d, and the same holds for the columns. ∎

So there is an empty d × h rectangle iff, for some lattice cell (p, q), there is an empty one containing (p, q). These rectangles have top-left corner (p − a, q − b) with *offset* (a, b) in [0, d) × [0, h), and they lie in the *window* of cells (p + x, q + y) with |x| < d and |y| < h.

**Lemma 2.** A 1 at (p + x, q + y) in the window lies in the rectangle with offset (a, b) iff a ≤ d − 1 − x when x ≥ 0 and a ≥ −x when x < 0, and in the same way for b, y and h.

So each 1 of the window rules out a box of offsets at one corner of [0, d) × [0, h). The corner depends on the signs of x and y, and the box shrinks as |x| or |y| grows. Split the window into four quadrants by these signs. Within a quadrant, a 1 at distances (|x|, |y|) rules out a subset of what a 1 at smaller or equal distances in both coordinates rules out. So only the *front* of the quadrant matters: the 1-cells with no other 1-cell at smaller or equal distances in both coordinates. The window has an empty rectangle through (p, q) iff the boxes of the four fronts do not cover all offsets (a, b) whose rectangle fits in the grid. Once the fronts are known, this needs no further queries.

## 2. Learning a front

**Lemma 3.** The front of the 1-cells in a region of d′ rows and h′ columns can be learned with at most 2 min(d′, h′)(⌈log₂ d′⌉ + 1) + 1 minimum findings, each erring with probability at most δ, using O(√(d′h′) log(d′ + 1) log(1/δ)) queries in total.

*Proof.* Split the rows into halves. Minimum finding [3] over the cells of the upper half returns a 1-cell of least column m, or reports that there is none, with O(√(cells)) queries. The front of the upper half is the front of the region in the upper rows, and it lies in the columns from m on. A 1-cell of the lower half is on the front iff its column is below m and it is on the front of the lower half restricted to these columns. So the algorithm recurses on the upper half with columns [m, h′) and on the lower half with columns [0, m), and stops on regions without a 1-cell or with one row.

At each depth the regions have at most d′ rows and h′ columns in total, since the column ranges of the two halves are disjoint. So the cost at one depth is at most a constant times log(1/δ) times Σ√(rᵢwᵢ) ≤ √(Σrᵢ · Σwᵢ) ≤ √(d′h′). There are ⌈log₂ d′⌉ + 1 depths. Each region with a 1-cell contains a point of the front, and the regions at one depth have disjoint rows and disjoint columns, so at most min(d′, h′) of them contain a 1-cell. Only these regions have children, so each depth has at most 2 min(d′, h′) regions. ∎

## 3. The algorithms

**Theorem 1.** For any d and h, deciding whether f has an empty d × h rectangle, and finding one, takes O(n log² n) quantum queries.

*Proof.* The window test learns the four fronts of a window by Lemma 3 with δ = 1/(120 min(d, h)(⌈log₂ d⌉ + 1)), so with at most 12 min(d, h)(⌈log₂ d⌉ + 1) minimum findings and error at most 1/10, in O(√(dh) log² n) queries, and decides by Lemmas 1 and 2. A search over the at most ⌈n/d⌉⌈n/h⌉ ≤ 4n²/(dh) lattice cells with this bounded-error test [4] uses O(n/√(dh)) tests, so O(n log² n) queries.

For the lower bound, take a = ⌊(n + 1)/(d + 1)⌋ by b = ⌊(n + 1)/(h + 1)⌋ blocks of d × h cells, with a row of ones after each block row, a column of ones after each block column, and ones in all remaining cells. If each block is either all zero or not, then f has an empty d × h rectangle iff some block is all zero, since d consecutive rows and h consecutive columns that avoid the ones form a block. Since ad ≥ (n + 1)/4 and bh ≥ (n + 1)/4, this is OR over ab blocks of AND over dh values with ab · dh ≥ n²/16, which needs Ω(n) queries [5]. ∎

**Theorem 2.** The largest empty square can be found with O(n log³ n log log n) quantum queries.

*Proof.* An empty k × k square contains an empty (k − 1) × (k − 1) square, so binary search on k with Theorem 1 applies. Each of its O(log n) steps runs Theorem 1 with error O(1/log n), at a factor O(log log n). ∎

**Theorem 3.** For every d, the empty rectangle with d rows and the most columns can be found with O(n log³ n log log n) quantum queries, and Ω(n) queries are needed.

*Proof.* The upper bound is binary search on the number of columns, as in Theorem 2. For the lower bound, take a = ⌊(n + 1)/(d + 1)⌋ blocks of d rows, with a row of ones after each block and ones in all remaining rows. If each block is either all zero or not, then a rectangle with d rows and n columns is empty iff some block is all zero, since every d consecutive rows that avoid the rows of ones form a block. This is OR over a blocks of AND over dn values, which needs Ω(√(a · dn)) = Ω(n) queries [5]. ∎

**Theorem 4.** The empty rectangle of largest area, with at least w rows and at least h₀ columns, can be found with O(n^{1.5} log⁴ n) quantum queries.

*Proof.* For each number of rows d ≥ w, binary search with Theorem 1 gives the most columns H(d) in O(n log⁴ n) queries with error at most 1/n², repeating each step O(log n) times. Maximum finding [3] over the values d · H(d), for the d with H(d) ≥ h₀, uses O(√n) evaluations. ∎

## Scripts

`sim/check_window.py` checks, against brute force:
- Lemma 1 for small d;
- the window test with the four fronts, on 1500 random grids of up to 14 × 14 cells, for random d and h;
- that the divide-and-conquer learner returns exactly the front, and that its cost at each depth is at most √(dh) per quadrant;
- the largest square by binary search, on 400 random grids;
- the lower-bound instances of Theorem 3, for all n ≤ 12, all d and all choices of zero blocks;
- the lower-bound instances of Theorem 1, for all n ≤ 10 and all d and h, with all choices of zero blocks when there are at most 10 blocks and 300 random choices otherwise, and random positions of the 1 in the other blocks.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check script, and to draft the text.

## References

1. K. Khadiev et al. Quantum algorithm for searching for the longest segment and the largest empty rectangle. arXiv:2512.03788, 2025.
2. M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschr. Phys. 46, 1998. arXiv:quant-ph/9605034.
3. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014, 1996.
4. P. Høyer, M. Mosca, R. de Wolf. Quantum search on bounded-error inputs. ICALP 2003. arXiv:quant-ph/0304052.
5. B. W. Reichardt. Reflections for quantum query algorithms. SODA 2011. arXiv:1005.1601.
