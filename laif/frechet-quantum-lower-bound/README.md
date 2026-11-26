# A conditional quantum time lower bound n^{1.5−o(1)} for the discrete Fréchet distance

Written 26 Nov 2026.

The discrete Fréchet distance of two sequences of n points is computed by a standard dynamic program in time O(n²) [4]. Classically, no algorithm in time O(n^{2−ε}) exists unless the Strong Exponential Time Hypothesis fails [3]. Quantumly, no algorithm faster than quadratic is known, and the only conditional lower bound we know of is linear: it follows from the hardness of Orthogonal Vectors under the quantum version of that hypothesis [1, Section 3.1].

Here the discrete Fréchet distance is shown to need quantum time n^{1.5−o(1)}, under the depth-2 Quantum Strong Exponential Time Hypothesis of [1] and a compression-obliviousness assumption for grid reachability. The bound applies to points in dimension polylog n.

## Result

For a Boolean K × K matrix M, let REACH(M) = 1 if there is a sequence of cells from (1, 1) to (K, K) whose entries are all 1, where each step goes from (i, j) to (i+1, j), (i, j+1) or (i+1, j+1). For a truth table t of length 2^n with n even, write M_t(a, b) = t(a, b) for a, b ∈ {0, 1}^{n/2}, in lexicographic order. REACH is then a property of truth tables in the sense of [1, Section 2.2].

**Hypotheses.**
- (Q) DEPTH2-QSETH, i.e. [1, Conjecture 3] for the class DEPTH2 of polynomial-size depth-2 circuits with unbounded fan-in AND and OR gates.
- (H) REACH is DEPTH2-compression oblivious in the sense of [1, Section 2.2].

**Theorem 1.** Assume (Q) and (H). Then there is a constant c such that, for every ε > 0, no bounded-error quantum algorithm decides in time O(n^{1.5−ε}) whether two sequences of n points in {0, 1}^d have discrete Fréchet distance at most a given δ. Here d ≤ log^c n, and the metric is the Hamming metric; on {0, 1}^d it is the same as L₁, and as squared Euclidean distance with threshold √δ.

Status: conditional on (Q) and (H). The two lemmas below are proved here and checked by scripts.

## Before and after

| Problem | Previous best bound (quantum time, conditional) | This work |
|---|---|---|
| Discrete Fréchet distance, n points, dimension polylog n | n^{1−o(1)}, implied by [1, Section 3.1] with the reduction of [3]; upper bound O(n²) [4] | n^{1.5−o(1)} under (Q) and (H) |

## Proof

**Lemma 2 (query complexity of REACH).** For every ε > 0, the bounded-error quantum query complexity of REACH on K × K matrices is Ω(K^{1.5−ε}).

*Proof.* In [2, Corollary 1], connectivity from (0, 0) to (k, k) in a subgraph of the directed k × k grid needs Ω(k^{1.5−ε}) quantum queries to the edges, with edges (x, y) → (x+1, y) and (x, y) → (x, y+1). Map vertex (x, y) to cell (3x, 3y), which is always 1. Map the edge (x, y) → (x+1, y) to the cells (3x+1, 3y) and (3x+2, 3y), and the edge (x, y) → (x, y+1) to (3x, 3y+1) and (3x, 3y+2). Both cells of an edge are 1 iff the edge is present, and every other cell is 0.

The cells equal to 1 lie on the lines x ≡ 0 or y ≡ 0 (mod 3). So a diagonal step between two such cells passes a vertex cell, and the vertex cell is always 1. Monotone reachability with diagonal steps on the (3k+1) × (3k+1) matrix therefore equals reachability in the grid graph. Each cell is a function of at most one edge variable, so an algorithm for REACH gives an algorithm for grid connectivity with the same number of queries. ∎

**Lemma 3 (reduction).** Let C be a depth-2 circuit with m gates at the bottom level and n variables, split as x = (a, b). There are vectors p_a, q_b ∈ {0, 1}^{3m} and a threshold δ such that hamming(p_a, q_b) ≤ δ iff C(a, b) = 1. They can be computed in time O(mn) each.

*Proof.* For a DNF, let α_t(a) = 1 if a satisfies the literals of term t on the first half, and β_t(b) the same on the second half. Then C(a, b) = 1 iff the inner product ⟨α(a), β(b)⟩ is at least 1.

Pad both vectors to weight m, using a separate block of m coordinates for each side: p_a = (α(a), π(a), 0^m) and q_b = (β(b), 0^m, π(b)). Then hamming(p_a, q_b) = 2m − 2⟨α(a), β(b)⟩, so δ = 2m − 2 works.

For a CNF, let u_c(a) = 1 if a falsifies the literals of clause c on the first half, and v_c(b) the same on the second half. Then C(a, b) = 1 iff ⟨u(a), v(b)⟩ = 0. Pad as before, and replace q_b by its complement. Then hamming(p_a, q_b) = 3m − 2m + 2⟨u(a), v(b)⟩, so δ = m works. ∎

**Proof of Theorem 1.** The discrete Fréchet distance of P and Q is at most δ iff the matrix [d(P_i, Q_j) ≤ δ] has a path of the kind in the definition of REACH [4]. Given a depth-2 circuit C on n variables, let K = 2^{n/2}. Lemma 3 produces two sequences of K points in dimension 3m = poly(n) = polylog K, in time O(K · poly(n)), whose Fréchet decision equals REACH(M_tt(C)).

A quantum Fréchet algorithm in time O(K^{1.5−ε}) would thus decide REACH in the white-box setting of [1] in time O(K^{1.5−ε} + K poly(n)). By (Q), which applies to REACH by (H), white-box time is Ω(Q(REACH)), and by Lemma 2 that is Ω(K^{1.5−ε/2}), a contradiction. ∎

## Scripts

- `sim/scale_check.py` compares grid connectivity with REACH on the scaled matrix. It covers every instance of size 1 × 1, 2 × 1 and 2 × 2, and 3000 random grids up to 9 × 9.
- `sim/frechet_reduction_check.py` builds the points of Lemma 3 for 4000 random CNFs and DNFs on up to 8 variables. It asserts the pointwise identity, and that the Fréchet decision by dynamic programming equals REACH of the truth-table matrix.

## Limits

- The points lie in dimension polylog n. The classical lower bound of [3] holds already in the plane.
- (Q) concerns depth-2 circuits. By [1, Fact 2] it implies the NC version used in [1] for edit distance, so it is the stronger assumption of the two.
- (H) is an assumption on REACH of the same kind as the compression-obliviousness assumption for edit distance in [1, Section 4.3].
- The bound does not exclude a quantum algorithm in time o(n²).
- Not formalized: Lemmas 2 and 3 and the theorem. The scripts check small instances only.

## References

1. H. Buhrman, S. Patro, F. Speelman. A framework of quantum strong exponential-time hypotheses. STACS 2021, arXiv:1911.05686.
2. A. Ambainis, K. Balodis, J. Iraids, K. Khadiev, V. Kļevickis, K. Prūsis, Y. Shen, J. Smotrovs, J. Vihrovs. Quantum lower and upper bounds for 2D-grid and Dyck language. MFCS 2020, arXiv:2007.03402.
3. K. Bringmann. Why walking the dog takes time: Fréchet distance has no strongly subquadratic algorithms unless SETH fails. FOCS 2014, arXiv:1404.1448.
4. T. Eiter, H. Mannila. Computing discrete Fréchet distance. Technical report, TU Wien, 1994.

## Use of AI

The reduction, the analysis, the scripts and this text were produced with the help of Claude Opus 5.5.
