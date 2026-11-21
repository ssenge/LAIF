# Volume of origin-centred ellipsoids from membership queries

Written 22 Nov 2026.

**Setting.** A convex body K ⊂ ℝ^d is given by a quantum membership oracle, which answers exactly, also on the boundary, at any finite coordinate precision, and counts one query per call, as in [1, Section 2.4]. The task is to estimate vol(K) within relative error ε with probability at least 2/3. Here K = {x : xᵀAx ≤ 1} is an ellipsoid centred at the origin, with A symmetric and positive definite and unknown, and with known radii 0 < r ≤ R such that B(0, r) ⊆ K ⊆ B(0, R).

| | Previous best bound | This folder | Status |
|---|---|---|---|
| Upper | O(d² log(dR/(rε))) by learning A with classical bisection along the d(d + 1)/2 directions e_i and e_i + e_j; O(d^{5/2} + d^{3/2}/ε) up to log factors for all convex bodies [1, Thm 1.1] | O(d log d · log(dR/(rε))), and the matrix A within entrywise error ε/(4d²R²) | Claim; checked by script |
| Lower | Ω(d) for ε = 1/4, already for origin-centred ellipsoids with B(0, 1/2) ⊆ K ⊆ B(0, Cd²) [1, Thm 7.3] | | |

On the class of [1, Thm 7.3] the bound is O(d log d · log(d/ε)), so for constant ε the query complexity of that class is Θ(d) up to a factor log² d, and the dependence on ε is logarithmic there. The algorithm is the quantum gradient algorithm of [2], applied column by column to a difference of the squared gauge of K that is exactly linear, with each value computed by bisection along a ray.

## Theorem 1

**Theorem 1.** There is a quantum algorithm that, for an ellipsoid K = {x : xᵀAx ≤ 1} with B(0, r) ⊆ K ⊆ B(0, R), outputs a symmetric matrix Â with |Â_{ik} − A_{ik}| ≤ ε/(4d²R²) for all i, k and an estimate of vol(K) within relative error ε, with probability at least 2/3, using O(d log d · log(dR/(rε))) membership queries.

**Notation.** Let Λ = 1/r². The eigenvalues of A lie in [1/R², Λ], so |A_{ik}| ≤ Λ. Let f(y) = yᵀAy. Let N be the smallest power of 2 with N ≥ 16 d² (R/r)²/ε, and let s be the smallest integer with 2^s ≥ 200 N² d R/r.

**Bisection.** For y ≠ 0 the ray {t y : t > 0} leaves K at t* = f(y)^{−1/2}, and t* ∈ [r/|y|, R/|y|]. Bisection on this interval with s membership queries returns t̃ with |t̃ − t*| ≤ 2^{−s} R/|y| ≤ 2^{−s}(R/r) t*. Let f̃(y) = t̃^{−2} and f̃(0) = 0. For 2^{−s} R/r ≤ 1/10 this gives |f̃(y) − f(y)| ≤ 3 · 2^{−s} (R/r) f(y).

**The linear function.** For a vector u, f(u + j) − f(u − j) = 4 uᵀAj, so g_u(j) = (f(u + j) − f(u − j))/4 = (Au) · j is linear in j. Let g̃_u(j) = (f̃(u + j) − f̃(u − j))/4.

**Algorithm.** For each i = 1, …, d, with u = e_i, repeat m = ⌈c log(10 d²)⌉ times, for an absolute constant c:

1. Prepare the uniform superposition over j ∈ {0, …, N − 1}^d.
2. Compute g̃_u(j) into a register with 2s queries, apply the phase e^{2πi g̃_u(j)/(4Λ)}, and uncompute g̃_u(j) with 2s more queries.
3. Apply the inverse Fourier transform over ℤ_N to each of the d coordinates and measure, giving a vector k ∈ {−N/2, …, N/2 − 1}^d.

Let â_i be the coordinatewise median of the m values 4Λk/N. Set Â = (B + Bᵀ)/2 for the matrix B with columns â_i, and output Â and vol(B^d) · det(Â)^{−1/2}, where vol(B^d) is the volume of the unit ball.

*Proof.* Let w = Au/(4Λ), so every coordinate lies in [−1/4, 1/4].

*The ideal run.* With the exact phase e^{2πi g_u(j)/(4Λ)} = e^{2πi w · j}, the state after step 2 is a product over the coordinates of the states N^{−1/2} Σ_{j_k} e^{2πi w_k j_k}|j_k⟩, and step 3 is phase estimation on each coordinate. Each measured k_k satisfies |k_k − N w_k| ≤ 1 with probability at least 8/π² [3].

*The perturbed run.* For j ∈ {0, …, N − 1}^d we have |u ± j|² ≤ (1 + N√d)² ≤ 4N²d, so f(u ± j) ≤ 4ΛN²d and |g̃_u(j) − g_u(j)| ≤ 6 · 2^{−s} (R/r) ΛN²d ≤ 0.03Λ. The phases therefore differ from the ideal phases by at most η = 2π · 0.03/4 < 0.05. Since |e^{iφ} − 1| ≤ |φ|, the state before measurement is within Euclidean distance η of the ideal state, and the distribution of the outcome is within total variation distance η. Each coordinate therefore satisfies |k_k − N w_k| ≤ 1 with probability at least 8/π² − 0.05 > 3/4.

*Medians.* For each pair (i, k), more than half of the m runs give |k_k − N w_k| ≤ 1 except with probability 1/(10d²), by Hoeffding's inequality, and then the median satisfies the same bound. By the union bound over the d² pairs, with probability at least 9/10 every entry of B is within 4Λ/N of the entry of A, and so is every entry of Â, since A is symmetric. As 4Λ/N ≤ ε/(4d²R²), this is the stated accuracy.

*Volume.* Write E = Â − A. Then ‖E‖_2 ≤ d · ε/(4d²R²) and ‖A^{−1}‖_2 ≤ R², so X = A^{−1/2}EA^{−1/2} has ‖X‖_2 ≤ ε/(4d) ≤ 1/4. Every eigenvalue μ of X satisfies |log(1 + μ)| ≤ 2|μ|, so |log det(Â) − log det(A)| = |log det(I + X)| ≤ ε/2. Since vol(K) = vol(B^d) det(A)^{−1/2}, the estimate is within a factor e^{ε/4} of vol(K), which is relative error at most ε for ε ≤ 1.

*Queries.* Each run makes 4s queries, and there are d m runs, so the total is O(d log d · s) = O(d log d · log(dR/(rε))). ∎

The algorithm queries points t(u ± j) with dyadic t and integer j, so all coordinates have finite precision. The class of [1, Thm 7.3] has r = 1/2 and R = O(d²), which gives O(d log d · log(d/ε)).

## Script

`sim/check_gradient.py` runs the algorithm on random ellipsoids in dimensions 2 and 3, with r = 1/2, R = 3, grids N = 64 and 32 and s = 40 bisection steps, by computing the full state vector. It checks that the phase error is below 0.05 and that the output distribution is within that distance of the ideal one. It also checks that each coordinate is within one grid step of N w_k with probability at least 0.7, and that the medians of 9 runs per column recover A within 4Λ/N in every entry.

```
python sim/check_gradient.py
phase error, distance to the ideal output and per-coordinate success >= 0.7 checked for d = 2, 3
end to end, d = 3, N = 32: max entry error 0.2198 <= 4 Lam/N = 0.5000
```

**Not formalized:** all of the folder. Phase estimation [3] and Hoeffding's inequality enter as known results. The script tests small dimensions and grids only.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. R. Zhang. Improved upper and lower bounds for quantum convex-body volume estimation. arXiv:2610.04987, 2026.
2. S. P. Jordan. Fast quantum algorithm for numerical gradient estimation. Physical Review Letters 95, 050501, 2005. arXiv:quant-ph/0405146.
3. R. Cleve, A. Ekert, C. Macchiavello, M. Mosca. Quantum algorithms revisited. arXiv:quant-ph/9708016, 1997.
