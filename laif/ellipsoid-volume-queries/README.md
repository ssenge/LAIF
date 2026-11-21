# Volume of origin-centred ellipsoids from membership queries

Written 22 Nov 2026.

**Setting.** A convex body K ⊂ ℝ^d is given by a quantum membership oracle, which answers exactly, also on the boundary, at any finite coordinate precision, and counts one query per call, as in [1, Section 2.4]. The task is to estimate vol(K) within relative error ε with probability at least 2/3. Here K = {x : xᵀAx ≤ 1} is an ellipsoid centred at the origin, with A symmetric and positive definite and unknown, and with known radii 0 < r ≤ R such that B(0, r) ⊆ K ⊆ B(0, R).

| | Previous best bound | This folder | Status |
|---|---|---|---|
| Upper | Õ(d), implied by the separation oracles built from membership queries in [4, Thm 2.3] and [5, Thm 23], with one call per column of A; O(d^{5/2} + d^{3/2}/ε) up to log factors for all convex bodies [1, Thm 1.1] | O(d log d · log(dR/(rε))) with explicit constants, and the matrix A within entrywise error ε/(4d²R²) | Claim; checked by script |
| Lower | Ω(d) for ε = 1/4, already for origin-centred ellipsoids with B(0, 1/2) ⊆ K ⊆ B(0, Cd²) [1, Thm 7.3] | | |

On the class of [1, Thm 7.3] the bound is O(d log d · log(d/ε)), so for constant ε ≤ 1/4 the query complexity of that class is Θ(d) up to a factor log² d, and the dependence on ε is logarithmic there. The algorithm uses the technique of [4, 5], bisection along rays followed by the quantum gradient algorithm of [2], applied column by column to a difference of the squared gauge of K that is exactly linear. The exact linearity gives the logarithmic dependence on ε. A classical algorithm that learns A by bisection along the d(d + 1)/2 directions e_i and e_i + e_j uses O(d² log(dR/(rε))) queries.

## Theorem 1

**Theorem 1.** Let 0 < ε ≤ 1, and let r and R be dyadic. There is a quantum algorithm that, for an ellipsoid K = {x : xᵀAx ≤ 1} with B(0, r) ⊆ K ⊆ B(0, R), outputs a symmetric matrix Â with |Â_{ik} − A_{ik}| ≤ ε/(4d²R²) for all i, k and an estimate of vol(K) within relative error ε, with probability at least 2/3, using O(d log d · log(dR/(rε))) membership queries.

**Notation.** Let Λ = 1/r². The eigenvalues of A lie in [1/R², Λ], so |A_{ik}| ≤ Λ. Let f(y) = yᵀAy. Let N be the smallest power of 2 with N ≥ 16 d² (R/r)²/ε, and let s be the smallest integer with 2^s ≥ 200 N² d R/r.

**Bisection.** For y ≠ 0 the ray {t y : t > 0} leaves K at t* = f(y)^{−1/2}, and t* ∈ [r/|y|, R/|y|]. Let H = 2^{⌈log₂(R/|y|)⌉} < 2R/|y|, which is computable exactly for integer vectors y, since |y|² is an integer. Bisection on [0, H] with s + 1 membership queries at dyadic multiples of y returns the midpoint t̃ of the final interval, with |t̃ − t*| ≤ H 2^{−s−2} ≤ 2^{−s} R/|y| ≤ 2^{−s}(R/r) t*. Let f̃(y) = t̃^{−2} and f̃(0) = 0. For 2^{−s} R/r ≤ 1/10 this gives |f̃(y) − f(y)| ≤ 3 · 2^{−s} (R/r) f(y).

**The linear function.** For a vector u, f(u + j) − f(u − j) = 4 uᵀAj, so g_u(j) = (f(u + j) − f(u − j))/4 = (Au) · j is linear in j. Let g̃_u(j) = (f̃(u + j) − f̃(u − j))/4.

**Algorithm.** For each i = 1, …, d, with u = e_i, repeat m = ⌈c log(10 d²)⌉ times, with c = 8:

1. Prepare the uniform superposition over j ∈ {0, …, N − 1}^d.
2. Compute g̃_u(j) into a register with 2(s + 1) queries, apply the phase e^{2πi g̃_u(j)/(4Λ)}, and uncompute g̃_u(j), including the answer bits of both bisections, by executing the bisections in reverse with 2(s + 1) more queries.
3. Apply the inverse Fourier transform over ℤ_N to each of the d coordinates and measure, giving a vector k ∈ {−N/2, …, N/2 − 1}^d.

Let â_i be the coordinatewise median of the m values 4Λk/N. Set Â = (B + Bᵀ)/2 for the matrix B with columns â_i, and output Â and vol(B^d) · det(Â)^{−1/2}, where vol(B^d) is the volume of the unit ball.

*Proof.* Let w = Au/(4Λ), so every coordinate lies in [−1/4, 1/4].

*The ideal run.* With the exact phase e^{2πi g_u(j)/(4Λ)} = e^{2πi w · j}, the state after step 2 is a product over the coordinates of the states N^{−1/2} Σ_{j_k} e^{2πi w_k j_k}|j_k⟩, and step 3 is phase estimation on each coordinate. Each measured k_k satisfies |k_k − N w_k| ≤ 1 with probability at least 8/π² [3].

*The perturbed run.* For j ∈ {0, …, N − 1}^d we have |u ± j|² ≤ (1 + N√d)² ≤ 4N²d, so f(u ± j) ≤ 4ΛN²d and |g̃_u(j) − g_u(j)| ≤ 6 · 2^{−s} (R/r) ΛN²d ≤ 0.03Λ. The phase is computed with finite-precision arithmetic to 10 bits, which adds at most 2π · 2^{−10} < 0.007, so the phases differ from the ideal phases by at most η = 2π · 0.03/4 + 0.007 < 0.055. Since |e^{iφ} − 1| ≤ |φ|, the state before measurement is within Euclidean distance η of the ideal state, and the distribution of the outcome is within total variation distance η. Each coordinate therefore satisfies |k_k − N w_k| ≤ 1 with probability at least 8/π² − 0.055 > 3/4.

*Medians.* For each pair (i, k), more than half of the m runs give |k_k − N w_k| ≤ 1 except with probability 1/(10d²), by Hoeffding's inequality, and then the median satisfies the same bound. By the union bound over the d² pairs, with probability at least 9/10 every entry of B is within 4Λ/N of the entry of A, and so is every entry of Â, since A is symmetric. As 4Λ/N ≤ ε/(4d²R²), this is the stated accuracy.

*Volume.* Write E = Â − A. Then ‖E‖_2 ≤ d · ε/(4d²R²) and ‖A^{−1}‖_2 ≤ R², so X = A^{−1/2}EA^{−1/2} has ‖X‖_2 ≤ ε/(4d) ≤ 1/4. Hence Â = A^{1/2}(I + X)A^{1/2} is positive definite. Every eigenvalue μ of X satisfies |log(1 + μ)| ≤ 2|μ|, so |log det(Â) − log det(A)| = |log det(I + X)| ≤ ε/2. Since vol(K) = vol(B^d) det(A)^{−1/2}, the estimate is within a factor e^{ε/4} of vol(K), which is relative error at most ε for ε ≤ 1.

*Queries.* Each run makes 4(s + 1) queries, and there are d m runs, so the total is O(d log d · s) = O(d log d · log(dR/(rε))). ∎

The algorithm queries points t(u ± j) with dyadic t and integer vectors u ± j, so all coordinates are dyadic. The class of [1, Thm 7.3] has r = 1/2 and R = O(d²), which gives O(d log d · log(d/ε)), and with the lower bound of [1] at ε = 1/4 the class has query complexity Θ(d) up to log² d for constant ε ≤ 1/4.

## Script

`sim/check_gradient.py` runs the algorithm on random ellipsoids with r = 1/2 and R = 3, by computing the full state vector, for (d, N) = (2, 64), (3, 16) and (4, 8), with the dyadic bisection bracket and the value of s from the theorem. It checks the bisection bound |f̃ − f| ≤ 3 · 2^{−s}(R/r) f, the phase error η < 0.05, the total variation bound to the ideal output, and that each coordinate satisfies |k_k − N w_k| ≤ 1 with probability at least 8/π² − η. In dimension 3 with N = 64 it then takes the medians of 9 sampled runs per column, checks the entry error 4Λ/N, and checks the bound |log det Â − log det A| ≤ 2d‖X‖_2 whenever ‖X‖_2 ≤ 1/4, the regime that the value of N in the theorem guarantees. It also checks the constants of the median, logarithm, volume and phase steps.

```
python sim/check_gradient.py
d = 2, N = 64, s = 24: phase error 0.0002, per-coordinate success >= 0.8108
d = 3, N = 16, s = 20: phase error 0.0007, per-coordinate success >= 0.8132
d = 4, N = 8, s = 19: phase error 0.0003, per-coordinate success >= 0.8215
end to end, d = 3, N = 64: max entry error 0.1617 <= 4 Lam/N = 0.2500; |log det error| <= 2 d ||X|| in the 2 of 4 cases with ||X|| <= 1/4
median, logarithm, volume and phase constants checked
```

**Not formalized:** all of the folder. Phase estimation [3] and Hoeffding's inequality enter as known results. The script tests small dimensions and grids only.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. R. Zhang. Improved upper and lower bounds for quantum convex-body volume estimation. arXiv:2610.04987, 2026.
2. S. P. Jordan. Fast quantum algorithm for numerical gradient estimation. Physical Review Letters 95, 050501, 2005. arXiv:quant-ph/0405146.
3. R. Cleve, A. Ekert, C. Macchiavello, M. Mosca. Quantum algorithms revisited. arXiv:quant-ph/9708016, 1997.
4. S. Chakrabarti, A. M. Childs, T. Li, X. Wu. Quantum algorithms and lower bounds for convex optimization. Quantum 4, 221, 2020. arXiv:1809.01731.
5. J. van Apeldoorn, A. Gilyén, S. Gribling, R. de Wolf. Convex optimization using quantum oracles. Quantum 4, 220, 2020. arXiv:1809.00643.
