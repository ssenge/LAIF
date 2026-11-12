# Quantum speedup of algebraic sieves: Hamiltonicity, TSP with small weights, k-path, set packing

Written 5 Nov 2026.

## Result

The algebraic sieves of [1] and [2] repeat a randomized run until it succeeds. A run fixes a random partition and random field values and then evaluates a sum of 2^L terms. The classical cost is 2^L/P, with P the probability that a run is admissible for a fixed solution. Amplitude amplification over the runs [3] costs 2^L/√P. With new parameters this gives the following bounds. All are bounded-error quantum decision algorithms with one-sided error, polynomially many qubits and no QRAM.

| Problem | Previous best bound | This folder |
|---|---|---|
| Hamiltonicity, undirected, n vertices | O*((4(√2 − 1))^n) = O*(1.6569^n) [1] | O*((8/3)^{n/2}) = O*(1.6330^n) |
| TSP, undirected, positive integer weights of total w | O*(w 1.6569^n) [1]; O*(1.728^n) quantum for any weights, with QRAM [4] | O*(w 1.6330^n) |
| k-path, undirected | O*(1.6569^k) [2] | O*(1.6330^k) |
| p-packing of 3-sets | O*(3.3432^p) [2] | O*(2.804^p) |
| p-packing of 4-sets, 5-sets, 6-sets | O*(7.2562^p), O*(15.072^p), O*(30.82^p) [2] | O*(5.976^p), O*(12.316^p), O*(25.08^p) |

O* hides polynomial factors in n. For TSP the bound is below 1.728^n when w < 1.0578^n. TSP with arbitrary weights is unchanged, and so are Set Cover and Feedback Arc Set [4].

The packing baselines are the values of [2, Section 4.7], and 30.82 is 1.7707^6 from [2, Section 1.3]. The sums of 2^L terms are unchanged, so the gain comes only from the repetition. The gain for Hamiltonicity and k-path is a factor 1.0146^n.

## The argument

**Runs.** In each problem, a run is a function of (partition, field values) with value 0 or 1. It is 1 when a sum of 2^L terms over a field of characteristic two is nonzero. Each term takes polynomial time and space. If no solution exists, the sum vanishes as a polynomial, so every run gives 0. If a solution exists, a fixed solution is admissible for the partition with probability P, and then the run gives 1 with probability at least 1/2 over the field values, by the Schwartz-Zippel lemma, for a field of size at least twice the degree.

**Quantum.** A run is computed reversibly with 2^L poly(n) gates and poly(n) qubits: compute a term, add it to a register, uncompute it. Search over (partition, field values) with BBHT [3], cut off after O(1/√P) iterations, then decides with bounded error in time 2^L poly(n)/√P. A solution follows by self-reduction, at a polynomial factor.

**Hamiltonicity [1].** Split V into halves V1, V2. A Hamiltonian cycle with m arcs inside V1 needs L = n/2 + m labels. A fixed cycle has exactly m such arcs with probability at least C(n/2 − 1, n/2 − m − 1)²/C(n, n/2), from the counting in the proof of [1, Lemma 10]. Write s = n/2 − m and σ = s/n. Then 2^L/P^w has exponent n(1 − σ + w(1 − H(2σ))), with H the binary entropy. For w = 1 the minimum is at 2m/n = √2 − 1, which is [1]. For w = 1/2 it is at σ = 1/3, so m = n/6, with value n(3/2 − (1/2) log₂ 3). This gives (8/3)^{n/2}. Unbalanced splits give larger values. Polynomial space comes from [1, Section 4], with the special vertex s = min V1 and a field of size Θ(n²).

**TSP with small weights.** [1, Section 5] tabulates the evaluations T(l) of the sum at y = g^l, for all l below the field size, and reads off the lowest nonzero coefficient in y. That table is exponential when w is. Instead, fix a threshold W, add a random field element γ to the input of a run, and test c = Σ_l T(g^l) Σ_{j ≤ W} (γ g^{−l})^j ≠ 0. In characteristic two, c = Σ_{j ≤ W} γ^j c_j, where c_j is the coefficient of y^j. So c is a polynomial of degree at most n + W in the field values and γ, and it is nonzero exactly when an admissible tour of weight at most W exists. The inner sum is geometric, so no table is needed, and a run costs w 2^L poly(n) polylog(w). Binary search over W adds a factor log w. The field has size at least max{2(n + W), n²/3 + 2, w + 1}.

**k-path [2].** Colour the vertices at random with two colours. A path with k1 vertices of colour 1 and ℓ2 edges inside colour 2 needs L = k1 + ℓ2 labels, with probability P = 2^{−k} C(k1 + 1, k − k1 − ℓ2) C(k − k1 − 1, ℓ2) [2, Lemma 7]. Take k1 = k/2 and ℓ2 = k/6, for the same base (8/3)^{1/2}. The sum is taken for a fixed start vertex, and the start vertex is part of the search. Summed over all start vertices it vanishes, since each path cancels with its reversal.

**Set packing [2].** L = q p0 + (q − 1) p1 + (q − 2) p2, and P is [2, (16)], with p_j = β_j p. The optima of 2^L/√P are at (β1, β2) = (0.1331, 0.8601), (0.1658, 0.8216), (0.1805, 0.8032), (0.1888, 0.7924) for q = 3, 4, 5, 6. This holds for families of polynomial size.

## Machine check

`lean/QuantumSieve.lean` checks the exponents, with Lean 4.36.0-rc1 and Mathlib revision `d875a8de5222f62cf1c2fafc7984588adadc990a`. It contains no `sorry`, and its theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). For n = k = 6t and L = 4t:

- `hamiltonicity_cost`: 4^L C(6t, 3t) ≤ ((3/2)(3t + 1))² (8/3)^{6t} C(3t − 1, 2t − 1)², which is 4^L/P ≤ poly(t) (8/3)^n with the P above.
- `kpath_cost`: 4^L 2^{6t} ≤ (3/2)(3t + 1)² (8/3)^{6t} C(3t + 1, 2t) C(3t − 1, t), the same for k-path.
- `choose_lower`: (27/4)^t ≤ (3t + 1) C(3t, t).

**Not machine-checked:** BBHT, the reductions of [1] and [2], the reversible implementation, the TSP threshold test, and the set packing exponents, which are numerical.

## Numerical check

- `sim/check_sieve.py` enumerates the counts behind P for Hamiltonicity and k-path, reproduces the classical constants of [1] and [2], computes the new ones, and checks that unbalanced splits do not help.
- `sim/check_small_sieves.py` runs the four sieves over GF(2^k) on small inputs and asserts the following.
  - Hamiltonicity: the walk sum of [1, Section 4] agrees with the sum over paths, and there are no false positives.
  - Graphs made of two disjoint cycles: the sum vanishes, and it does not vanish when the mirror property of [1] is removed.
  - The marked fraction on the 6-cycle is at least P/2.
  - TSP: the threshold test decides the weight bound.
  - k-path: no false positives, with false positives when the palindrome filter of [2] is removed, and the cancellation over all start vertices.
  - Packing of 3-sets: no false positives, including families with prepackings but no packing.

  Sizes: n ≤ 10, k ≤ 6, q = 3.

## References

[1] A. Björklund. Determinant sums for undirected Hamiltonicity. SIAM J. Comput. 43(1), 2014. arXiv:1008.0541.

[2] A. Björklund, T. Husfeldt, P. Kaski, M. Koivisto. Narrow sieves for parameterized paths and packings. J. Comput. Syst. Sci. 87, 2017. arXiv:1007.1161.

[3] M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschr. Phys. 46, 1998. arXiv:quant-ph/9605034.

[4] A. Ambainis, K. Balodis, J. Iraids, M. Kokainis, K. Prūsis, J. Vihrovs. Quantum speedups for exponential-time dynamic programming algorithms. SODA 2019. arXiv:1807.05209.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
