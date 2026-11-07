# Optimizing parametrized quantum circuits with logarithmically many parameters

Written 7 Nov 2026.

## Problem

[1] studies the global optimization of a parametrized quantum circuit (PQC) on N qubits,

U(θ) = U_K(θ_{j_K}) C_K ⋯ U_1(θ_{j_1}) C_1,  U_k(t) = e^{−itV_k},  f(θ) = ⟨0|U(θ)† O U(θ)|0⟩,  f* = min_θ f(θ),

with fixed gates C_k, self-adjoint generators V_k and M independent parameters θ_1, …, θ_M, each of which may appear in many gates. Under its assumptions (the spectra of the V_k have integer differences; K and the spectral diameters Δ_k = λ_max(V_k) − λ_min(V_k) are at most polynomial in N; ‖O‖ is at most polynomial in N; M is constant), [1] gives a randomized approximation scheme for f* that runs in polynomial time and makes polynomially many queries to the quantum device. As a consequence, the gap problem GAP-PQCO (given a < b with b − a ≥ 1/poly(N), decide whether f* ≤ a or f* ≥ b) is in BPP^BQP for constant M, so it is not NP-hard unless NP ⊆ BQP [1, Theorem 10]. Together with the NP-hardness when M grows linearly [3], [1] concludes: "the problem is tractable for M = O(1), and non-tractable for M = O(n), while the case of M = O(log n) remains unknown."

This note answers the case M = O(log N) for algorithms that use the device by running the circuit and measuring, which includes the algorithm of [1]: they need time N^{Θ(M)} in the worst case, quasi-polynomial at M = Θ(log N). The upper bound N^{O(M)} holds for every instance, and the lower bound holds under the exponential time hypothesis (ETH). So for such algorithms the case is not polynomial under ETH, and it is not NP-hard unless NP has quasi-polynomial quantum algorithms.

## Result

All instances below satisfy the assumptions of [1] except that M may grow with N; parameters θ are rational of polynomial bit length, as in [1]. For parameter j, let Λ_j = Σ_{k : j_k = j} Δ_k be the total spectral diameter of its gates, and Λ = max_j Λ_j ≤ KΔ_max.

**Theorem 1 (upper bound).** GAP-PQCO with M parameters is decided with error at most 1/3 by a grid search that runs the circuit

G · O(‖O‖² (b − a)^{−2} log G) times,  G = ⌈6πM‖O‖Λ/(b − a)⌉^M,

with classical work of the same order, and log(6G) in place of log G. Under the assumptions of [1] this is N^{O(M)}, so N^{O(log N)} for M = O(log N).

**Theorem 2 (reduction from Clique).** Given a graph G on n ≥ 2 vertices and k ≥ 2, one can build in time poly(n, k) a description of an instance with M = k parameters, k⌈log₂ n⌉ active qubits, K = k⌈log₂ n⌉ + 1 parametrized gates of spectral diameter less than n, and a diagonal observable with ‖O‖ ≤ 1, such that

- if G has a k-clique, then f* = 0;
- if G has no k-clique, then f(θ) ≥ 1/C(k, 2) for every θ.

Adding idle qubits up to N = max(n, 2^k, k⌈log₂ n⌉) gives M ≤ log₂ N, spectral diameters below N, a description of size poly(N) and a gap 1/C(k, 2) ≥ 2/log₂² N. With O scaled by C(k, 2) instead, ‖O‖ ≤ log₂² N and the gap is 1. The padding to N ≥ n cannot be avoided by a reduction of this kind: the state of a register is a trigonometric polynomial of degree at most Λ_j in θ_j, so selecting one of n vertices needs Λ_j ≥ (n − 1)/2, while Λ_j ≤ poly(N). The output law of the circuit is a product of k explicit laws on m = 2^{⌈log₂ n⌉} values, so samples of the measurement of O, and the values f(θ), can be computed classically in time poly(n, k).

**Corollary 3.** Consider algorithms for GAP-PQCO that access the circuit only by running U(θ) at chosen θ and measuring O (or by receiving estimates of f(θ)), with classical computation otherwise. The algorithm of [1] and the grid search of Theorem 1 are of this kind. Assume ETH.

- No such algorithm runs in time N^{o(M)} on the instances with M ≤ log₂ N; in particular none runs in polynomial time on them. On these instances the exponent of Theorem 1 is optimal up to a constant factor.
- For algorithms that use a quantum computer in an arbitrary way, the same conclusion holds under the assumption that k-Clique has no quantum algorithm of time g(k) n^{o(k)} for a computable g, which follows from a quantum version of ETH by the reduction of [2].

**Corollary 4.** If GAP-PQCO with M = O(log N) is NP-hard under polynomial-time many-one reductions, then NP is contained in quantum quasi-polynomial time, BQTIME(2^{polylog n}).

So at M = Θ(log N) the problem sits strictly between the two cases of [1] and [3], under these hypotheses.

## Proofs

**Theorem 1.** Shift each V_k by a multiple of the identity so that ‖V_k‖ = Δ_k/2; this changes U(θ) only by a phase. Then ∂f/∂θ_j is a sum over the gates k with j_k = j of terms −i⟨ψ_k|[V_k, O_k]|ψ_k⟩ with O_k unitarily equivalent to O, each at most 2‖V_k‖‖O‖ = Δ_k‖O‖ in absolute value. So |f(θ) − f(θ′)| ≤ ‖O‖ Σ_j Λ_j |θ_j − θ′_j|. Integer spectral differences make U_k(t + 2π) equal to U_k(t) up to a phase, so f is 2π-periodic in every coordinate. Take the grid with spacing δ = 2π/⌈6πM‖O‖Λ/(b − a)⌉ ≤ (b − a)/(3M‖O‖Λ) in each coordinate. The minimizer is within δ/2 of a grid point in every coordinate, so that grid point has f ≤ f* + (b − a)/6. Estimate f at each of the G points to within (b − a)/6 by averaging measurements of O, whose outcomes lie in [−‖O‖, ‖O‖]: by the additive tail bound for bounded samples, O(‖O‖²(b − a)^{−2} log G) runs per point make all G estimates correct with probability at least 2/3. Answer "f* ≤ a" exactly when the smallest estimate is at most (a + b)/2. If f* ≤ a, the smallest estimate is at most a + (b − a)/3 < (a + b)/2. If f* ≥ b, every estimate is at least b − (b − a)/6 > (a + b)/2. Under the assumptions of [1], M‖O‖Λ/(b − a) ≤ poly(N), so G = N^{O(M)}.

**Theorem 2.** Let s = ⌈log₂ n⌉ and m = 2^s, and name the vertices 0, …, n − 1; the values n, …, m − 1 are extra vertices without edges. Use k registers of s qubits. On register j:

1. apply the gate (X + Z)/√2 to each qubit, giving the uniform superposition over x ∈ {0, …, m − 1};
2. for q = 0, …, s − 1 apply e^{−iθ_j 2^q n_q}, where n_q = |1⟩⟨1| on qubit q. The generator 2^q n_q has spectrum {0, 2^q}, an integer difference less than n. Together these give the state m^{−1/2} Σ_x e^{−iθ_j x}|x⟩;
3. apply the quantum frequency transform |x⟩ ↦ m^{−1/2} Σ_u e^{2πixu/m}|u⟩, a fixed circuit of O(s²) gates.

In the form of [1], whose circuit ends with a parametrized gate, the transforms of all registers form the fixed gate C_K of one last gate U_K with V_K = 0, which changes nothing.

The parameter θ_j is shared by the s gates of register j, so M = k, and the registers never interact. Register j then gives outcome u with probability

p_m(θ_j − 2πu/m),  p_m(t) = sin²(mt/2) / (m² sin²(t/2)),

and the k outcomes are independent. At θ_j = 2πv/m the register gives v with probability 1.

Call a pair of vertices bad if they are equal or not adjacent; every extra vertex is in a bad pair with every vertex. Let O be diagonal with entry (1/C(k, 2)) · #{j < j′ : (u_j, u_j′) bad} on the outcome (u_1, …, u_k). Then 0 ≤ O ≤ 1, and O is a sum of C(k, 2) diagonal terms on 2s qubits each, so it has a description of size poly(n, k).

If v_1, …, v_k is a k-clique, then at θ_j = 2πv_j/m the outcome is (v_1, …, v_k) with probability 1, and no pair is bad, so f = 0 = f*. If G has no k-clique, then every outcome (u_1, …, u_k) has a bad pair: otherwise the u_j are distinct, all in {0, …, n − 1} and pairwise adjacent. So O ≥ 1/C(k, 2) on every outcome and f(θ) ≥ 1/C(k, 2) for every θ.

The outcome law is the product of the k laws above, each on m < 2n values, so it can be sampled exactly and f(θ) computed classically in time poly(n, k) (the sum of C(k, 2) terms p_j^T B p_{j′}, with B the matrix of bad pairs).

**Corollary 3.** Suppose such an algorithm A runs in time N^{M/r(M)} on instances with M ≤ log₂ N, with r computable, unbounded and nondecreasing; we may take r ≥ 1. Polynomial time N^c is the case r(M) = M/c. Given (G, k), build the instance of Theorem 2 and run A, replacing each run of the circuit by a classical sample, which costs poly(n, k). This decides whether G has a k-clique. With s = ⌈log₂ n⌉ and N = max(n, 2^k, ks) ≤ 2^k · 2kn, the time is N^{k/r(k)} poly(n, k) ≤ (2^{k²} (2k)^k) n^{k/r(k)} poly(n, k). So k-Clique is solved in time g(k) n^{o(k)} with g computable, which ETH excludes [2]. For a general quantum algorithm the same argument, without the classical replacement, gives a quantum algorithm for k-Clique of time g(k) n^{o(k)}.

**Corollary 4.** By Theorem 1 with b − a ≥ 1/poly(N), M = O(log N) and the other bounds polynomial, GAP-PQCO is decided in quantum time N^{O(log N)}; the grid points can be rounded to rational points of polynomial bit length at an extra error that the slope bound absorbs, as in [1]. Composing with a polynomial-time reduction from an NP-complete problem gives quantum algorithms of time 2^{O(log² n)} for it.

## Scope

- Theorem 1 is the plain grid search and needs no structure beyond the slope bound and periodicity; the approximation scheme of [1] has the same exponential dependence on M through the size of its relaxation.
- The lower bound holds for the gap problem with gap 1 and ‖O‖ ≤ log₂² N, so it excludes polynomial algorithms with constant additive error. Scaled by the range max f − f* ≤ C(k, 2), as in [1, Eq. 10], it excludes error 1/(2C(k, 2)) and smaller, of order 1/log² N; constant range-scaled error is not addressed.
- Numerical evidence of many poor local minima for circuits whose number of parameters grows logarithmically is given in [4].
- The hard instances are classically simulable, so the hardness comes from the optimization over θ and not from simulating the circuit, as in [3] for M = Θ(N).
- Corollary 3 for arbitrary quantum algorithms rests on the stated hypothesis about k-Clique, not on ETH alone.

## Check

`sim/clique_check.py` (numpy, scipy):

1. simulates the circuit of Theorem 2 as a state vector on 9 qubits (three registers of 3 qubits) for random graphs and angles and compares f with the closed form;
2. on a graph on 8 vertices with a 4-clique, gives f = 0 at the clique angles;
3. on the graph on 8 vertices with edges between vertices at cyclic distance 1 or 2 (largest clique 3), finds no point below 1/C(4, 2) among 2000 random angles and 100 local minimizations;
4. compares the mean of O over classical samples from the product law with f.

Output:

```
1. state vector simulation on 9 qubits agrees with the closed form (3 random graphs and angles)
2. graph with a 4-clique: f = 6.6e-32 at theta = 2 pi (0, 2, 5, 7) / 8
3. graph without a 4-clique: min f over 2000 random points 0.1742, after 100 local minimizations 0.1667, bound 1/C(4,2) = 0.1667
4. classical sampling: mean of O over 200000 samples 0.4461, f = 0.4461
reduction checks pass
```

## References

1. I. Sakos, A. Varvitsiotis, G. Korpas, W. Lin. Global Optimization for Parametrized Quantum Circuits. arXiv:2603.21757 (2026).
2. J. Chen, X. Huang, I. A. Kanj, G. Xia. Strong computational lower bounds via parameterized complexity. Journal of Computer and System Sciences 72(8), 1346-1367 (2006).
3. L. Bittel, M. Kliesch. Training variational quantum algorithms is NP-hard. Physical Review Letters 127, 120502 (2021), arXiv:2101.07267.
4. J. Rajakumar, J. Golden, A. Bärtschi, S. Eidenbenz. Trainability barriers in low-depth QAOA landscapes. ACM Computing Frontiers 2024, arXiv:2402.10188.
