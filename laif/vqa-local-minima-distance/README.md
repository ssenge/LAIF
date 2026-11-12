# Local minima of training objectives: hardness at distance N^{(1−ε)/p}

Written 7 Nov 2026.

## Problem

[1, Theorem 1] shows that for every p ≥ 1 it is strongly NP-hard to find a parameter vector θ ∈ [0, 2π]^n within ℓp distance strictly less than π/2 of some local minimiser of an efficiently represented training objective F(θ) = ⟨0|U(θ)†HU(θ)|0⟩. The same holds for real trigonometric polynomials of total degree at most 2 [1, Proposition 2]. The threshold π/2 is the same for every p, while the diameter of [0, 2π]^N in ℓp is 2πN^{1/p}. So for p < ∞, and in particular for ℓ1 and ℓ2, the theorem only excludes a small neighbourhood.

## Result

Let 𝓕 be the class of objectives of [1, Section III] with polynomially bounded data: single-qubit rotations e^{−iθ_iX/2} on two qubits per parameter, and a commuting diagonal two-local observable with rational coefficients. Each such objective is a real trigonometric polynomial of total degree at most 2.

**Theorem 1.** Fix p ≥ 1 and ε ∈ (0, 1). There is a polynomial-time map from a graph G on n vertices and an integer k to an objective F ∈ 𝓕 on N parameters, whose coefficients have numerators O(n) and constant denominators, with the following property. Given any θ ∈ [0, 2π]^N with ‖θ − v‖_p strictly less than

(π/2) N^{(1−ε)/p}

for some local minimiser v of F over [0, 2π]^N, one can decide in polynomial time whether α(G) ≥ k. Hence, unless P = NP, no polynomial-time algorithm outputs such a θ for every F in 𝓕, and the hardness is strong. More precisely, for r copies of an instance of [1] (N = rn) the radius is (π/2)(1 − 1/N) r^{1/p}. For r = 1 this is the radius π/2 of [1] up to the factor 1 − 1/N.

For p = 1 the radius is (π/2)N^{1−ε}, against the diameter 2πN.

## Proof

**Copies.** Let f be the hard instance of [1] on n parameters built from G and k. Its local minimisers lie in {0, 2π}^n if α(G) < k. If α(G) ≥ k, each of them has a coordinate equal to π [1, Lemmas 3 and 4]. Take r copies on disjoint parameter blocks,

F(θ^(1), …, θ^(r)) = f(θ^(1)) + ⋯ + f(θ^(r)).

Local minimisers are meant as in [1]: F(θ) ≤ F(θ′) on a neighbourhood of θ relative to the box. If θ is a local minimiser of F, fix all blocks but one. The slice of a neighbourhood is then a neighbourhood of that block, so each block is a local minimiser of f. (Conversely, adding the inequalities on a product of neighbourhoods shows that tuples of local minimisers are local minimisers of F. Only the first direction is used.) So for α(G) < k all local minimisers of F lie in {0, 2π}^N. For α(G) ≥ k each of them has at least r coordinates equal to π. The copies stay in 𝓕: 2N qubits, one rotation per qubit, and the observable is the sum of the r observables of [1] on disjoint qubits, with the same coefficients.

**Decoder.** Let D(θ) = (Σ_i min(θ_i, 2π − θ_i)^p)^{1/p} be the ℓp distance from θ to the corner set {0, 2π}^N, and ρ = (π/2) r^{1/p}. Suppose ‖θ − v‖_p < (1 − 1/N)ρ for a local minimiser v.
- **If α(G) < k:** v is a corner, so D(θ) ≤ ‖θ − v‖_p < (1 − 1/N)ρ.
- **If α(G) ≥ k:** v has at least r coordinates at π, each at distance π from both 0 and 2π, so v is at distance at least πr^{1/p} = 2ρ from every corner. By the triangle inequality, D(θ) > 2ρ − (1 − 1/N)ρ ≥ (1 + 1/N)ρ.

The two cases are separated by a margin ρ/N, so computing D(θ) to polynomially many bits and comparing it with ρ decides Stable Set. This radius cannot be improved by any decoder that uses only the dichotomy. The point with θ_i = π/2 on r coordinates and 0 elsewhere is at distance exactly ρ both from a corner and from the point with π on those coordinates. With r = 1 this is also why [1] stops at π/2, and why ℓ∞ stays at π/2.

**Choice of r.** With r = n^{⌈2/ε⌉} we have n ≤ r^{ε/2} and N = rn ≤ r^{1+ε/2}, so r ≥ N^{1/(1+ε/2)} ≥ N^{1−ε/2}. Then

(1 − 1/N)ρ ≥ (π/2)(1 − 1/N)N^{(1−ε/2)/p} ≥ (π/2)N^{(1−ε)/p}

as soon as N^{ε/(2p)}(1 − 1/N) ≥ 1, which holds for n ≥ n_0(ε, p). Smaller graphs can be padded with isolated vertices, raising k by the same number. The instance has polynomial size and the same numbers as in [1], so the hardness is strong.

## Scope and related work

- For the objectives over a polytope in [2], the distance is amplified by enlarging the feasible region; for example [2, Corollary 2.8] gives strong hardness at ℓ2 distance ε√n for quadratic programs with small integer data. Rescaling does not change distances on the fixed periodic box of training parameters, and taking copies replaces it here.
- A local minimiser always exists, so the search problem is total. Hardness under this reduction therefore also implies that a claimed θ cannot be checked in polynomial time unless NP = coNP, consistent with the hardness of testing local minimality.
- The amplification uses only the dichotomy of [1]. A base instance whose minimisers in the yes case have a constant fraction of their coordinates at π would give the radius cN^{1/p}.

## Check

`sim/check.py` (about 30 s) checks two things:
- Evidence for the dichotomy of the base instance: on 311 small graph and threshold pairs, it looks at the end points of projected descent on [0, 1]^n. In the yes case, descent sometimes stops at the stationary point 0, and the script certifies that 0 is then not a local minimiser.
- The decoder of the proof on 12000 points, for p ∈ {1, 1.5, 2, 3} and up to 64 copies. The points include those that move every coordinate at π, or the corner coordinates, as far towards the other case as the radius allows. It also checks that the example at the end of the decoder paragraph is at distance exactly ρ from both points.

The output is in `sim/out.txt`.

## References

1. D. E. Koh, T. Mundo, I. Sakos, A. Varvitsiotis. Training Variational Quantum Algorithms Is NP-Hard, Even Locally. arXiv:2610.05128 (2026).
2. A. A. Ahmadi, J. Zhang. On the complexity of finding a local minimizer of a quadratic function over a polytope. Mathematical Programming 195, 783-792 (2022), arXiv:2008.05558.
