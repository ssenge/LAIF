# Local minima of training objectives: hardness at distance N^{(1−ε)/p}

Written 7 Nov 2026.

## Problem

[1, Theorem 1] shows that for every p ≥ 1 it is strongly NP-hard to find a parameter vector θ ∈ [0, 2π]^n within ℓp distance strictly less than π/2 of some local minimiser of an efficiently represented training objective F(θ) = ⟨0|U(θ)†HU(θ)|0⟩. The same holds for real trigonometric polynomials of total degree at most 2 [1, Proposition 2]. The threshold π/2 is the same for every p, while the diameter of [0, 2π]^N in ℓp is 2πN^{1/p}. So for p < ∞, and in particular for ℓ1 and ℓ2, the theorem only excludes a small neighbourhood.

## Result

**Theorem 1.** Fix p ≥ 1 and ε ∈ (0, 1). It is strongly NP-hard, for objectives on N parameters of the form of [1] (single-qubit rotations with shared parameters, a commuting diagonal two-local observable, and degree at most 2 as trigonometric polynomials), to find θ ∈ [0, 2π]^N within ℓp distance

(π/2) (N^{1−ε}/2)^{1/p}

of some local minimiser. More generally, for r copies of an instance of [1] on n parameters (N = rn), the distance (π/2)(r/2)^{1/p} is hard.

For p = 1 this is N^{1−ε}π/4, compared with the diameter 2πN. For ℓ∞ the threshold stays at π/2.

## Proof

Let f be the hard instance of [1] on n parameters built from a graph G and a threshold k. Its local minimisers lie in {0, 2π}^n if α(G) < k. If α(G) ≥ k, each of them has a coordinate equal to π [1, Lemmas 3 and 4]. Take r copies on disjoint parameter blocks,

F(θ^(1), …, θ^(r)) = f(θ^(1)) + ⋯ + f(θ^(r)).

On the product domain, a point is a local minimiser of a sum of functions of disjoint blocks if and only if each block is a local minimiser of its term. (If one block could be improved nearby, so could the sum; conversely, fix the other blocks.) So for α(G) < k all local minimisers of F lie in {0, 2π}^N. For α(G) ≥ k each of them has at least r coordinates equal to π. The copies keep the form of [1]: 2N qubits, one rotation per qubit, and the observable is the sum of the r observables of [1] on disjoint qubits.

Suppose θ satisfies ‖θ − v‖_p < δ for a local minimiser v, with (2δ/π)^p ≤ r/2. Let Z be the number of coordinates with θ_i ∈ (π/2, 3π/2).
- **If α(G) < k:** each such coordinate has |θ_i − v_i| ≥ π/2, so Z < (2δ/π)^p ≤ r/2.
- **If α(G) ≥ k:** of the at least r coordinates with v_i = π, fewer than (2δ/π)^p have |θ_i − π| ≥ π/2, so Z > r − r/2 = r/2.

So comparing Z with r/2 decides Stable Set. With n vertices and r = n^{⌈1/ε⌉}, we have N = rn ≤ r^{1+ε}, hence r ≥ N^{1/(1+ε)} ≥ N^{1−ε}. The instance has polynomial size and the same numbers as in [1], so the hardness is strong.

## Scope

- In ℓ∞ every coordinate is decoded on its own, and the threshold π/2 is not improved here.
- The amplification uses only the dichotomy of [1]. It applies to any hard family with that dichotomy, and the factor r^{1/p} could become N^{1/p} with a base instance whose minimisers in the yes case have a constant fraction of their coordinates at π.

## Check

`sim/check.py` (about 30 s) checks two things:
- the dichotomy of the base instance on 311 small graph and threshold pairs, by projected descent on [0, 1]^n;
- the decoder on 12000 points that spend the whole distance budget against it, for p ∈ {1, 1.5, 2, 3} and up to 64 copies.

In the yes case, descent sometimes stops at the stationary point 0. The script certifies that 0 is then not a local minimiser. The output is in `sim/out.txt`.

## References

1. D. E. Koh, T. Mundo, I. Sakos, A. Varvitsiotis. Training Variational Quantum Algorithms Is NP-Hard, Even Locally. arXiv:2610.05128 (2026).
