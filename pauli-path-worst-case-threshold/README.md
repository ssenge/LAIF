# Exact failure threshold of Pauli path truncation on majority circuits

Written 6 Nov 2026.

## Problem

**The method.** The Pauli path method estimates a noisy expectation value by expanding the observable in Pauli paths through the circuit [1]. The noise is N_p(ρ) = (1 − p)ρ + pI/2 on every qubit, after every layer and before the first; write z = 1 − p. A path s = (s₀, s₁, …) has Pauli weight |s| = |s₀| + |s₁| + ⋯, which includes the weight of the observable. Its contribution is damped by z^{|s|}, so the noisy value is ⟨O⟩_err = Σ_w F_w z^w with F_w the sum of the path values of weight w. The method keeps the paths with w ≤ ℓ. Its error at cutoff ℓ is

E_ℓ = |Σ_{w>ℓ} F_w z^w|.

**The worst-case circuits of [1].** [1, Section 6] takes:

- input |0⟩^{⊗n};
- one layer of 3-qubit gates V [1, Eq. (19)] with V†Z₁V = (Z₁ + Z₂ + Z₃ − Z₁Z₂Z₃)/2, the majority vote on three qubits;
- the observable O_K, a product of Z on the first qubit of each of K blocks [1, Lemma 6].

[1, Lemma 7, Theorem 3] average O_{4k} over Θ((log n)²) values of k, so that every cutoff is covered. Each block contributes the polynomial G(x) = (3/2)x² − (1/2)x⁴, so Σ_w F_w x^w = G(x)^K [1, Eq. (21)]. [1, Theorem 3] shows that the error grows exponentially in ℓ for p < 1 − √(2/3) ≈ 0.1835. The lower bound uses the leading term ((3/2)z²)^K. Whether this range is the full range of failure for these circuits is not addressed there.

## Result

Let k be odd. Maj_k and x ↦ x₁ are both balanced on {0, 1}^k, so there is a k-qubit permutation V_k of the computational basis with V_k† Z₁ V_k = Maj_k(Z₁, …, Z_k). Every such permutation gives the same path sums, and [1, Eq. (19)] is one of them for k = 3. Let Maj_k = Σ_S \hat{M}(S) χ_S be the Fourier expansion and put

G_k(x) = x Σ_S \hat{M}(S) x^{|S|},  Ĝ_k(x) = x Σ_S |\hat{M}(S)| x^{|S|}.

The circuits are one layer of gates V_k on K blocks. When stated, one idle qubit is added, with Z in the observable; it is the 1-qubit majority, with G₁(x) = x².

**Theorem 1.** Let N = (k − 1)K/2 + 1.

1. **Failure at some cutoff.** For every K there is a cutoff ℓ ∈ [2K − 2, (k + 1)K] with E_ℓ ≥ Ĝ_k(z)^K/(2N), while |⟨O_K⟩_err| = G_k(z)^K ≤ z^K.
2. **Success.** If Ĝ_k(z) < 1, then E_ℓ ≤ r^ℓ for every ℓ, every K and every convex combination of the O_K, where r < 1 solves Ĝ_k(z/r) = 1.
3. **Every noise rate.** Ĝ_k(z) ≥ z²√(k/2). So for every p < 1 and every odd k > 2(1 − p)^{−4}, one layer of k-qubit majority gates makes the error grow exponentially. The smallest odd k with Ĝ_k(1 − p) > 1 is 11 at p = 0.5, 43 at p = 0.7 and 121 at p = 0.8.

**Lemma 2 (every prescribed cutoff).** Let Ĝ_k(z) ≥ 1. Let x₀ ∈ (0, 1] solve Ĝ_k(z x₀) = 1, and put β = k|\hat{M}({1})| z² x₀². For every even ℓ ≥ 2 there are K ≤ ℓ/2 and J ∈ {0, 1} such that the circuit with K blocks and J idle qubits has

E_ℓ ≥ z² β^{(k−1)/2} x₀^{−ℓ}/ℓ.

**The threshold.** Let ρ solve Ĝ_k(z/ρ) = 1.

- If ρ > 1, then by Lemma 2 the worst circuit of the family at cutoff ℓ has error at least ρ^ℓ/poly(ℓ), on n ≤ kℓ/2 + 1 qubits. So ℓ = Θ(log n) gives an error polynomially large in n, as in [1, Theorem 3], with a single product observable.
- If ρ < 1, then every circuit has error at most ρ^ℓ by part 2.

So the method fails on this family exactly when Ĝ_k(1 − p) > 1. For k = 3, Ĝ₃(z) = (3/2)z² + (1/2)z⁴, and the threshold is

p* = 1 − √((√17 − 3)/2) ≈ 0.2506.

At p = p* the worst error is at least of order 1/ℓ by Lemma 2, and every error is at most Σ_w |F_w| z^w = 1.

On the same circuits, the range of failure shown in [1], p < 0.1835, thus extends to p < 0.2506, and this is the exact threshold for the family. With majority gates of width O((1 − p)^{−4}), failure extends to every p < 1. This last part is a direct generalization of the construction of [1] with a standard Fourier fact.

## Proof

- **Fourier coefficients.** The coefficients of majority vanish on even levels. On a set S of odd size j they are [2, Section 5.3]
  \hat{M}(S) = (−1)^{(j−1)/2} · C((k−1)/2, (j−1)/2)/C(k−1, j−1) · C(k−1, (k−1)/2)/2^{k−1}.
- **Paths.** Conjugating O_K by the layer gives ⊗_b Maj_k(Z_{block b}) = ⊗_b Σ_S \hat{M}(S) Z_S. A path through block b ends in Z₁ (weight 1) and starts in Z_S (weight |S|). Its value is \hat{M}(S)⟨0|Z_S|0⟩ = \hat{M}(S). So Σ_w F_w x^w = G_k(x)^K, and the noisy value is G_k(z)^K. Here G_k(z) is z times the noisy majority at the all-zero input, so it lies in [0, z]. An idle qubit with Z contributes weight 1 before and after the layer and value 1, which is the factor x².
- **Signs.** The coefficient of x^{1+j} in G_k has sign (−1)^{(j−1)/2}, and i^{1+j} = −(−1)^{(j−1)/2}. So every term of G_k(ix) is −|coefficient|·x^w, and G_k(ix) = −Ĝ_k(x). The coefficients of G_k(ix)^K = (−1)^K Ĝ_k(x)^K are F_w i^w. So no cancellation happens inside a degree: |F_w| is the coefficient of x^w in Ĝ_k^K, and Σ_w |F_w| z^w = Ĝ_k(z)^K.
- **Part 1.** Only the N even degrees from 2K to (k + 1)K carry coefficients. So some w* has |F_{w*}| z^{w*} ≥ Ĝ_k(z)^K/N. The signed tails T_ℓ = Σ_{w>ℓ} F_w z^w satisfy T_{w*−2} − T_{w*} = F_{w*} z^{w*}. So one of the two has modulus at least Ĝ_k(z)^K/(2N).
- **Part 2.** Since Ĝ_k(1) ≥ G_k(1) = 1 and Ĝ_k(z) < 1, some r ∈ (z, 1) has Ĝ_k(z/r) = 1. Then
  E_ℓ ≤ Σ_{w>ℓ} |F_w| (z/r)^w r^w ≤ r^ℓ Ĝ_k(z/r)^K = r^ℓ,
  uniformly in K. By the triangle inequality the bound holds for convex combinations too.
- **Part 3.** Level one contributes k · C(k−1, (k−1)/2)/2^{k−1}. Using C(2m, m)/4^m ≥ 1/(2√m), this is at least k/√(2(k − 1)) ≥ √(k/2). Since every term of Ĝ_k is nonnegative, Ĝ_k(z) ≥ z · z · √(k/2).
- **Lemma 2.** Put a_w(K) = |F_w(K)| z^w, the coefficient of x^w in Ĝ_k(zx)^K.
  - The numbers q_w = [x^w] Ĝ_k(zx) · x₀^w sum to Ĝ_k(z x₀) = 1. So they form a probability law on the even steps {2, 4, …, k + 1}, and Σ_K a_ℓ(K) x₀^ℓ is the probability that the walk with these steps hits ℓ.
  - Look at the first time the walk is at least ℓ − k + 1. Steps are at most k + 1 and positions are even, so the walk is then in [ℓ − k + 1, ℓ]. From there, at most (k − 1)/2 steps of size 2 reach ℓ, and each has probability q₂ = β. So the walk hits ℓ with probability at least β^{(k−1)/2}.
  - Only K ≤ ℓ/2 contribute, so some K has a_ℓ(K) ≥ (2/ℓ) β^{(k−1)/2} x₀^{−ℓ}.
  - With one idle qubit the tail at cutoff ℓ is z² T_{ℓ−2}(K). Since T_{ℓ−2} − T_ℓ = F_ℓ z^ℓ, one of the two circuits has E_ℓ ≥ z² a_ℓ(K)/2. □

## Remarks

1. **Scope.**
   - As in [1], this concerns the plain truncation by path weight. The circuits have one layer and are easy to simulate classically. [1] notes that applying the method to each observable of its mixture separately works. For the product O_K, evaluating the blocks separately avoids the failure as well.
   - In part 3 the width k is a constant for each fixed p, but it grows like (1 − p)^{−4} as p → 1. For gates of width bounded independently of p, and for deeper circuits, the worst-case threshold is not treated here.
2. **Why the leading term undercounts.** The coefficients of G_k^K have fixed signs by degree. So one of two neighbouring tails is at least half the largest single term, which is at least Ĝ_k(z)^K/N. The bound in [1] uses only the leading term ((3/2)z²)^K.

## Check

`sim/threshold_check.py` works in exact rational arithmetic and asserts the following.

- **The block.** For k = 3 and 5 it builds a permutation V_k with V_k†Z₁V_k = Maj_k, and for k = 3 also checks the gate of [1, Eq. (19)]. It compares the Pauli weights of the conjugated observable with G_k. It compares the noisy value from a density-matrix simulation with N_p before and after the layer against G_k(1 − p) at p = 0.3.
- **k = 3.** For p ∈ {0.20, 0.22, 0.24, 0.26, 0.30} and K ∈ {10, 40, 160}:
  - Σ_w |F_w| x^w = Ĝ₃(x)^K coefficient by coefficient;
  - the worst truncation error is at least the bound of part 1, at a cutoff in [2K − 2, 4K];
  - where Ĝ₃(z) < 1, every error is at most r^ℓ.
- **Every rate.** For p ∈ {0.5, 0.7, 0.8} it finds the smallest odd k with Ĝ_k(z) > 1 and checks that it is below 2/z⁴. For K = 30 it checks the bound of part 1, against true values of order 10⁻¹⁰ to 10⁻²². It checks the level-one bound √(k/2) for every odd k ≤ 201.
- **Lemma 2.** For k = 3 at p = 0.24 and every even ℓ ≤ 120, and for k = 5 at p = 0.3 and every even ℓ ≤ 80, it finds a circuit with K ≤ ℓ/2 and J ∈ {0, 1} meeting the bound.

```
block check: V^dag Z_1 V = Maj for k = 3, 5; Pauli weights and noisy values match G
k = 3: G(z) = 1.5 z^2 - 0.5 z^4, Ghat(z) = 1.5 z^2 + 0.5 z^4, Ghat(1 - p) = 1 at p* = 0.2506
  p = 0.20, Ghat = 1.1648: K = 10: worst error 0.814 >= 0.209; K = 40: worst error 37.6 >= 5.45; K = 160: worst error 1.65e+09 >= 1.24e+08
  p = 0.22, Ghat = 1.0977: K = 10: worst error 0.453 >= 0.115; K = 40: worst error 3.57 >= 0.507; K = 160: worst error 1.27e+05 >= 9.29e+03
  p = 0.24, Ghat = 1.0332: K = 10: worst error 0.249 >= 0.063; K = 40: worst error 0.318 >= 0.0451; K = 160: worst error 8.03 >= 0.579
  p = 0.26, Ghat = 0.9713: K = 10: worst error 0.134 >= 0.034; K = 40: worst error 0.0276 >= 0.00381; K = 160: worst error 0.000418 >= 2.96e-05
  p = 0.30, Ghat = 0.8550: K = 10: worst error 0.0383 >= 0.00949; K = 40: worst error 0.000176 >= 2.32e-05; K = 160: worst error 5.98e-13 >= 4.08e-14
p = 0.5: smallest odd k with Ghat > 1 is 11 (bound 2/z^4 = 32); Ghat = 1.0600, K = 30 blocks: worst error 0.295, true value 1.10e-10
p = 0.7: smallest odd k with Ghat > 1 is 43 (bound 2/z^4 = 247); Ghat = 1.0258, K = 30 blocks: worst error 0.073, true value 5.54e-17
p = 0.8: smallest odd k with Ghat > 1 is 121 (bound 2/z^4 = 1250); Ghat = 1.0167, K = 30 blocks: worst error 0.0447, true value 4.88e-22
k = 3, p = 0.24: every even cutoff l <= 120 has a circuit with error >= z^2 beta^((k-1)/2) x0^-l / l, x0 = 0.9860 (growth rate 1/x0 = 1.0142); smallest ratio worst error / bound 1.61
k = 5, p = 0.3: every even cutoff l <= 80 has a circuit with error >= z^2 beta^((k-1)/2) x0^-l / l, x0 = 0.9130 (growth rate 1/x0 = 1.0953); smallest ratio worst error / bound 1.88
level one mass of k-bit majority >= sqrt(k/2) for odd k = 3..201
Pauli path threshold checks pass
```

## References

1. G. González-García, J. I. Cirac, R. Trivedi. Pauli path simulations of noisy quantum circuits beyond average case. Quantum 9, 1730 (2025), arXiv:2407.16068.
2. R. O'Donnell. Analysis of Boolean Functions. Cambridge University Press (2014), arXiv:2105.10386.
