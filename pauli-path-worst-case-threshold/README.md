# Exact failure threshold of Pauli path truncation on majority circuits

Written 6 Nov 2026.

## Problem

**The method.** The Pauli path method estimates a noisy expectation value by expanding the observable in Pauli paths through the circuit [1]. Write z = 1 − p for depolarizing noise of rate p. A path of Pauli weight w is damped by z^w, so the noisy value is ⟨O⟩_err = Σ_w F_w z^w. The method keeps the paths with w ≤ ℓ. Its error at cutoff ℓ is

E_ℓ = |Σ_{w>ℓ} F_w z^w|.

**The worst-case circuits of [1].** [1, Section 6] uses the following setup:

- input |0⟩^{⊗n};
- one layer of 3-qubit gates V with V†Z₁V = (Z₁ + Z₂ + Z₃ − Z₁Z₂Z₃)/2, the majority vote on three qubits;
- depolarizing noise on every qubit before and after the layer;
- the observable O_K, a product of Z on the first qubit of each of K blocks.

Each block contributes the polynomial G(x) = (3/2)x² − (1/2)x⁴, so Σ_w F_w x^w = G(x)^K. [1, Lemma 6, Theorem 3] shows that E_ℓ grows exponentially in ℓ for p < 1 − √(2/3) ≈ 0.1835. The proof bounds the error by the leading term ((3/2)z²)^K. Whether this threshold is tight is not addressed there.

## Result

Let k be odd. Let V_k be a k-qubit permutation of the computational basis with V_k† Z₁ V_k = Maj_k(Z₁, …, Z_k), the majority vote; for k = 3 this is the gate of [1]. Let Maj_k = Σ_S \hat{M}(S) χ_S be its Fourier expansion and put

G_k(x) = x Σ_S \hat{M}(S) x^{|S|},  Ĝ_k(x) = x Σ_S |\hat{M}(S)| x^{|S|}.

**Theorem 1.** Take the circuits above with gates V_k and K blocks. Let N = (k − 1)K/2 + 1.

1. **Failure.** For every K there is a cutoff ℓ with E_ℓ ≥ Ĝ_k(z)^K/(2N), while |⟨O_K⟩_err| = G_k(z)^K ≤ 1.
2. **Success.** If Ĝ_k(z) < 1, then E_ℓ ≤ r^ℓ for every ℓ, where r < 1 solves Ĝ_k(z/r) = 1.
3. **The threshold.** So on these circuits the method fails exactly when Ĝ_k(1 − p) > 1. For k = 3, Ĝ₃(z) = (3/2)z² + (1/2)z⁴, and the threshold is
   p* = 1 − √((√17 − 3)/2) ≈ 0.2506.
   The error grows exponentially in K for p < 0.2506 and decays exponentially in ℓ for p > 0.2506.
4. **Every noise rate.** Ĝ_k(z) ≥ z²√(k/2). So for every p < 1 and every odd k > 2(1 − p)^{−4}, one layer of k-qubit majority gates makes the error grow exponentially in K. The smallest such k is 11 at p = 0.5, 43 at p = 0.7 and 121 at p = 0.8.

In parts 1 and 4 the cutoffs lie between 2K − 2 and (k + 1)K. So ℓ = Θ(log n) gives an error that is polynomially large in n, as in [1, Theorem 3]. The threshold 0.1835 of [1] thus rises to 0.2506 for the same circuits. With gates of width O((1 − p)^{−4}), the worst-case failure extends to every p < 1.

## Proof

- **Fourier coefficients.** The coefficients of majority vanish on even levels. On a set S of odd size j they equal [2, Chapter 5]
  \hat{M}(S) = (−1)^{(j−1)/2} · C((k−1)/2, (j−1)/2)/C(k−1, j−1) · C(k−1, (k−1)/2)/2^{k−1}.
- **Paths.** Conjugating O_K by the layer gives ⊗_b Maj_k(Z_{block b}) = ⊗_b Σ_S \hat{M}(S) Z_S. A path through block b ends in Z₁ (weight 1) and starts in Z_S (weight |S|). Its value is \hat{M}(S)⟨0|Z_S|0⟩ = \hat{M}(S). So Σ_w F_w x^w = G_k(x)^K, which is [1, Eq. (21)] for k = 3. The noisy value is G_k(z)^K, and G_k(z) ∈ [0, 1] is the noisy majority on the all-zero input.
- **Signs.** The coefficient of x^{1+j} in G_k has sign (−1)^{(j−1)/2}, and i^{1+j} = −(−1)^{(j−1)/2}. So every term of G_k(ix) is −|coefficient|·x^w, and G_k(ix) = −Ĝ_k(x). Hence F_w i^w = (−1)^K |F_w|, and Σ_w |F_w| z^w = Ĝ_k(z)^K.
- **Part 1.** Only the N even degrees from 2K to (k + 1)K carry coefficients. So some w* has |F_{w*}| z^{w*} ≥ Ĝ_k(z)^K/N. The signed tails T_ℓ = Σ_{w>ℓ} F_w z^w satisfy T_{w*−2} − T_{w*} = F_{w*} z^{w*}. So one of the two has modulus at least Ĝ_k(z)^K/(2N).
- **Part 2.** Since Ĝ_k(1) ≥ G_k(1) = 1 and Ĝ_k(z) < 1, some r ∈ (z, 1) has Ĝ_k(z/r) = 1. Then
  E_ℓ ≤ Σ_{w>ℓ} |F_w| (z/r)^w r^w ≤ r^ℓ Ĝ_k(z/r)^K = r^ℓ.
- **Part 4.** Level one contributes k · C(k−1, (k−1)/2)/2^{k−1}. Using C(2m, m)/4^m ≥ 1/(2√m), this is at least k/√(2(k − 1)) ≥ √(k/2). Since every term of Ĝ_k is nonnegative, Ĝ_k(z) ≥ z · z · √(k/2). □

## Remarks

1. **Scope.**
   - As in [1], this concerns the plain truncation by path weight. The circuits have one layer and are easy to simulate classically, and applying the method to each block separately avoids the failure, as [1] notes.
   - Part 4 uses gates whose width grows like (1 − p)^{−4} as p → 1. For circuits of fixed locality, and for deeper circuits, the worst-case threshold is not treated here.
2. **Why the leading term undercounts.** The coefficients alternate in sign. So the tail at a cutoff in the middle of the range is close to the largest single term, which carries the full mass Ĝ_k(z)^K/N, not only the top coefficient (3/2)^K.

## Check

`sim/threshold_check.py` works in exact rational arithmetic and asserts the following.

- **The block.** For k = 3 and 5 it builds the permutation V_k with V_k†Z₁V_k = Maj_k. It computes the Pauli weights of the conjugated observable and compares them with the formula for G_k. It also compares the noisy value from a density-matrix simulation with G_k(1 − p) at p = 0.3.
- **k = 3.** For p ∈ {0.20, 0.22, 0.24, 0.26, 0.30} and K ∈ {10, 40, 160}, the worst truncation error is at least the bound of part 1. Where Ĝ₃(z) < 1, every error is at most r^ℓ.
- **Every rate.** For p ∈ {0.5, 0.7, 0.8} it finds the smallest odd k with Ĝ_k(z) > 1 and checks that it is below 2/z⁴. For K = 30 it checks the bound of part 1, against true values of order 10⁻¹⁰ to 10⁻²².

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
Pauli path threshold checks pass
```

## References

1. G. González-García, J. I. Cirac, R. Trivedi. Pauli path simulations of noisy quantum circuits beyond average case. Quantum 9, 1730 (2025), arXiv:2407.16068.
2. R. O'Donnell. Analysis of Boolean Functions. Cambridge University Press (2014), arXiv:2105.10386.
