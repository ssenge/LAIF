# Multi-photon quantum neural networks with a fixed observable: the photon threshold is m − 1

2026-11-22

## Problem

A multi-photon quantum neural network (MPQNN) of [1] sends n photons through m optical modes. It applies L + 1 trainable linear optical blocks with L phase-shift encodings e^{ix} in between, and measures an observable that is diagonal in the photon-number basis. By [1, Theorem 1] its output functions are exactly the functions g(y_1(x), …, y_m(x)), where g is a real polynomial of total degree at most n, fixed by the observable, and y = (y_1, …, y_m) lies in

Δ = {y ∈ P_L^m : y_j ≥ 0, Σ_j y_j = 1},

with P_L the real trigonometric polynomials of degree at most L. For a fixed observable the hypothesis space is H_g = {α g(y) : y ∈ Δ, α ∈ ℝ} [1, eq. (13)].

In [1, Lemma 6] a g of degree at most n with P_{dL} ⊆ H_g is constructed for d = min{n, m − 2}. With the rate of best trigonometric approximation [1, Proposition 5] this gives the error bound C_K ‖f^{(K)}‖_∞ / (dL)^K for every K-times differentiable 2π-periodic f [1, Theorem 2]. Above the photon threshold n = m − 2 the bound stops improving. A dimension count gives the necessary condition N ≤ min{nL, (m − 1)L + (m − 1)/2} for P_N ⊆ H_g [1, eq. (B30)].

| | largest N with P_N ⊆ H_g for some g of degree ≤ n, n ≥ m − 1 |
|---|---|
| Previous construction [1, Lemma 6] | N ≥ (m − 2)L |
| Dimension bound [1, eq. (B30)] | N ≤ (m − 1)L + ⌊(m − 1)/2⌋ |
| Proposition 1 | N ≥ (m − 1)L |

## Results

**Proposition 1.** For m ≥ 3, L ≥ 1 and n ≥ m − 1 there is a real polynomial g of total degree m − 1 with P_{(m−1)L} ⊆ H_g.

So the threshold of [1, Lemma 6] improves from m − 2 to m − 1: the inclusion P_{dL} ⊆ H_g holds with d = min{n, m − 1}, and the bound of [1, Theorem 2] holds with this d:

inf_{h ∈ H_g} ‖f − h‖_∞ ≤ C_K ‖f^{(K)}‖_∞ / (min{n, m − 1} L)^K.

For a trainable observable, H_g ⊆ H, so the d of [1, Theorem 3] becomes min{nL, max{(m − 1)L, n⌊(m − 1)/2⌋}}.

With [1, eq. (B30)], for a fixed observable the largest N with P_N ⊆ H_g is nL for n ≤ m − 1, and lies between (m − 1)L and (m − 1)L + ⌊(m − 1)/2⌋ for every n ≥ m − 1. So the growth with the photon number stops at n = m − 1: beyond it, the reachable degree gains at most ⌊(m − 1)/2⌋, independent of L. For m = 3 the reachable degree doubles, from L to 2L.

## Proof

Use the coordinates z_j = y_j − 1/m for j < m. For 0 < ε < 1/(2√2 m) let

y*(x) = (1/m + ε cos Lx, 1/m + ε sin Lx, 1/m, …, 1/m, 1/m − ε(cos Lx + sin Lx)),

so z(x) = ε(cos Lx, sin Lx, 0, …, 0). Every coordinate of y* is at least 1/m − √2 ε > 1/(2m), so a ball of radius 1/(2m) around y* in T, in the supremum norm, lies in Δ, as [1, Lemma 6] needs. Let

G(z) = z_1² + z_2² + Σ_{j=3}^{m−1} z_j T_{j−1}(z_1/ε),

where T_k is the polynomial of degree k with T_k(cos t) = cos kt. G has total degree m − 1, and g(y) = G(y_1 − 1/m, …, y_{m−1} − 1/m) − ε² does not depend on y_m.

**Constant on the curve.** Along y*, the terms with j ≥ 3 vanish, so g(y*(x)) = ε² cos² Lx + ε² sin² Lx − ε² = 0.

**Derivative.** The tangent space of Δ at y* is T = {v ∈ P_L^m : Σ_j v_j = 0}, with v_1, …, v_{m−1} free. Since ∂g/∂y_m = 0, the derivative of v ↦ g(y* + v) at 0 is v ↦ Σ_{j<m} M_j v_j with the multipliers

M_1 = 2ε cos Lx,  M_2 = 2ε sin Lx,  M_j = cos((j − 1)Lx) (3 ≤ j ≤ m − 1).

**The image is P_{(m−1)L}.** The image lies in P_{(m−1)L}. The products of e^{±iLx} with P_L span all frequencies in [−2L, 2L], and cos Lx, sin Lx give both signs, so the first two multipliers give P_{2L}. For k = 2, …, m − 2 and 1 ≤ ω ≤ L, the products cos(kLx) cos(ωx) and cos(kLx) sin(ωx) equal ½ cos((kL + ω)x) and ½ sin((kL + ω)x) plus terms at the lower frequency kL − ω. Every f with 2L < f ≤ (m − 1)L is f = kL + ω for one such pair, and kL − ω < f. Going upward from f = 2L + 1, cos(fx) and sin(fx) are twice such a product minus a term of lower frequency, which is already in the image. So the image is all of P_{(m−1)L}.

**Conclusion.** The rest is the argument of [1, Lemma 6]. The map F(v) = g(y* + v) from a small ball of T into P_{(m−1)L} has F(0) = 0 and a surjective derivative at 0, so by the open mapping theorem of [2] its image contains a ball around 0 in P_{(m−1)L}. That ball lies in g(Δ), and scaling by α covers P_{(m−1)L}.

The construction of [1, Lemma 6] uses a point y with y_1 = … = y_{m−1}, where the multipliers sum to zero; on the circle above all m − 1 multipliers are independent, which gives the extra factor L.

## Check

`sim/exact.py`, output in `sim/out_exact.txt`. For m = 3, …, 6 and L = 1, 2, 3 it checks in exact arithmetic that G has degree m − 1 and is constant on the curve, that its gradient there is the list of multipliers above, and that the products M_j p, with p in the basis of P_L, have rank 2(m − 1)L + 1 = dim P_{(m−1)L}.

`sim/newton.py` solves g(y* + v) = p with v ∈ T by repeated linearization (least-squares steps with the derivative) for a random small p ∈ P_{(m−1)L}, for m = 3, …, 6 and L = 1, 2, 3, with residual below 10⁻⁹ and y* + v > 0 on a fine grid, so it checks P_{(m−1)L} ⊆ H_g directly.

`sim/rank.py` repeats the rank test numerically for a random ellipse and a random G constant on it, for m = 3, …, 7 and L ∈ {1, 2, 3, 5}.

## Lean

`lean/PhotonThreshold/Basic.lean` proves that the quadratic part is constant on the circle (`quad_on_circle`), that T_k(cos θ) = cos kθ for the multipliers (`multiplier_cos`), the two product formulas (`cos_mul_cos`, `cos_mul_sin`), and that every f with 2L < f ≤ (m − 1)L is kL + ω with 2 ≤ k ≤ m − 2, 1 ≤ ω ≤ L and kL − ω < f (`freq_decomp`). `lean/axioms.txt` lists the axioms of every named theorem: only standard axioms. Not formalized: the span argument as a statement about P_{(m−1)L}, and the open mapping step of [1, Lemma 6].

## Scope

- Proposition 1 is about the hypothesis space of [1], with the realizability of every y ∈ Δ and every g as in [1, Theorem 1]. The open mapping step is that of [1, Lemma 6].
- The gap of at most ⌊(m − 1)/2⌋ in N, between the construction and the dimension bound, stays open.
- Proposition 1 for general m is a Claim with the written proof above. It is checked in exact arithmetic for m ≤ 6, L ≤ 3, and numerically for m = 7, L ≤ 5.

## References

1. Z. Xiao, W. Shi, Y. Wang, L. Lao, J. Wu. Expressive power and limitations of multi-photon quantum neural networks. arXiv:2608.01365 (2026).
2. H. J. Sussmann. High-order open mapping theorems. In: Directions in Mathematical Systems Theory and Optimization, Springer, 2003, pp. 293-316.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
