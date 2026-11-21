# LeJEPA with an over-complete embedding: an exactly normal embedding pays a power of the noise level

Written 21 Nov 2026.

LeJEPA [3] trains an encoder so that the embeddings of two views of the same scene are close, while the SIGReg regularizer pushes the embedding distribution towards an isotropic normal law. In [1] it was proved that, in a normal world and with an encoder output dimension M equal to the latent dimension N, every encoder that meets both goals exactly recovers the latent variables up to an orthogonal map. What happens for M > N, the over-complete case used in practice, was stated as open in [2]. The results below answer the exact form of this question. For M > N an exactly normal embedding exists only for encoders that are not locally slope-bounded, and its alignment loss is at least of order (1 − ρ)^{N/M} instead of the order 1 − ρ reached for M = N. The bound follows from information theory and holds for every world, not only the normal one.

**Setting.** The normal world of [1, Section 3.1.1]: z ∼ N(0, I_N), and the second view is z′ = ρz + √(1 − ρ²) η with η ∼ N(0, I_N) independent of z and 0 ≤ ρ < 1. An encoder is a measurable map h : ℝ^N → ℝ^M applied to both views, and its alignment loss is

    L(h) = E ‖h(z′) − h(z)‖²,

the loss of equation (2) of [1]. Exact SIGReg means that h(z) ∼ N(0, I_M), the constraint of equation (2) of [1]. This is the case where the SIGReg statistic over all directions vanishes, since all one-dimensional projections are then standard normal. A finite set of directions with a vanishing statistic is a weaker condition and is not covered. For M = N the smallest loss under exact SIGReg is 2N(1 − ρ), attained exactly by the orthogonal maps [1, Theorem 1].

More generally, Theorem 1 uses only a pair of views (x, x′) with the same distribution and finite mutual information I = I(x; x′), measured in nats. In the normal world, I = (N/2) log 1/(1 − ρ²).

## Results

**Theorem 1 (alignment under exact SIGReg).** If h(x) ∼ N(0, I_M), then

    L(h) ≥ M e^{−2I/M}.

In the normal world, every encoder with h(z) ∼ N(0, I_M) has

    L(h) ≥ max{ M (1 − ρ²)^{N/M}, 2M(1 − ρ) }.

For M = N the first term is N(1 − ρ²), and its ratio to the optimum 2N(1 − ρ) of [1] is (1 + ρ)/2, which tends to 1 as ρ → 1.

**Corollary 2 (the over-complete gap).** For M > N, the smallest loss under exact SIGReg divided by the matched optimum 2N(1 − ρ) is at least M(1 − ρ²)^{N/M} / (2N(1 − ρ)), which grows like (1 − ρ)^{−(M−N)/M} as ρ → 1. So for M > N no encoder with an exactly normal embedding comes close to the alignment of the matched case, and the gap widens as the views become more similar.

**Proposition 3 (no slope-bounded encoder).** Call h locally slope-bounded if every point has a neighbourhood U and a constant C with ‖h(x) − h(y)‖ ≤ C‖x − y‖ for x, y in U. For M > N, no locally slope-bounded encoder, and so no neural network with slope-bounded activations, satisfies h(z) ∼ N(0, I_M). The law of h(z) is then singular with respect to volume.

**Theorem 4 (near-normal embeddings).** Suppose the law of X = h(x) has a density and E‖X‖² = M, and let K be its relative entropy with respect to N(0, I_M). Then

    K ≥ (M/2) log(M / L(h)) − I.

In the normal world, an encoder with matched-level alignment L(h) ≤ cN(1 − ρ) therefore has K ≥ ((M − N)/2) log 1/(1 − ρ) − C for a constant C that depends on M, N and c only. The theorem applies to encoders whose output has a density, for example encoders with injected noise. For a deterministic locally slope-bounded encoder with M > N the relative entropy is infinite by Proposition 3.

**Example (an exactly normal over-complete encoder).** For N = 1 and M = 2, the following space-filling map sends z ∼ N(0, 1) to N(0, I_2), up to the resolution of the curve. Fold z to s = |2Φ(z) − 1|, which is uniform on [0, 1). Then use the polar map of two independent standard normal variables, (a, b) ↦ √(−2 log(1 − a)) (cos 2πb, sin 2πb). The a-range is cut into annular bands: radii halve towards the centre, and the mass halves towards the tail. Each band of s is sent to the same band of a, and the band is filled by space-filling curves on K cells in b, with K chosen so that every cell is round after the polar map. For 1 − ρ between 10⁻¹⁰ and 10⁻⁵, the loss of this map is between 4.94 and 5.10 times the bound 2√(1 − ρ²) of Theorem 1. So, numerically, the order (1 − ρ)^{N/M} of Theorem 1 is reached with a constant of about 5. Applied to each coordinate, the same map gives M = 2N for every N, with N times the loss and the same ratio to the bound.

These results give a possible reason for the observation of [1, Appendix H.13] that encoders trained with a SIGReg penalty and M > N leave the surplus dimensions collapsed or fill them with nonlinear functions of z. By Theorem 1 and Corollary 2, an exactly normal embedding in M > N dimensions costs far more alignment than the matched case allows.

## Proofs

**Theorem 1.** Write X = h(x) and Y = h(x′). Both have the law N(0, I_M), since x and x′ have the same law. By the data processing inequality [4, Theorem 2.8.1], I(X; Y) ≤ I(x; x′) = I. By the rate distortion function of N(0, I_M) under squared error [4, Theorem 10.3.3], any pair with E‖X − Y‖² = L has I(X; Y) ≥ (M/2) log(M/L) when L ≤ M. The total distortion is L, so the distortion per coordinate is L/M. Hence (M/2) log(M/L) ≤ I, that is, L ≥ M e^{−2I/M}; for L > M this holds trivially. In the normal world, the pairs (zᵢ, z′ᵢ) are independent with correlation ρ, so I = (N/2) log 1/(1 − ρ²), which gives the first term. For the second term, let T_ρ f(z) = E f(ρz + √(1 − ρ²) η), the noise semigroup that keeps the normal law, so that E[f(z) f(z′)] = E[f(z) T_ρ f(z)]. Expanding a function f of z with mean zero in the orthogonal polynomials of the normal density, with P_d f its part of degree d, gives E[f(z) f(z′)] = Σ_{d≥1} ρ^d ‖P_d f‖² ≤ ρ Var f [5, Chapter 11]. Each coordinate of h has mean 0 and variance 1, so L = 2M − 2 Σᵢ E[hᵢ(z) hᵢ(z′)] ≥ 2M(1 − ρ).

**Proposition 3.** A slope-bounded map sends a compact subset of ℝ^N to a set of dimension at most N, which has volume 0 in ℝ^M for M > N [6]. Since ℝ^N is a countable union of compact sets, h(ℝ^N) is a set of volume 0 that carries the whole law of h(z), whereas N(0, I_M) gives it measure 0.

**Theorem 4.** For X with a density p, the differential entropy is h(X) = (M/2) log(2π) + E‖X‖²/2 − K, which is (M/2) log(2πe) − K when E‖X‖² = M. Then I(X; Y) = h(X) − h(X | Y) and h(X | Y) = h(X − Y | Y) ≤ h(X − Y) ≤ (M/2) log(2πe L/M), since among the random vectors W in ℝ^M with E‖W‖² ≤ L the entropy is largest for N(0, (L/M) I_M) [4, Theorem 8.6.5]. So I ≥ I(X; Y) ≥ (M/2) log(M/L) − K. For the normal world, insert L ≤ cN(1 − ρ) and I = (N/2) log 1/(1 − ρ²), and use 1 − ρ² ≥ 1 − ρ.

## Scope and status

| Result | Scope | Status | Posted |
|---|---|---|---|
| Theorem 1 | Exact SIGReg, h(x) ∼ N(0, I_M); any pair of views with finite mutual information; the normal world of [1] for the second statement | Claim; uses the data processing inequality and the rate distortion function of the normal law [4] and the expansion in orthogonal polynomials of the normal density [5]; checked numerically | 2026-11-21 |
| Corollary 2 | As Theorem 1, M > N | Claim | 2026-11-21 |
| Proposition 3 | Locally slope-bounded encoders, M > N | Claim; uses the behaviour of dimension under slope-bounded maps [6] | 2026-11-21 |
| Theorem 4 | Output law with a density and E‖X‖² = M | Claim | 2026-11-21 |
| Example | N = 1, M = 2 and M = 2N, 1 − ρ from 10⁻¹⁰ to 10⁻² | Numerical | 2026-11-21 |

Not covered: SIGReg with a finite set of directions, the penalized objective of LeJEPA with a finite weight, encoders with a predictor, and a proof that the ratio of the example stays bounded as ρ → 1. For ratios M/N other than 2, Theorem 1 is not matched by a construction.

## Simulations

Scripts in [`sim/`](sim/), run with NumPy and SciPy, with asserts.

- `round_rate.py`: the encoder of the example, as a fixed map with 4¹⁶ points per cell. Checks that h(z) is close to N(0, I_2) (tests on the maximum distance between distribution functions, 2 · 10⁶ samples, correlation below 0.01), that the loss is above the bound of Theorem 1 at 9 values of 1 − ρ from 10⁻¹⁰ to 10⁻², and that its ratio to the bound stays below 5.5 and varies by less than 6 % over 1 − ρ from 10⁻¹⁰ to 10⁻⁵.
- `strip_rate.py`: a variant with squares of equal side in each strip, each filled by a space-filling curve (cells that are not round after the polar map), as a fixed map with 4¹⁶ cells per square. Checks that h(z) is close to N(0, I_2) (tests on the maximum distance between distribution functions, 10⁶ samples, correlation below 0.01), that the loss is above the bound of Theorem 1 at 13 values of 1 − ρ from 10⁻⁸ to 10⁻¹, and that the fitted exponent over 1 − ρ from 10⁻⁸ to 10⁻⁵ lies within 0.08 of 1/2; its ratio to the bound grows from 8.8 to 9.4 in this range.
- `hilbert_rate.py`: the same check for the map z ↦ Φ⁻¹(H(Φ(z))) with a plain space-filling curve H of the unit square and the normal distribution function Φ. The loss is above the bound at all 9 values of 1 − ρ from 10⁻⁵ to 10⁻¹, with a fitted exponent of about 0.35 in this range.

## References

1. D. Klindt, Y. LeCun, R. Balestriero. When does LeJEPA learn a world model? arXiv:2605.26379, 2026.
2. F. Arnez, A. Gomez-Villa. The SIGReg objective as variational free energy: a theoretical active-inference account of JEPA world models. arXiv:2607.13612, 2026.
3. R. Balestriero, Y. LeCun. LeJEPA: provable and scalable self-supervised learning without the heuristics. arXiv:2511.08544, 2025.
4. T. M. Cover, J. A. Thomas. Elements of Information Theory, 2nd edition. Wiley, 2006.
5. R. O'Donnell. Analysis of Boolean Functions. Cambridge University Press, 2014.
6. L. C. Evans, R. F. Gariepy. Measure Theory and Fine Properties of Functions. CRC Press, 1992.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check the proofs, to write the simulation scripts, and to draft the text.
