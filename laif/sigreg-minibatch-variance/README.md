# Noise of the minibatch SIGReg statistic: closed forms for the value and the gradient

Written 22 Nov 2026.

SIGReg, the regularizer of LeJEPA [1], pushes a batch of N embeddings in ℝ^K towards the standard normal law. It projects the batch on M random unit directions and, on each of these one-dimensional slices, computes N times the weighted squared distance between the empirical characteristic function and that of N(0, 1), a characteristic-function goodness-of-fit statistic [2, 3, 4]. Its expected value is known: N D(s) + B(s) for a slice with law N(0, s), where D is the population discrepancy and B is a bias from the finite batch ([`lejepa-linear-dynamics`](../lejepa-linear-dynamics/), Lemma 5). Closed forms for the slice average with the directions integrated out were given in [5], and the noise that random directions add to the gradient was observed in [6]. The results below give the variance of the minibatch statistic and of its gradient under the null in closed form. The noise splits into a part from the random directions, which falls like 1/M, and a part from the batch itself, which no choice of directions removes. They also give the scale that the minibatch statistic prefers in expectation.

**Setting.** A slice is X₁, …, X_N independent, φ_N(t) = (1/N) Σⱼ e^{itXⱼ}, and the statistic is

    T = N ∫ e^{−t²/2} |φ_N(t) − e^{−t²/2}|² dt,

with the weight e^{−t²/2} of the algorithm and the code of [1] and the integral over the whole line. SIGReg of a batch z₁, …, z_N ∈ ℝ^K with unit directions a₁, …, a_M is S = (1/M) Σ_m T(a_mᵀz). The null is z ∼ N(0, I_K), so that every slice is N(0, 1). Expanding the square gives the kernel form T = (1/N) Σ_{j,k} H(Xⱼ, X_k) with

    H(x, y) = √(2π) e^{−(x−y)²/2} − √π (e^{−x²/4} + e^{−y²/4}) + √(2π/3).

Under the null E H(x, Y) = 0 for every x, so T is a degenerate double-sum statistic, a sum over all ordered pairs of the batch including j = k [7, Chapter 5]. Constants used below: D″(1) = (3/2)√(2π) 3^{−5/2} ≈ 0.24120 and

- C₁ = 2π(5^{−1/2} − 2^{−1/2} + 1/3) ≈ 0.46144,
- V₁ = 4π(2^{−1/2} − 2/3) ≈ 0.50819,
- γ = (π/64)[3·2^{−5/2} − 4·2^{−3/2} + 4·2^{−1/2} − (1.5^{−3/2} − 2·1.5^{−1/2})²] ≈ 0.03727,
- η = 4π·5^{−3/2} − π√2/8 + (π/4)·2^{−3/2} ≈ 0.84629.

## Results

**Proposition 1 (one slice).** Under the null, for every N ≥ 1,

    E T = B(1) = √(2π)(1 − 3^{−1/2}) ≈ 1.0594,   Var T = 2(1 − 1/N) C₁ + V₁/N.

So the null fluctuation of T stays of order 1 for every batch size, with standard deviation near 0.96, while the population term N D(s) grows linearly in N.

**Proposition 2 (slices of one batch).** Under the null, for unit directions a, a′ with aᵀa′ = r, the statistics of the two slices of the same batch have covariance

    2(1 − 1/N) C(r) + V(r)/N,
    C(r) = 2π[(9 − 4r²)^{−1/2} − √2 (9/2 − r²/2)^{−1/2} + 1/3],   V(r) = 4π[(9/4 − r²/4)^{−1/2} − 2/3].

Here C(0) = V(0) = 0, C(1) = C₁, V(1) = V₁, and 2(1 − 1/N) C(r) + V(r)/N = (4π/27) r² + O(r⁴) for every N. For M directions drawn uniformly, E r² = 1/K for two different directions, so

    Var S = [2(1 − 1/N) C₁ + V₁/N]/M + (1 − 1/M)(4π/27)/K + O(1/K²).

The first term, about 0.923/M, comes from the random directions. The second, about 0.465/K, comes from the batch and does not depend on N. More directions help only while M is below about 2K. The statistic with the directions integrated out, as in [5], is the limit M → ∞ and keeps the second term.

**Proposition 3 (the scale direction).** Let T(s) be the statistic of the samples √s X₁, …, √s X_N with Xⱼ ∼ N(0, 1).
(a) B′(1) = √(2π) 3^{−3/2} = 2 D″(1). Hence the expected statistic N D(s) + B(s) has its minimum at s* = 1 − 2/N + O(1/N²): in expectation the minibatch statistic prefers slices with standard deviation about 1 − 1/N.
(b) The derivative of T(s) at s = 1 is a non-degenerate double-sum statistic, and Var T′(1) = 4Nγ + O(1). Against the curvature N D″(1) + B″(1) = D″(1)(N − 2), the minimizer of T(s) for a single batch therefore deviates from that of the expectation by about (4Nγ)^{1/2}/(N D″(1)) ≈ 1.60/√N in standard deviation, which exceeds the shift 2/N of (a) for every N ≥ 2.

**Proposition 4 (shape directions, to leading order in 1/K).** Let the batch move as z ↦ (I + εΔ)z with Δ symmetric, tr Δ = 0 and ‖Δ‖_F = 1, the directions be drawn uniformly and afresh for each batch, and S′ be the derivative of S at ε = 0. Under the null E S′ = 0 and, to leading order in 1/K,

    Var S′ ≈ 4η/(MK) + 32Nγ/(MK(K + 2)) + 32 D″(1)² (K² + N)/K⁴,   with 32 D″(1)² ≈ 1.862.

The first two terms come from the random directions and the last from the batch. So the directions dominate the noise of the shape gradient unless M ≳ 1.8 K³/(K² + N), that is, M ≳ 1.8K when N ≤ K². The remainder terms are not bounded; the formula agrees with simulation within 15 % for K = 16 and 32 and M from 1 to 256.

Taken together, the noise from random directions is removed by integrating them out [5, 6], but a floor of order 1/K for the value and (K² + N)/K⁴ for the shape gradient stays, set by the batch. The bias of Proposition 3(a) comes from the diagonal terms j = k of the double sum, which the unbiased estimator of [5] leaves out.

## Proofs

**Kernel form.** Expanding |φ_N − g|² with g(t) = e^{−t²/2} and using ∫ cos(tu) e^{−t²/2} dt = √(2π) e^{−u²/2}, ∫ cos(tx) e^{−t²} dt = √π e^{−x²/4} and ∫ e^{−3t²/2} dt = √(2π/3) gives H; the sine parts vanish by symmetry. With k(x, y) = √(2π) e^{−(x−y)²/2}, m(x) = E k(x, Y) = √π e^{−x²/4} and E m(X) = √(2π/3) under the null, H = k − m(x) − m(y) + E m, which is k centred at N(0, 1), so E H(x, Y) = 0.

**Proposition 1.** Split T = A + U with A = (1/N) Σⱼ H(Xⱼ, Xⱼ) and U = (1/N) Σ_{j≠k} H(Xⱼ, X_k). By degeneracy every covariance between A and U vanishes, and in Var U only the pairs {j, k} = {j′, k′} remain, so Var U = 2N(N − 1) E H(X, Y)²/N². For a centred kernel E H² = E k² − 2 E m² + (E m)² = 2π/√5 − π√2 + 2π/3 = C₁, using X − Y ∼ N(0, 2) and E e^{−aX²} = (1 + 2a)^{−1/2}. H(x, x) = √(2π) + √(2π/3) − 2√π e^{−x²/4} gives E A = B(1) and Var A = 4π Var(e^{−X²/4})/N = V₁/N.

**Proposition 2.** The two slices are jointly normal with correlation r. The same splitting gives the covariance 2(1 − 1/N) E[H(X, Y) H(X′, Y′)] + Cov(H(X, X), H(X′, X′))/N, where (X, X′) and (Y, Y′) are independent pairs with correlation r. Both expectations follow from E e^{−vᵀAv/2} = det(I + ΣA)^{−1/2} for a normal vector v with covariance Σ. For the first, E[H(X, Y) H(X′, Y′)] = E[k k′] − 2 E[k(X, Y) m(X′)] + (E m)²; the other terms vanish since E[H(X′, Y′) | X, X′] = 0. Expanding at r = 0 gives C(r) = 2π r²/27 + O(r⁴) and V(r) = 4π r²/27 + O(r⁴). For S, sum over the pairs of directions; the directions are independent of the batch, and for two independent uniform directions E r² = 1/K and E r⁴ = 3/(K(K + 2)).

**Proposition 3.** (a) From B(s) = √(2π)(1 − (2s + 1)^{−1/2}) and the closed form of D, B′(1) = √(2π) 3^{−3/2} and D″(1) = (3/2)√(2π) 3^{−5/2}, whose ratio is 2. Since D(1) = D′(1) = 0, the minimizer of N D + B satisfies N D″(1)(s − 1) + B′(1) = O((s − 1)²) + O(N(s − 1)²), so s* = 1 − 2/N + O(1/N²). (b) T′(1) = (1/N) Σ_{j,k} G(Xⱼ, X_k) with G(x, y) = ½(x∂₁H + y∂₂H)(x, y). Its projection G₁(x) = E G(x, Y) equals √π e^{−x²/4}(x²/8 − 1/4) up to a constant, computed with E[e^{−(x−Y)²/2}] = 2^{−1/2} e^{−x²/4} and the moments of the normal law. The decomposition of a double-sum statistic into projections [7, Chapter 5] gives Var T′(1) = 4N Var G₁ + O(1), and Var G₁ = γ.

**Proposition 4 (leading order).** On slice m the batch moves by ρ_m x + w with ρ_m = a_mᵀΔa_m and w independent of the slice x. The terms with one direction give 4η E|w|²/M with E|w|² = 1/K + O(1/K²), where η = E[∂₁H(X, Y)²], and 4ρ_m² Var T′(1)/M with E ρ² = 2/(K(K + 2)). For M → ∞ the derivative becomes a double-sum statistic in z with kernel Φ(z, z′) = E_a[∂₁H(aᵀz, aᵀz′) aᵀΔz]. One projection vanishes. The other is D″(1)·2zᵀΔz/(K(K + 2)) + O(K^{−3}), by integration by parts against the normal density and the expansion in orthogonal polynomials of the normal density, and gives 32N D″(1)²/K⁴. The two degenerate parts each give 4(2D″(1))²/K², from the moment formula for products of jointly normal variables with E[∂₁²H] = 0 and E[∂₁∂₂H] = 2D″(1). Terms of order K^{−3} and remainders in 1/N are not bounded.

## Scope and status

| Result | Scope | Status | Posted |
|---|---|---|---|
| Proposition 1 | Null N(0, 1), exact integral with weight e^{−t²/2}, every N | Claim; checked numerically | 2026-11-22 |
| Proposition 2 | Null N(0, I_K), any directions; the expansion in r for uniform directions | Claim; checked numerically | 2026-11-22 |
| Proposition 3 | Null, the isotropic scale direction; (b) up to O(1) in the variance | Claim; checked numerically | 2026-11-22 |
| Proposition 4 | Null, traceless shape directions, fresh uniform directions per batch, leading order in 1/K | Numerical, with a derivation to leading order | 2026-11-22 |

Not covered: the integral computed by quadrature as in the code of [1] (the constants change slightly), embeddings that are not normal, where the kernel is not degenerate and the variance grows with N, the gradient through a nonlinear encoder, and bounds on the remainders of Proposition 4.

## Simulations

Scripts in [`sim/`](sim/), run with NumPy and SciPy, with asserts, on one core.

- `null_moments.py`: the kernel form against a direct quadrature of the integral (to 10⁻⁸). The null mean at N = 16 and 128 (within 1.3 standard errors) and the variances of one slice and of the average of 8 slices with K = 32 (within 8 %, 4000 batches). The expansions of C and V at r = 0 and the cancellation of N in the 1/K term.
- `scale_noise.py`: the minimizer s* of N D + B at N = 64, 256 and 1024 (N²(s* − 1 + 2/N) between 0.99 and 1.00), the constant γ, the variance of T′(1) at N = 64 and 256 (ratios 1.02 and 0.96), and a finite-difference check of T′(1).
- `shape_noise.py`: the derivative S′ against finite differences, η and the identity E[G₁(X)(X² − 1)] = D″(1) by Monte Carlo, and the variance of S′ against Proposition 4 for K = 16 (M = 1, 8, 64, 256) and K = 32 (M = 1, 64, 256), with N = 64: ratios between 0.86 and 1.08.

## References

1. R. Balestriero, Y. LeCun. LeJEPA: provable and scalable self-supervised learning without the heuristics. arXiv:2511.08544, 2025.
2. T. W. Epps, L. B. Pulley. A test for normality based on the empirical characteristic function. Biometrika 70, 1983.
3. L. Baringhaus, N. Henze. A consistent test for multivariate normality based on the empirical characteristic function. Metrika 35, 1988.
4. N. Henze, B. Zirkler. A class of invariant consistent tests for multivariate normality. Communications in Statistics, Theory and Methods 19, 1990.
5. E. Zimmermann, H. Wiltzer, J. Szeto, D. Alvarez-Melis, L. Mackey. KerJEPA: kernel discrepancies for Euclidean self-supervised learning. arXiv:2512.19605, 2025.
6. L. Nicollier, E. Meinhardt-Llopis, M. Dunitz, M. Pic, P. Musé, G. Facciolo. Expanding SPHERE-JEPA: a family of statistical regularizers for the hypersphere. arXiv:2606.17603, 2026.
7. R. J. Serfling. Approximation Theorems of Mathematical Statistics. Wiley, 1980.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check the derivations, to write the simulation scripts, and to draft the text.
