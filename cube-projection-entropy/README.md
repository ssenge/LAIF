# Entropy of cube projections: equal weights are optimal for n = 2, n = 3 and every n ≥ 7

Written 11 Nov 2026.

## Problem

Let U₁, …, Uₙ be independent and uniform on [−1, 1]. Among all a ∈ Rⁿ with Σ aᵢ² = 1, which direction maximizes the differential entropy h(Σ aᵢUᵢ)? The conjecture of [3, Question 9], also asked in [2, Question 3] and [4, Section 6], is that the maximum is at |aᵢ| = 1/√n for all i. Reference [1] proves it for every n ≥ 150, with equality only at equal magnitudes [1, Theorem 1.1].

## Result

**Theorem.** For n = 2, for n = 3 and for every 7 ≤ n ≤ 149, equal magnitudes maximize the entropy, and only they do. Together with [1] for n ≥ 150, the conjecture holds for n = 2, n = 3 and every n ≥ 7. As far as we know, n = 4, 5, 6 remain open.

(For n = 1 there is nothing to prove.)

## Proof

**The reduction of [1] works from n = 5.** Let qₙ be the density of n^{−1/2} Σ Uᵢ. Reference [1, Proposition 2.2] proves the theorem for n whenever

(log qₙ)'''(x) ≤ 0 for every x ∈ (0, √n). (∗)

This is the criterion of [2, Section 8.3.1]. The proof of [1, Proposition 2.2] uses n ≥ 150 in one place only: to make V = −log qₙ three times continuously differentiable on (−√n, √n). But qₙ is n − 2 times continuously differentiable and positive there, so n ≥ 5 is enough. The rest of that proof (averaging two coefficients [1, Lemma 2.1], the limit, and the relative-entropy step with its equality case) does not depend on n. Sections 3 and 4 of [1] prove (∗) for n ≥ 150, so it remains to check (∗) for 7 ≤ n ≤ 149.

**(∗) for 7 ≤ n ≤ 149, exactly.** After the change of variable s = (x√n + n)/2, (log qₙ)'''(x) = (√n/2)³ (log f)'''(s), so (∗) says that (log f)''' ≤ 0 on (n/2, n). We prove the strict inequality. Here f is the density of a sum of n independent uniforms on [0, 1]. On each piece s = j + t with 0 ≤ t ≤ 1, (n − 1)! f equals the integer polynomial

F_j(t) = Σ_{k ≤ j} (−1)^k C(n, k) (t + j − k)^{n−1},

and (log f)''' = N/F³ with N = F'''F² − 3FF'F'' + 2F'³. So (∗) on that piece says that the integer polynomial N, of degree at most 3n − 6, is negative on the part of [0, 1] in (n/2, n). The script checks this in exact integer arithmetic:
- The last piece [n − 1, n] needs no computation. There f is proportional to (n − s)^{n−1}, and (log f)''' = −2(n − 1)/(n − s)³ < 0.
- The centre s = n/2 lies on the piece j = ⌊n/2⌋, at t = 0 for even n and at t = 1/2 for odd n. Since log f is even about n/2, N vanishes at the centre. The script checks that N vanishes there and divides out one factor exactly; for odd n it first substitutes t = (1 + u)/2. The zero is simple, since the quotient is shown to be negative at the centre.
- The polynomial left on each piece, of degree D, is written in the basis C(D, i) tⁱ(1 − t)^{D−i} of [0, 1]. These basis polynomials are nonnegative on [0, 1] and sum to 1, so a polynomial whose coefficients in this basis are all negative is negative on [0, 1]. Where some coefficient is not negative, the script halves the interval by exact corner cutting and tries again on both halves. All coefficients are kept as integers.

Every piece of every n from 7 to 149 passes. As a control, the same test fails for n = 4, 5, 6, where (∗) is indeed false: exact evaluation gives N > 0 at rational points of (n/2, n), for instance s = n/2 + 1/100 for n = 4, 6 and s = 3 + 1/100 for n = 5. For n = 4, f is only twice continuously differentiable, so (∗) cannot be used there in any case.

**n = 3.** Here (∗) fails, so a different route is used. Let f be the density of the sum of three independent uniforms on [0, 1], so f(s) = s²/2 on [0, 1], f(s) = (s − r₁)(r₂ − s) on [1, 2] with r₁,₂ = (3 ∓ √3)/2, and f(s) = (3 − s)²/2 on [2, 3]. Let φ = −log f, which is convex because f is log-concave. For S = Σ aᵢUᵢ put c = (√3/2)a, so that |c|² = 3/4 and (√3 S + 3)/2 = 3/2 + c·U. The cross-entropy inequality gives

h(S) ≤ E[−log q₃(S)] = K(c) − log(√3/2), K(c) = E[φ(3/2 + c·U)],

with equality at c = e = (1/2, 1/2, 1/2), where S has density q₃. Here Σ cᵢ < 3/2 for every c ≠ e with |c|² = 3/4 and cᵢ ≥ 0, so 3/2 + c·U stays inside (0, 3) and K is finite. By symmetry it suffices to show K(c) < K(e) for every other c with |c|² = 3/4 and c₁ ≥ c₂ ≥ c₃ ≥ 0.

- *Convexity.* K is convex on {Σ|cᵢ| < 3/2}, because φ is convex. A spherical triangle with vertices on the rays of v₁, v₂, v₃ is contained in the set of points λy with y in the flat triangle conv(v₁, v₂, v₃) and λ between R/max|vᵢ| and R/h, where R = √3/2 and h is the distance of the plane of the flat triangle from 0. So the spherical triangle lies in the convex hull of the six points λvᵢ with λ at these two ends, and K on it is at most the largest of the six values.
- *Values.* With bₑ = 3/2 − ε·c, K(c) = Σ_ε (ε₁ε₂ε₃) Ψ(bₑ)/(16c₁c₂c₃), where Ψ(b) = ∫_b^3 (s − b)² φ(s) ds has a closed form in logarithms. If only m coordinates are nonzero, the same formula holds with m signs, the power m − 1 in place of 2 in Ψ, and the factor (m − 1)! 2^m times the product of the nonzero cᵢ in place of 16c₁c₂c₃.
- *Near e.* Integration by parts gives Σ cᵢ ∂K/∂cᵢ = E[(σ − 3/2) φ′(σ)] = 1 at c = e (σ = 3/2 + e·U), so the gradient at e is (2/3)(1, 1, 1). By symmetry the matrix of second derivatives at e is αI + β11ᵀ, with α = 2√3 log(2 + √3) − 10/3 ≈ 1.2287 in closed form and β = 2/3; the script uses only |β| ≤ J = 2√3 log(2 + √3), which equals E[φ″(σ)] = ∫ f′²/f. For c on the sphere with |c − e| = δ one has Σ(cᵢ − eᵢ) = −δ², so an expansion to third order along the chord from e to c gives the bound below. The expansion is valid although e is a boundary point: along the chord, g(t) = K(e + t(c − e)) has an absolutely continuous second derivative, the density bound near the ends of the support makes g′ and g″ continuous at t = 0, and |g‴(t)| grows only like δ³ log(1/(tδ²)), which is integrable. The jump terms use that the joint density of (d·U, 3/2 + ξ·U) is continuous. The result is

 K(c) − K(e) ≤ δ² (−(4/3 − α)/2 + (J/2)δ² + 3^{3/2} δ (A + B(log(1/δ)/3 + 11/36))).

 Here A = (M + 12p)/6 and B = 1/(2(1/2 − δ)³), where M = 2/(r₂ − 2)³ − 2/(2 − r₁)³ ≈ 40 bounds |φ‴| on [1, 2], the term 12p covers the jumps ±6 of φ″ at s = 1 and s = 2 with the density bound p = 1/(1 − 2δ), and B with the logarithm comes from the bound (s − s_min)²/(16 c₁c₂c₃) for the density near the ends of its support. Since 4/3 − α ≈ 0.105, the bracket is negative at δ = 3·10⁻⁴. The bracket increases with δ on (0, 3·10⁻⁴], because A + B(log(1/δ)/3 + 11/36) − B/3 > 0 there, so it is negative for every 0 < δ ≤ 3·10⁻⁴.
- *Cover.* The script splits the sector adaptively into spherical triangles. Each one either lies within distance 3·10⁻⁴ of e or passes the convexity test, with all values in interval arithmetic at 200 bits. 286 triangles pass the test, and 3 lie near e.

**n = 2.** By symmetry take a = cos θ ≥ b = sin θ ≥ 0, so θ ∈ [0, π/4]. The density of aU₁ + bU₂ is a trapezoid. It equals 1/(2a) on |x| ≤ a − b, and falls linearly to 0 on two ramps of width 2b. The flat part has mass (a − b)/a and contributes ((a − b)/a) log(2a). The ramps have mass b/a and contribute (b/a)(log(2a) + 1/2). Hence

h(aU₁ + bU₂) = log(2a) + b/(2a) = log(2 cos θ) + (tan θ)/2,

and d/dθ = −tan θ + 1/(2cos²θ) = (1 − sin 2θ)/(2cos²θ) > 0 on [0, π/4). So h increases strictly in θ, and its only maximum is θ = π/4, i.e. a = b. ∎

## Check

`python sim/cert3.py` needs mpmath and takes about 10 seconds. It checks the closed form of K and of α against numerical quadrature, the local bound and the cover for n = 3. The output is in `sim/out3.txt`.


`python sim/cert.py 4 149` uses only the standard library and takes about 3 minutes on 10 cores (`python sim/cert.py lo hi cores`). It builds the pieces F_j and checks three things for each n: f and its first n − 2 derivatives agree across the integers, the total mass is 1, and the last piece is (1 − t)^{n−1}. It then runs the test above. The output is in `sim/out.txt`.

## References

1. Z. Pang. Entropy maximization for cube projections. arXiv:2611.13533 (2026).
2. M. Bartczak, P. Nayar, S. Zwara. Sharp variance-entropy comparison for nonnegative Gaussian quadratic forms. IEEE Trans. Inform. Theory 67 (2021), 7740-7751.
3. A. Eskenazis, P. Nayar, T. Tkocz. Gaussian mixtures: entropy and geometric inequalities. Ann. Probab. 46 (2018), 2908-2945.
4. G. Chasapis, K. Gurushankar, T. Tkocz. Sharp bounds on p-norms for sums of independent uniform random variables, 0 < p < 1. J. Anal. Math. 149 (2023), 529-553.
