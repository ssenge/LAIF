# A smaller row constant for bounded functions of low degree

Written 11 Nov 2026.

## Problem

For f : {−1, 1}ⁿ → [−1, 1] and a point x, a *row* of f at x is a vector a ∈ [0, ∞)ⁿ with |f(x) − f(x^S)| ≤ a(S) = Σ_{i∈S} a_i for every S ⊆ [n], where x^S is x with the signs on S changed. Its cost is ‖a‖₁ [1, Definition 2.3]. Reference [1] proves the influence conjecture for bounded low-degree functions, with the row bound as one of its two inputs. A number c is called *admissible* if every f : {−1, 1}ⁿ → [−1, 1] of degree at most d has, at every point, a row of cost at most c d², for all n and d. Reference [1, Sec. 9.5] asks:

> "The row bound. Let c∗ be the infimum of the admissible numbers of Section 9.4, so that 2 ≤ c∗ ≤ π²/2. What is the value of c∗?"

The upper bound π²/2 comes from the bound fbs(f) ≤ (π²/4) deg(f)² for the fractional block sensitivity of bounded functions [2, Theorem 3.3], [1, Remark 6.9]. The lower bound 2 comes from a symmetric example [1, Sec. 9.4].

## Result

- **Theorem 1.** c∗ ≤ 3.4454. Equivalently, every f : {−1, 1}ⁿ → [−1, 1] satisfies fbs(f) ≤ 1.7227 deg(f)², against the previous best bound (π²/4) deg(f)² ≈ 2.4674 deg(f)² [2].
- **Theorem 2 (reduction).** Let m(N) be the least degree of a real polynomial p with p(0) = 1, p(1) = −1 and |p(j)| ≤ 1 at the integers j = 0, 1, …, N. Then c∗ ≤ 2 liminf_{N→∞} m(N)²/N.
- **Proposition 3 (construction).** Let Φ(s) = a cos(τs) + Ψ(s), where Ψ is a finite sum of shifted squared sinc functions with frequencies in [−τ, τ]. If Φ satisfies the inequalities (★) below, then m(N) ≤ τ√N/2 for all large N. The script `sim/cert.py` checks (★) for τ = 2.625 in 50-digit decimal arithmetic, so c∗ ≤ τ²/2 = 3.4453.

The reduction is the composition argument of [2] and [1, Lemmas 6.4 and 6.5]. The only change is that the polynomial needs to be bounded at the integers and not on a whole interval: the number of flipped blocks through a coordinate is always an integer. The bound of [2] uses the polynomial T_m(1 − 2(1 − cos(π/m))x), where T_m(cos t) = cos(mt). That polynomial is bounded on the whole interval [0, 2/(1 − cos(π/m))], which gives m(N)²/N → π²/4. A polynomial that is bounded only at the integers can overshoot between 1 and 2, and near N, and then N can be about 0.582 m² instead of about 0.405 m².

In [1, Theorem 1.4] the row bound enters through K. With K = 3.4454 d² and the bound L(f) ≤ 2d² of [3], the constant of [1, Theorem 1.1] becomes √15/(250 · 3.4454²) ≈ 1.30 · 10⁻³, so Inf_j(f) ≥ 1.30 · 10⁻³ Var(f)^{5/2}/d⁶ for some coordinate j. With the bounds of [2] and [3] the constant is about 6.36 · 10⁻⁴ [1, remarks after Theorem 1.1].

**Scope.** For this composition the constant cannot go much lower. Every polynomial with p(0) = 1, p(1) = −1, bounded at the integers 0, …, N, gives a bounded symmetric function on N bits that changes by 2 in every coordinate at one point, so N ≤ m² by [3]. Numerically, N_max(m)/m² levels off at 0.582 (table below), so the method gives at best about 2/0.582 ≈ 3.435. Whether c∗ = 2 stays open. As a check in small cases: for n ≤ 5 and every d, the largest minimal row cost over all f is attained with blocks of size one, where [3] gives at most 2d².

## Proofs

Write Q_k = {−1, 1}^k, 1 = (1, …, 1), and 1^b for 1 with the bth sign changed.

**Lemma A [3, Theorem 3.3].** If G : Q_k → [−1, 1] has degree at most D, then Σ_b |G(1) − G(1^b)| ≤ 2D².

**Lemma B.** Let f : Qₙ → [−1, 1] have degree at most d, let x ∈ Qₙ, and let S_1, …, S_k ⊆ [n] be a list of blocks in which every coordinate lies in at most N blocks. Let p have degree m with p(0) = 1, p(1) = −1 and |p(j)| ≤ 1 for j = 0, …, N. Then Σ_b |f(x) − f(x^{S_b})| ≤ 2d²m².

*Proof.* This is [1, Lemma 6.4] with T_m(1 − c·) replaced by p. For w ∈ Q_k let cnt_i(w) = Σ_{b: i∈S_b} (1 − w_b)/2 be the number of flipped blocks through i, and θ_i(w) = p(cnt_i(w)). Let f̃ be the multilinear extension of f, which is bounded by 1 on [−1, 1]ⁿ [1, Lemma 6.2], and put G(w) = f̃(x_1θ_1(w), …, x_nθ_n(w)).
- On Q_k, cnt_i(w) is an integer in [0, N], so |θ_i(w)| ≤ 1 and |G(w)| ≤ 1.
- Each θ_i is a polynomial of degree at most m in w, and every term of f̃ has at most d factors, so G has degree at most dm.
- G(1) = f(x), since every count is 0. G(1^b) = f(x^{S_b}), since the count is 1 on S_b and 0 elsewhere.

Lemma A with D = dm gives the claim. ∎

**Proof of Theorem 2.** Fix f, x and a fractional packing κ (κ_S ≥ 0, Σ_{S∋i} κ_S ≤ 1 for every i). Put t_S = |f(x) − f(x^S)| and Λ = Σ_S κ_S t_S. For N ≥ 1 take the list in which S occurs k_S = ⌊Nκ_S⌋ times. Every coordinate lies in at most N blocks, so Lemma B gives Σ_S k_S t_S ≤ 2d²m(N)². Since Nκ_S < k_S + 1, NΛ ≤ 2d²m(N)² + C₀ with C₀ = Σ_S t_S, which does not depend on N. Divide by N and let N run through a sequence along which m(N)²/N tends to its lower limit: Λ ≤ 2d² liminf m(N)²/N. By linear programming duality [1, Proposition 6.7], f has at x a row of cost max_κ Λ. ∎

**Proof of Proposition 3.** Let K(s) = (sin(τs/2)/(τs/2))², whose frequency transform is a triangle supported on [−τ, τ]. Let Ψ(s) = Σ_k b_k [K(s − t_k) + K(s + t_k)] with 0 ≤ t_k ≤ T, put B = Σ_k |b_k|, and let Φ(s) = a cos(τs) + Ψ(s). Fix J ≥ 2 and S > T + 1, and put

M = max( max_{2≤j≤J} |Φ(√j)|, sup_{√J−1 ≤ s ≤ S} |Φ(s)|, |a| + 2B (2/(τ(S − T)))² ),  α = 2/(Φ(0) − Φ(1)),  β = 1 − αΦ(0).

The condition is

(★)  α > 0 and αM + |β| < 1.

The third entry of M bounds |Φ(s)| for s ≥ S, since |sin z/z| ≤ 1/|z|.

For N large, let c = √N/2 and m = ⌊cτ⌋, and define g(φ) = a cos(mφ) + Σ_{ℓ∈ℤ} Ψ(c(φ + 2πℓ)). By the periodization (summation) formula, the second part equals (2πc)⁻¹ Σ_k Ψ̂(k/c) e^{ikφ}. Since Ψ̂ vanishes outside [−τ, τ], only |k| ≤ cτ occur. So g is an even trigonometric polynomial of degree at most m, and q(x) = g(arccos(1 − 2x/N)) is a polynomial of degree at most m.

The integer j ∈ [0, N] corresponds to φ_j = 2 arcsin √(j/N), that is, to s_j = cφ_j = √N arcsin √(j/N). These satisfy s_j ≥ √j, and s_j → √j as N → ∞ for each fixed j.
- *Far copies.* For φ ∈ [0, π] the terms with ℓ ≠ 0 have |φ + 2πℓ| ≥ (2|ℓ| − 1)π, so they add up to at most ε_N = Σ_{ℓ≥1} 4B (2/(τ(c(2ℓ − 1)π − T)))², which tends to 0.
- *Frequency.* Since cτ − 1 < m ≤ cτ, the main part a cos(mφ) = a cos((m/c)s) differs from a cos(τs) by at most |a|s/c, which tends to 0 uniformly for s ≤ S.

Hence g(φ_0) → Φ(0), g(φ_1) → Φ(1), and g(φ_j) → Φ(√j) for 2 ≤ j ≤ J. For j > J, s_j ≥ √j > √J − 1, so |g(φ_j)| ≤ M + o(1) uniformly in j: use the second entry of M while s_j ≤ S and the third beyond. With α_N = 2/(g(φ_0) − g(φ_1)) and β_N = 1 − α_N g(φ_0), the polynomial p = α_N q + β_N has p(0) = 1, p(1) = −1, and max_{2≤j≤N} |p(j)| ≤ α_N(M + o(1)) + |β_N| → αM + |β| < 1. So m(N) ≤ ⌊τ√N/2⌋ for all large N, and liminf m(N)²/N ≤ τ²/4. ∎

**The certificate.** `sim/cert.py` chooses the coefficients by a linear program (t_k = k/8 for k = 0, …, 160, so T = 20, plus J = 150 and S = 90). It then evaluates everything in 50-digit decimal arithmetic:
- sine and cosine by series after reduction modulo 2π, with an allowance of 10⁻³⁰ added to every value of Φ;
- Φ on a grid of step at most 0.02 on [√J − 1, S], with the interpolation error bounded by |Φ''| ≤ τ²|a| + (7/12)τ²B, from |(sin z/z)'| ≤ 1/2 and |(sin z/z)''| ≤ 1/3;
- the tail bound for s ≥ S.

For τ = 2.625 the results are a = 0.99808, B = 1.1563, α = 1.0000, |β| < 10⁻¹⁰ and αM + |β| = 0.99860 < 1. Hence c∗ ≤ 2.625²/2 = 3.4453 < 3.4454.

## Numbers

The largest N with a polynomial of degree m, p(0) = 1, p(1) = −1 and |p(j)| ≤ 1 for j = 0, …, N, from linear programs (`sim/jump.py`):

| m | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 10 | 20 | 40 | 60 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| N_max(m) | 1 | 3 | 6 | 10 | 15 | 21 | 38 | 58 | 233 | 932 | 2096 |
| N_max(m)/m² | 1.000 | 0.750 | 0.667 | 0.625 | 0.600 | 0.583 | 0.594 | 0.580 | 0.583 | 0.583 | 0.582 |
| bounded on the whole interval | 1.000 | 0.500 | 0.444 | 0.427 | 0.419 | 0.415 | 0.411 | 0.409 | 0.406 | 0.406 | 0.405 |

The extremal polynomials reach −1 at both x = 1 and x = 2 and dip below −1 between them. For m = 4 the extremal polynomial is p(x) = 1 + x(x − 5)²(x − 10)/72, with p + 1 = (x − 1)(x − 2)(x − 8)(x − 9)/72.

## Check

`python sim/jump.py` (about one minute), `python sim/cert.py 2.625` (a few seconds) and `python sim/exact.py 5` (about four minutes; exact maximum of the minimal row cost over all f for n ≤ 5, by enumerating the vertices of the packing polytope). The output is in `sim/out.txt`. They need numpy and scipy.

## References

1. D. Turturean. A proof of the Aaronson–Ambainis conjecture. arXiv:2611.09773 (2026).
2. A. Agarwal, S. Ben-David. Oracle separations for the quantum-classical polynomial hierarchy. arXiv:2410.19062 (2024); ITCS 2026.
3. Y. Filmus, H. Hatami, N. Keller, N. Lifshitz. On the sum of the L1 influences of bounded functions. Israel J. Math. 214, 167–192 (2016); arXiv:1404.3396.
