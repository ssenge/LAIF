# Stabilizer-only data re-uploading: encoding depth O(D δ^{-1.42} polylog(D/ε)), and the lower bound Ω(D + 1/δ + log(1/ε))

2026-11-25

## Problem

The setting is the one-qubit data re-uploading model of [1, Sec. 3]:

U(x) = V_L E(x) ⋯ V_1 E(x) V_0,  f(x) = tr(Z U(x) ρ_r U(x)†),  ρ_r = (1 + rZ)/2,  0 < r ≤ 1.

Here E(x) = R_z(x) is the phase encoding on x ∈ [−1, 1], the gates V_j do not depend on x, and L, the number of encoding calls, is the encoding depth. The circuit is fixed in advance, with no measurement before the readout. Call a circuit stabilizer-only if every V_j is one of the 24 single-qubit stabilizer gates, the gates whose rotation permutes the six vectors ±e_x, ±e_y, ±e_z.

By [1, Theorem 4], stabilizer-only circuits approximate every continuous g: [−1, 1] → [−r, r] uniformly on δ ≤ |x| ≤ 1. If g is the model function of a circuit with D encoding calls and arbitrary gates, the depth is polynomial in D, 1/ε and 1/δ. The optimal depth is stated as open in [1, Sec. 7]. Their proof builds a non-stabilizer quarter-turn from a word U(x) of depth at most δ^{−4}η₁^{−2} for accuracy η₁ [1, Lemma F.1]. With η₁ = ε/(8(D + 1)N) and N gates per approximated rotation, the total is D + 128(D + 1)³N³δ^{−4}ε^{−2}.

| | encoding depth for error ε on δ ≤ \|x\| ≤ 1 |
|---|---|
| Previous best bound, implied by [1, Lemma F.1 and proof of Theorem 4] | O((D + 1)³ δ^{−4} ε^{−2} polylog((D + 1)/ε)) |
| Theorem 1 | O((D + 1) δ^{−1.4182} log^{c₀ + 3.33}((D + 1)/ε)), c₀ the exponent of gate-set approximation [2] |
| Theorem 2, every stabilizer-only circuit | Ω(D + 1/δ + log(1/ε)) for suitable targets, ε ≤ r/4, δ ≤ 1/2 |

## Results

**Lemma 1 (a uniform non-stabilizer axis).** For δ, η ∈ (0, 1) there is a word U(x) in stabilizer gates and R_z(x) with

m(δ, η) ≤ 10^{10} · (1/δ²)^{ln 10/ln 25.72} · max{1, ln(1/η)}^{log₂ 10} = O(δ^{−1.4182} log^{3.33}(1/η))

encoding calls such that the axis n(x) of U(x) S U(x)† satisfies |n_z(x) − 1/√2| ≤ η whenever δ ≤ |x| ≤ 1. Here S = R_z(π/2).

**Theorem 1 (upper bound).** Let g be the model function of a circuit with D encoding calls and arbitrary gates, and let ε, δ ∈ (0, 1). Then there is a stabilizer-only circuit with |f(x) − g(x)| ≤ ε for δ ≤ |x| ≤ 1 and encoding depth

L ≤ D + 2(D + 1) N m(δ, η/(2N)),  η = ε/(4(D + 1)),

where N = N(η) = O(log^{c₀}(1/η)) is the length of the gate-set approximation by recursive refinement [2]. So L = O((D + 1) δ^{−1.4182} log^{c₀ + 3.33}((D + 1)/ε)).

**Theorem 2 (lower bounds).** For every stabilizer-only circuit with L encoding calls:

- (a) if |f − r/2| ≤ ε on δ ≤ |x| ≤ 1, then L ≥ (1/2 − ε/r)/δ;
- (b) if every constant target c ∈ [−r, r] has an approximation within ε by some circuit of depth L, then L ≥ log₂₄(r/ε) − 1;
- (c) if |f(x) − r cos(Dx)| < r on δ ≤ x ≤ 1, then L ≥ (⌊D(1 − δ)/π⌋ − 1)/2.

The targets r/2, c and r cos(Dx) are model functions of circuits with arbitrary gates, using D = 0, 0 and D encoding calls. A model function with D′ < D encoding calls is also one with D calls: extra encoding calls placed before V_0 act trivially, since R_z(x) commutes with ρ_r. So, for ε ≤ r/4 and δ ≤ 1/2, the optimal depth over targets with D encoding calls lies between Ω(D + 1/δ + log(1/ε)) and O((D + 1) δ^{−1.4182} polylog((D + 1)/ε)).

## Proof

**Reduction to one coordinate.** Write O(U) ∈ SO(3) for the rotation of U and n = O(U)e_z, t = n_z, so that U S U† = S_n is the quarter-turn about n. For a word W = S_n^{k_1} S^{j_1} S_n^{k_2} ⋯ S^{j_{r−1}} S_n^{k_r}, the vector O(W)e_z has a z-component G_W(t) that depends only on t. This holds because conjugation by R_z(φ) changes only the azimuth of n and commutes with S. Replacing U by W(U) multiplies the number of encoding calls by 2r, since S_n^k = U S^k U†. G_W is a polynomial with integer coefficients. The recursion of [1, Lemma F.1] is the case W = S_n S S_n², with G = t + t(1 − t)(1 − 2t²) and 4 copies.

**Two words.** `sim/maps2.py` scans all words with r ≤ 5. It keeps those with an interval T = [ℓ, 1] ⊇ [cos 1, 1] satisfying G(T) ⊆ T and G < 1 on T \ {1}, and with exactly one fixed point of G and of G∘G in T \ {1}. Two of them are used, each with 10 copies:

- A = S_n² S S_n² S³ S_n² S³ S_n S³ S_n², with G_A(t) = 16t¹⁰ + 32t⁹ − 32t⁸ − 72t⁷ + 28t⁶ + 52t⁵ − 14t⁴ − 14t³ + 3t² + 2t. It has G_A(1) = 1, G_A′(1) = 26, the fixed point 1/√2 and G_A′(1/√2) = 1 − √2.
- B = S_n S S_n² S S_n² S S_n³ S S_n, with G_B(t) = 4t¹⁰ − 16t⁸ + 4t⁷ + 21t⁶ − 10t⁵ − 7t⁴ + 6t³ − 2t² + 1. It has G_B(1/√2) = 1/√2, G_B′(1/√2) = 0 and G_B″(1/√2)/2 = 11 − 11/√2.

**Certificate.** `sim/certify.py` checks the following with outward-rounded interval arithmetic at 40 digits, for κ = 10⁻³:

1. 1 − G_A(t) = (1 − t)P_A(t) with 25.72 ≤ P_A ≤ C = 26.0001 on [1 − κ, 1], and 1 − Cκ > cos 1.
2. J_A = [t_A − 0.005, t_A + 0.005] around t_A = 1/√2 satisfies G_A(J_A) ⊆ J_A.
3. Every t ∈ [cos 1, 1 − κ] lands in J_A within 8 steps of A, using 2000 subintervals, each certified directly.
4. J_A ⊆ J_B = [1/√2 − ρ, 1/√2 + ρ] with ρ = 0.01, and |G_B″| ≤ 2M on J_B with M = 3.3274, so Mρ < 1/2. The second-order expansion with remainder about 1/√2 then gives |G_B(t) − 1/√2| ≤ M(t − 1/√2)² on J_B.

**Lemma 1.** Start from U_0 = R_y(x), a word with one encoding call, so that t_0 = cos x ∈ [cos 1, cos δ]. If 1 − t_0 < κ, each step of A multiplies 1 − t by at least 25.72 as long as t ≥ 1 − κ. Since 1 − t_0 ≥ 2δ²/5, after k_1 = max{0, ⌈ln(5κ/(2δ²))/ln 25.72⌉} steps t has left [1 − κ, 1], and it lands in [1 − Cκ, 1 − κ] ⊆ [cos 1, 1 − κ]. After 8 more steps it lies in J_A, and J_A is invariant, so one common number k_1 + 8 of A-steps works for all x. Then j steps of B give |t − 1/√2| ≤ M^{−1}(Mρ)^{2^j} ≤ η once 2^j ≥ ln(1/(Mη))/ln(1/(Mρ)). The word has 10^{k_1 + 8 + j} encoding calls. Here 10^{k_1} ≤ 10(1/δ²)^{ln 10/ln 25.72}, and, since M > 1 and ln(1/(Mρ)) > 1, the least such j has 10^j ≤ 10 max{1, ln(1/η)}^{log₂ 10}. This gives the bound.

**Theorem 1.** This is the proof of [1, Theorem 4], with the word of Lemma 1 in place of [1, Lemma F.1]. The target axis z-component is the same value 1/√2. Each V_j is approximated within η by a product of at most N quarter-turns S^{±1}, S_{n*}^{±1} with n* = (e_x + e_z)/√2, which generate a dense subgroup of SU(2) [1, proof of Theorem 4]. Every S_{n*} is replaced by U(x)SU(x)†. The common azimuth of n(x) cancels as in [1]. The accuracy η/(2N) of Lemma 1 gives the error bound of [1]. Each replaced factor costs 2m encoding calls.

**Theorem 2.** Every rotation O(V_j) and every R_z(x) contributes entries of degree at most 1 in cos x and sin x. So f is a real trigonometric polynomial of degree at most L with |f| ≤ r. At x = 0 the circuit is a stabilizer gate, so f(0) ∈ {0, ±r}.

- (a) By the derivative bound for trigonometric polynomials [3], |f′| ≤ Lr. So r/2 − ε ≤ |f(δ) − f(0)| ≤ Lrδ.
- (b) A stabilizer-only circuit of depth L is fixed by L + 1 of the 24 gates, so at most 24^{L+1} model functions exist. Each of them is within ε of the constants in a window of length at most 2ε, and these windows must cover [−r, r], so 24^{L+1} · 2ε ≥ 2r.
- (c) cos(Dx) takes the values ±1 alternately at the points kπ/D, at least ⌊D(1 − δ)/π⌋ of which lie in [δ, 1]. At these points f has the same signs, so f has at least ⌊D(1 − δ)/π⌋ − 1 zeros in [δ, 1]. A nonzero trigonometric polynomial of degree L has at most 2L zeros in a period.

The target r cos(Dx) comes from V_0 = R_y(π/2), D encoding calls and V_D = R_y(−π/2). The constant c comes from V_0 = R_y(arccos(c/r)) with D = 0.

## Check

- `sim/poly.py` derives G_A, G_B and the map of [1] exactly. It checks G_A(1) = 1, G_A′(1) = 26, G_B(1/√2) = 1/√2 and G_B′(1/√2) = 0, and that the map of [1] matches [1, Eq. (F.2)].
- `sim/certify.py`, output in `sim/out_certify.txt`, gives the certificate above.
- `sim/e2e.py`, output in `sim/out_e2e.txt`, builds the words of Lemma 1 with its step counts as 2 × 2 unitaries for 450 inputs per δ ∈ {0.2, 0.05, 0.01}, with both signs of x.
  - The axis z-component of U S U† matches the iterated polynomials.
  - After the A- and B-steps it equals 1/√2 within η = 10⁻¹² for every input (in fact within 2·10⁻¹⁵).
- `sim/lower.py`, output in `sim/out_lower.txt`, enumerates all stabilizer-only circuits with L ≤ 6 on a grid.
  - It finds 7, 17, 53, 195, 863 and 3983 distinct model functions; [1, Fig. 4] reports 863 for L = 5.
  - It confirms that the best uniform error to the target 1/2 on δ ≤ |x| ≤ 1 is at least 1/2 − Lδ for δ ∈ {0.05, 0.1, 0.2}.
- `sim/maps.py` and `sim/maps2.py` list the candidate words, output in `sim/out_maps2.txt`.

## Scope

- The exponent 1.4182 of δ comes from the best word found among the words with at most 10 copies whose attracting axis component is usable. Words with the attracting value n_z = 0 expand faster near 1 (G′(1) = 82 with 10 copies), but an equatorial axis together with S generates only a finite group, up to the common azimuth.
- The gap between the bounds is a factor of order min{D, 1/δ} δ^{−0.42} polylog((D + 1)/ε), so δ^{−0.42} polylog(1/ε) for fixed D. The constants of Lemma 1 are large, about 10^{10}.
- Theorem 1 uses the gate-set approximation of [2] with its exponent c₀, and the density argument of [1] as stated. The statements are Claims with the listed checks; the interval certificate is computer-assisted.

## References

1. O. Shaya, L. Pira. Quantum resources constrain function approximation. arXiv:2611.30789 (2026).
2. M. A. Nielsen, I. L. Chuang. Quantum Computation and Quantum Information. Cambridge University Press, 2010, Appendix 3.
3. S. N. Bernstein's inequality for trigonometric polynomials; see A. Zygmund, Trigonometric Series, Cambridge University Press.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
