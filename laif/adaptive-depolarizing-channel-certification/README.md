# Adaptive certification of the completely depolarizing channel needs Ω(d_in² d_out^{3/2}/ε²) channel uses

26 November 2026. Status: **Claim** (written proof below; the identities used in it are checked by script).

## Problem

An unknown quantum channel N maps d_in × d_in matrices to d_out × d_out matrices. The tester must decide
whether N equals the completely depolarizing channel 𝒟(ρ) = Tr(ρ) I/d_out or satisfies ‖N − 𝒟‖_⋄ ≥ ε,
with success probability at least 2/3 in both cases. An *incoherent* strategy uses the channel once per step:
it prepares an input state ρ_t, on C^{d_in} (*ancilla-free*) or on C^{d_in} ⊗ C^k with an ancilla
(*ancilla-assisted*), applies N (to the first factor), measures, and may choose ρ_t and the measurement from all
earlier outcomes (*adaptive*).

| Strategy class | Previous best upper bound | Previous best lower bound |
|---|---|---|
| non-adaptive | O(d_in² d_out^{3/2}/ε²), ancilla-free [1, Thm 4.4] | Ω(d_in² d_out^{3/2}/(log²(d_in d_out/ε) ε²)), ancilla-assisted, for d_in ≥ 80, d_out ≥ 10, ε ≤ 1/32 [1, Thm 4.5] |
| adaptive | O(d_in² d_out^{3/2}/ε²) [1, Thm 4.4] | Ω((d_in² d_out + d_out^{3/2})/ε²), ancilla-assisted [1, Thm 4.6] |

## Results

**Theorem 1 (ancilla-free).** For 0 < ε ≤ 1/100 and d_out ≥ 10⁴, every adaptive, incoherent, ancilla-free
tester for 𝒟 against ‖N − 𝒟‖_⋄ ≥ ε uses at least

    n ≥ 5·10⁻⁹ · d_in² d_out^{3/2} / ε²

channel uses.

**Theorem 3 (ancilla-assisted).** For 0 < ε ≤ 1/100 and d_out ≥ 10⁴, every adaptive, incoherent,
ancilla-assisted tester (any ancilla dimension, chosen per step) uses at least

    n ≥ 1.5·10⁻⁹ · d_in² d_out^{3/2} / (ε² ln d_out).

For 10 ≤ d_out < 10⁴ the factor d_out^{1/2} is below 100, so [1, Thm 4.6] already gives the same order there
(for ε ≤ 1/32); this range rests on [1, Thm 4.6] and its unstated constant. Together, for d_out ≥ 10:

- ancilla-free strategies, adaptive or not: Θ(d_in² d_out^{3/2}/ε²), with [1, Thm 4.4];
- ancilla-assisted adaptive strategies: between Ω(d_in² d_out^{3/2}/(ε² log d_out)) and O(d_in² d_out^{3/2}/ε²).

For d_in = 1 the problem is mixedness testing and Theorem 1 is the bound of [2]. The alternatives used below are
ε-far already on a pure input without ancilla, so the bounds hold as well for testing in the input-wise trace
distance, where the tester of [1, Thm 4.4] also applies.

Theorem 4 below treats mixedness testing with measurements on t copies at once.

**Non-vacuity.** The alternatives below are channels (completely positive, trace preserving) with
‖N − 𝒟‖_⋄ ≥ ε, and the ancilla-free tester of [1, Thm 4.4] attains the order of Theorem 1.

## Instance

Write m = d_in, d = d_out and ε₀ = 10ε ≤ 1/10. Let H be a Hermitian Gaussian matrix with E|H_ab|² = 1/d,
G = H − (tr H/d) I, and U = {‖G‖_op ≤ 5, ‖G‖_F² ≥ d/2}. Then P(U^c) ≤ 2e^{−1.13d} + 2e^{−d²/32} + e^{−(d²−1)/36}
≤ 5e^{−1.13d} (a 1/10-net for ‖H‖_op ≤ 4.75, a Gaussian tail for tr H, and a χ² lower tail), U is symmetric
under G ↦ −G, and ‖G‖₁ ≥ ‖G‖_F²/‖G‖_op ≥ d/10 on U. Let φ be a Haar random unit vector in C^m and G be drawn
from the law of G conditioned on U. The alternative is

    N_{φ,G}(ρ) = Tr(ρ) I/d + (ε₀/d) ⟨φ|ρ|φ⟩ G.

It is trace preserving (tr G = 0), completely positive (its Choi matrix is I_m ⊗ I/d + (ε₀/d)|φ̄⟩⟨φ̄| ⊗ G ⪰ I/(2d)
as ε₀‖G‖_op ≤ 1/2), and ‖N_{φ,G} − 𝒟‖_⋄ ≥ ‖N_{φ,G}(φφ†) − I/d‖₁ = ε₀‖G‖₁/d ≥ ε.

**One step.** A randomized tester is a mixture of deterministic trees, a mixed input is the marginal of a pure
input on a larger ancilla, and refining a measurement only helps the tester. So by convexity we may take a
deterministic tree, pure inputs ψ_t ∈ C^m ⊗ C^k and rank-one measurements {ω_f ff†}_f on C^d ⊗ C^k (k = 1
without ancilla). Let ρ_B = Tr_A ψψ†, v = (⟨φ| ⊗ I)ψ ∈ C^k, so that vv† ⪯ ρ_B, and put

    q_f = ⟨f|I ⊗ ρ_B|f⟩,   w_f = (I ⊗ v†) f ∈ C^d,   c_f = ‖w_f‖²/q_f ∈ [0, 1],   x_f = w_f/‖w_f‖.

Under 𝒟 the outcome f has probability p₀(f) = ω_f q_f/d; under N_{φ,G} it has probability p₀(f)(1 + ε₀ c_f x_f†Gx_f).
Since Σ_f ω_f ff† = I,

    Σ_f ω_f w_f w_f† = a I_d,   a = ‖v‖² = ⟨φ|Tr_B ψψ†|φ⟩,                                   (1)

hence Σ_f p₀(f) c_f x_f x_f† = (a/d) I. Without ancilla, c_f = a for every outcome.

## Proof

Write ε for ε₀, P_t = x_tx_t†, and let δ = 10⁻⁵, B = δd^{3/2}/ε², α = δ^{−1/2}, A = d√B α = d^{7/4}/ε.

### Weighted adaptive mixedness testing

**Theorem 2.** Let d ≥ 10⁴ and ε ≤ 1/10. Consider an adaptive tree whose step t produces a unit vector x_t ∈ C^d
and a weight c_t ∈ [0, 1] (both functions of the transcript up to step t, and of a fixed φ), with law p₀ under the
null and step ratio 1 + εc_t x_t†Gx_t under p_G, where G has the law of the Instance (conditioned on U). Let Λ_t = E₀[c_t² P_t | past] and λ_t = inf{‖Λ′‖_op + tr Λ″ : Λ_t = Λ′ + Λ″,
Λ′, Λ″ ⪰ 0}. Assume E₀[c_t(dP_t − I) | past] = 0 and, on every path, Σ_t c_t² ≤ B + 1 and Σ_t λ_t ≤ 2B/d.
Then TV(p₀, E_G p_G) ≤ 0.109.

The proof follows the likelihood-ratio martingale of [2, Sec. 6], with the weights carried through.

**Lemma 1 (recursion).** For a sequence (c_i, x_i) let L = E Π_i (1 + εc_i x_i†G x_i), with G = H − (tr H/d)I
*not* conditioned on U. Then E[(x†Gx)(y†Gy)] = (d|⟨x,y⟩|² − 1)/d², and by the Isserlis formula L is the sum over
all matchings of Π_{pairs} ε²c_ac_b(d|⟨x_a,x_b⟩|² − 1)/d². Hence L is symmetric in its arguments and, for every i,

    L(z)/L(z^{∼i}) = 1 + (ε²c_i/d²) x_i† H(z^{∼i}) x_i,   H(w) = Σ_j c_j (dP_j − I) L(w^{∼j})/L(w).

For index sets S write L(S), H_S, K_S = Σ_{j∈S} c_j(dP_j − I) and M_S = Σ_{j∈S} c_j² dP_j.

**Lemma 2 (good event).** Under p₀, K_t = K_{[t]} and Y_t = M_{[t]} − Σ_{s≤t} dΛ_s are matrix martingales. Their
increments have E‖·‖_F² ≤ d² E[c_t² | past] = d² tr Λ_t ≤ d³λ_t, so E‖K_n‖_F², E‖Y_n‖_F² ≤ 2d²B and, by the maximal
inequality for ‖·‖_F, the event 𝒢 = {sup_t ‖K_t‖_F ≤ A, sup_t ‖Y_t‖_F ≤ A} has P₀(𝒢^c) ≤ 16/α² = 16δ. Since
‖Λ_s‖_F ≤ √d λ_s and ‖Λ_s‖_op ≤ λ_s, on 𝒢 we have ‖M_{[t]}‖_F ≤ 2√dB + A and ‖M_{[t]}‖_op ≤ 2B + A for all t.

**Lemma 3 (truncated against untruncated likelihood).** Let L̄(S) = E[1_U Π_{i∈S}(1 + u_i)], u_i = εc_i x_i†Gx_i.
If ‖K_S‖_F ≤ 2A, ‖M_S‖_op ≤ 2B + 2A and Σ_{i∈S} c_i² ≤ B + 1, then L(S) = L̄(S)(1 + η_S) with
|η_S| ≤ 6e^{−0.56d + 8.1√d}, and E Π_{i∈S}(1 + u_i)² ≤ e^{16.1√d}.

*Proof.* By Cauchy-Schwarz, |L − L̄| ≤ P(U^c)^{1/2}(E Π(1+u_i)²)^{1/2}. Since (1+u)² ≤ e^{2u+u²} and
Σu_i = (ε/d)⟨G, K_S⟩ (trace zero), E Π(1+u_i)² ≤ (E e^{4Σu_i})^{1/2}(E e^{2Σu_i²})^{1/2}. Here ⟨G,K⟩ = ⟨H,K⟩ is
Gaussian with variance ‖K‖_F²/d, so E e^{4Σu_i} = e^{8ε²‖K_S‖_F²/d³} ≤ e^{32√d}. For the second factor, the map
G ↦ e^{2ε²Σc_i²⟨P_i,G⟩²} is convex and H = G + (tr H/d)I with tr H independent of G, so by Jensen the expectation
is at most the same expectation over H. In an orthonormal basis of Hermitian matrices H has independent N(0, 1/d)
coordinates, and the quadratic form Σc_i²⟨P_i,·⟩² has trace Σc_i² ≤ B + 1 and largest eigenvalue at most
‖Σc_i²P_i‖_op = ‖M_S‖_op/d. Since 4ε²(2B + 2A)/d² ≤ 8δd^{−1/2} + 8εd^{−1/4} ≤ 1/2, the expectation is at most
e^{4ε²(B+1)/d}. Together E Π(1+u_i)² ≤ e^{16√d + 2.1δ√d}. For the lower bound on L̄, let ν be the law of G
conditioned on U. On U every factor lies in [1/2, 3/2], E_ν u_i = 0 by symmetry, and log(1+u) ≥ u − u² for
|u| ≤ 1/2, so Jensen gives L̄ ≥ P(U) exp(−Σ E_ν u_i²) ≥ P(U) e^{−2.1ε²B/d} ≥ ½ e^{−2.1δ√d}, using
E(x†Gx)² = (d−1)/d². With P(U^c)^{1/2} ≤ 3e^{−0.56d} the claim follows. ∎

This comparison hints at a possible gap in the ratio step of [2, Lemma 6.13], where the range [1/2, 3/2] of the
factors, valid for G ∈ U, is applied to the untruncated likelihood. Lemmas 3 and 4 give that step here.

**Lemma 4 (one removed index).** Let the conditions of 𝒢 hold at time t, D = ⌈ln(4 + d^{1/4})⌉, R ⊆ [t] with
|R| ≤ D + 1, S = [t] ∖ R and i ∈ S. Then ‖K_S‖_F ≤ 1.01A, ‖M_S‖_F ≤ 2√dB + 1.01A, ‖M_S‖_op ≤ 2B + 1.01A, and
r_i := L(S∖i)/L(S) satisfies |r_i − 1| ≤ 11εc_i.

*Proof.* ‖dP_j − I‖_F, ‖dP_j‖_F ≤ d, and d(D+2) ≤ 0.01A as A/d = d^{3/4}/ε ≥ 100(D+2) for d ≥ 10⁴, so Lemma 3
applies to S and S∖i (at most D + 2 indices removed). Write r_i − 1 = −Y_i/L(S) with Y_i = L(S) − L(S∖i) = E[Π_{S∖i}(1+u_j) u_i]. On U the
factors are positive and |u_i| ≤ 5εc_i, so |E[1_U Π_{S∖i}(1+u_j)u_i]| ≤ 5εc_i L̄(S∖i) ≤ 10εc_i L̄(S). By Hölder
with exponents 4, 2, 4, |E[1_{U^c} Π_{S∖i}(1+u_j)u_i]| ≤ P(U^c)^{1/4} e^{8.1√d} (E u_i⁴)^{1/4}, and
(E u_i⁴)^{1/4} ≤ 3^{1/4}εc_i/√d since x†Gx is Gaussian with variance below 1/d. Dividing by
L(S) ≥ L̄(S)/1.01 ≥ ½e^{−2.1δ√d}/1.01 gives |r_i − 1| ≤ εc_i(10.2 + 5e^{−0.28d + 8.2√d}) ≤ 11εc_i. ∎

**Lemma 5 (bootstrap).** If the conditions of 𝒢 hold at time t, then ‖H_{[t]}‖_F ≤ 3A.

*Proof.* For positive semidefinite P_j and |b_j| ≤ 1, ‖Σ b_jP_j‖_F ≤ ‖Σ P_j‖_F, since the pairwise inner products
are nonnegative. Hence ‖Σ_{j∈S} b_j c_j²(dP_j − I)‖_F ≤ ‖M_S‖_F + √d Σc_j² ≤ 1.01A + 3.1√dB =: Q. With
H_S = K_S + Σ_{j∈S} c_j(r_j − 1)(dP_j − I) and Lemma 4, for every S with |R| ≤ D,

    ‖H_S‖_F ≤ 1.01A + 11εQ ≤ (2.2 + 35δd^{1/4})A =: ξ₀,

because 3.1·11ε√dB/A = 34.1δd^{1/4}. If t < D, every S ⊆ [t] misses fewer than D indices, so r_i ≤ 1 + 11εc_i ≤ 2.1
and directly ‖H‖_F ≤ 2.1dD ≤ 3A. Otherwise induct on a = 0, …, D over the sets S with |R| = D − a: suppose
‖H_{S′}‖_F ≤ ξ_{a−1} whenever |R′| = D − a + 1. For i ∈ S, Lemma 1 gives |L(S)/L(S∖i) − 1| ≤ ε²c_iξ_{a−1}/d² ≤ 1/2,
hence |r_i − 1| ≤ 2ε²c_iξ_{a−1}/d². The deviation is proportional to c_i², and

    ‖H_S − K_S‖_F ≤ (2ε²ξ_{a−1}/d²) Q ≤ (2.02εd^{−1/4} + 6.2δ) ξ_{a−1} ≤ ξ_{a−1}/e.

So ξ_a = 1.01A + ξ_{a−1}/e, and ξ_D ≤ 1.6A + e^{−D}ξ₀ ≤ 3A by the choice of D. The case a = D is S = [t]. ∎

The weights are the point of Lemmas 4 and 5: every deviation of r_i is proportional to c_i, so only Σc_i² and
the matrix M enter, never Σc_i, which can be as large as n.

**Proof of Theorem 2.** Let Φ_t = L([t]), τ′ the first t at which the condition of 𝒢 fails, and Ψ_t = Φ_{t∧τ′}.
On {τ′ ≥ t} Lemma 3 gives Ψ_{t−1} = L([t−1]) > 0, and by Lemma 1 and the assumption
E₀[c_t(dP_t − I) | past] = 0, E[Ψ_t/Ψ_{t−1} | past] = 1, and since
(x†Hx)² ≤ x†H²x and ⟨H², Λ_t⟩ ≤ λ_t‖H‖_F²,

    E[(Ψ_t/Ψ_{t−1})² | past] ≤ 1 + ε⁴λ_t‖H_{[t−1]}‖_F²/d⁴ ≤ 1 + 9ε⁴A²λ_t/d⁴

by Lemma 5. As λ_t depends only on the past, Ψ_t² Π_{s≤t}(1 + 9ε⁴A²λ_s/d⁴)^{−1} is a supermartingale, so
E(Ψ_n − 1)² = EΨ_n² − 1 ≤ exp(9ε⁴A²·2B/d⁵) − 1 = e^{18δ} − 1 ≤ 19δ. On 𝒢 we have τ′ = ∞ and Ψ_n = L([n]). The true
likelihood ratio is L* = L̄([n])/P(U) = L([n])/((1+η)P(U)) ≥ (1 − s)/(1 + |η|) whenever also |Ψ_n − 1| ≤ s. So

    TV(p₀, E_G p_G) = E₀(1 − L*)₊ ≤ s + |η| + 16δ + 19δ/s²,

which is at most 0.109 for s = 0.0724. ∎

### Proof of Theorem 1

By convexity, TV(p₀, E_{φ,G} p_{φ,G}) ≤ E_φ TV(p₀, p_φ) with p_φ = E_G p_{φ,G}. Without ancilla, c_t = a_t =
⟨φ|ρ_t|φ⟩ depends only on the past, Λ_t = c_t² I/d and λ_t = c_t²/d. Under 𝒟 the transcript does not depend on φ,
so E_φ c_t² = (tr ρ_t² + 1)/(m(m+1)) ≤ 2/m² (fourth moment of a Haar vector).

Fix φ and let τ be the first t with Σ_{s≤t} c_s² > B. Let p̃_φ be the law in which every step t ≥ τ follows 𝒟,
that is, the tree with weights c_t 1{t < τ}; it satisfies the assumptions of Theorem 2. The two laws agree on every
leaf with τ > n, so TV(p_φ, p̃_φ) ≤ P_{p̃_φ}(τ ≤ n) ≤ P₀(τ ≤ n) + TV(p₀, p̃_φ), and

    TV(p₀, p_φ) ≤ 2 TV(p₀, p̃_φ) + P₀(τ ≤ n),   E_φ P₀(τ ≤ n) ≤ E_φ E₀ Σ_t c_t²/B ≤ 2n/(m²B).

With n ≤ 0.05 m²B the total is at most 0.218 + 0.1 < 1/3, so no tester with n uses succeeds. In terms of ε
this is n ≥ 5·10⁻⁹ m² d^{3/2}/ε². ∎

### Proof of Theorem 3

Now c_f depends on the outcome. By (1), E₀[c_t(dP_t − I) | past] = 0. Fix a step and its input ψ, and let
κ = min{1, x/m} with x = 11 ln d. Split Λ_t = Λ′ + Λ″ according to c_f ≤ κ or c_f > κ. By (1),
Λ′ = (1/d) Σ_{c_f≤κ} ω_f c_f w_fw_f† ⪯ (κa/d) I, so dλ_t ≤ κa_t + d tr Λ″_t, a quantity fixed by the past.

*Haar averages.* For a fixed outcome f, w_f = R_fφ is linear in φ, so c_f = φ†Q_fφ/q_f with Q_f ⪰ 0 and
tr Q_f = q_f. Then E_φ c_f² ≤ 2/m², E_φ c_f⁴ ≤ 24/m⁴ (φ†Qφ/q is a convex combination of |⟨u_j, φ⟩|²), and
E_φ a = 1/m. For m > x, writing φ = g/‖g‖ with g complex Gaussian, P(g†Q_fg ≥ xq_f/2) ≤ e^{−(x/4 − ln 2)}
(moment generating function at θ = 1/(2‖Q_f‖_op)) and P(‖g‖² ≤ m/2) ≤ e^{−0.193m}, so P_φ(c_f > x/m) ≤ 3e^{−0.193x}
and E_φ[c_f² 1{c_f > κ}] ≤ (24/m⁴)^{1/2}(3e^{−0.193x})^{1/2} ≤ 9e^{−x/11}/m² = 9/(m²d). For m ≤ x the part Λ″ is
empty. Since p₀(f) does not depend on φ,

    E_φ dλ_t ≤ x/m² + 9/m² = (11 ln d + 9)/m²,   E_φ E₀[c_t² | past] ≤ 2/m².

Fix φ and stop: let the steps be active while Σ_{s<t} c_s² ≤ B and Σ_{s≤t} dλ_s ≤ 2B (both known before step t),
and let later steps follow 𝒟. The active part satisfies Σc² ≤ B + 1 and Σλ ≤ 2B/d, so Theorem 2 applies, and as
before TV(p₀, p_φ) ≤ 2·0.109 + P₀(stop), with

    E_φ P₀(stop) ≤ 2n/(m²B) + n(11 ln d + 9)/(2m²B) ≤ 6.21 n ln d/(m²B)

for d ≥ 10⁴. With n ≤ 0.015 m²B/ln d the total is at most 0.218 + 0.094 < 1/3, that is,
n ≥ 1.5·10⁻⁹ m² d^{3/2}/(ε² ln d). ∎

## Mixedness testing with t-copy measurements

Here an unknown state ρ on C^d is given as n copies, and each measurement acts jointly on at most t of them (an
arbitrary POVM on (C^d)^{⊗t'}, t' ≤ t), chosen adaptively from earlier outcomes. The task is ρ = I/d against
‖ρ − I/d‖₁ ≥ ε.

| | Previous best upper bound | Previous best lower bound |
|---|---|---|
| non-adaptive | O(d^{3/2}/ε²) for every t (single-copy measurements); O(max{d²/(√t ε²), d/ε²}) [3, Thm 1.3] | Ω(max{d^{3/2}/(t^{1/4}ε²), d/ε²}) for ε ≤ O(1/(d^{3/2}t^{7/4})) [3, Thm 1.2] |
| adaptive | as above | Ω(d^{4/3}/(tε²)) for t ≤ O(min{d^{2/3}, √d/ε, 1/ε²}) [4]; Ω(d/ε²) [5] |

**Theorem 4.** Let d ≥ 10⁴, t ≥ 1 and 0 < ε ≤ 0.07 t^{−1} d^{−3/4}. Every adaptive tester with measurements on at
most t copies each uses at least

    n ≥ 10⁻⁷ · d^{3/2} / (t ε²)

copies. For t = O(1) this gives Θ(d^{3/2}/ε²) together with the upper bound above. In the range of ε where both
apply, it improves the adaptive bound of [4] by a factor d^{1/6}; it is above Ω(d/ε²) for t ≤ 10⁻⁷√d, and it leaves
a factor t to the upper bound O(d^{3/2}/ε²).

*Proof.* Take ρ_G = (I + ε₀G)/d with ε₀ = 10ε and G as in the Instance; then ‖ρ_G − I/d‖₁ = ε₀‖G‖₁/d ≥ ε. As before
we may take rank-one POVMs {ω_f ff†} on (C^d)^{⊗t'}. Under I/d an outcome has probability p₀(f) = ω_f/d^{t'}, under ρ_G
it has probability p₀(f) r_f(G) with r_f(G) = ⟨f|(I + ε₀G)^{⊗t'}|f⟩. Let S_f = (1/t′)Σ_j Tr_{≠j} ff†, a density matrix, and
ℓ_f(G) = 1 + ε₀t′⟨G, S_f⟩, the part of r_f of first order in G. Since Σ_f ω_f ff† = I we have Σ_f p₀(f) S_f = I/d, so
Σ_f p₀(f)ℓ_f(G) = 1, and ℓ_f ≥ 1/2 as 5ε₀t ≤ 1/2. So q_G, the adaptive law with step probabilities p₀(f)ℓ_f(G), is a
law of the same tester.

*Linear part.* Write S_f = Σ_k s_k y_ky_k† in eigenvectors and split each outcome f into outcomes (f, k) with null
probability p₀(f)s_k and step ratio 1 + ε₀t (t′/t) y_k†Gy_k. This finer tree has q_G as its image, so it can only make
the two hypotheses easier to tell apart. It is a tree as in Theorem 2, with ε replaced by ε₀t ≤ 1/10, weights
c = t′/t ∈ [0, 1] fixed before each measurement, E₀[c(dP − I) | past] = c(dΣ_f p₀(f)S_f − I) = 0, Λ = c²I/d and
λ = c²/d. With Σc² ≤ Σt′/t = n/t ≤ B = δd^{3/2}/(ε₀t)², Theorem 2 gives TV(p₀, E_G q_G) ≤ 0.109.

*Higher orders.* Each ⟨f|G_J|f⟩ with G on the copies J has modulus at most ‖G‖_op^{|J|} ≤ 5^{|J|}, so with x = 5ε₀t′ ≤ 3.5·10⁻³ (by the condition on ε),
|r_f − ℓ_f| ≤ (1 + 5ε₀)^{t′} − 1 − x ≤ e^x − 1 − x ≤ 0.51x². The χ² divergence of one step is
Σ_f p₀(f)(r_f − ℓ_f)²/ℓ_f ≤ 2(0.51·25)²ε₀⁴t′⁴ ≤ 330ε₀⁴t′⁴. By the chain rule and KL ≤ χ², for every G in U,
KL(p_G ‖ q_G) ≤ 330ε₀⁴t³Σt′ = 330ε₀⁴t³n, and since TV ≤ (KL/2)^{1/2}, TV(p_G, q_G) ≤ (165ε₀⁴t³n)^{1/2}. For
n ≤ tB = 10⁻⁵d^{3/2}/(ε₀²t) this is at most 0.041 ε₀t d^{3/4} ≤ 0.029.

So TV(p₀, E_G p_G) ≤ 0.109 + 0.029 < 1/3 whenever n ≤ 10⁻⁵d^{3/2}/(ε₀²t) = 10⁻⁷d^{3/2}/(ε²t). ∎

The linear part is the statistics of an adaptive single-copy tester for the state (I + tε₀G)/d: the effects
d·p₀(f)s_k y_ky_k† form a POVM on C^d. So the bound is the single-copy bound of [2], in the form of Theorem 2, with ε
replaced by tε, and the condition on ε pays for the terms of higher order.

**Theorem 5.** There are absolute constants c, C > 0 such that for d ≥ C, 1 ≤ t ≤ d²/C and
0 < ε ≤ c t^{−3/2} d^{−3/4}, every adaptive tester with measurements on at most t copies each uses at least

    n ≥ c · d^{3/2} / (t^{1/4} ε²)

copies. This is the order of the non-adaptive bound [3, Thm 1.2], here for adaptive testers and for a wider range
of ε. The non-adaptive bound is proved in [3, Sec. 6] from the one-measurement bounds of Lemmas 6 and 7 below; the
proof of Theorem 5 combines them with the adaptive martingale of Theorem 2. It is above Ω(d/ε²) for t ≤ d²/C, and for t ≤ d it leaves a factor
t^{1/4} to the upper bound O(d^{3/2}/ε²).

Theorem 5 keeps the mixed directions S_f instead of refining them. Two facts about one measurement on t′ ≤ t copies
replace the refinement. Write S̃ = S − I/d, A_X = Σ_j X_(j) (X acting on copy j), and E₀ for the null average over
the outcome given the past.

**Lemma 6 (variance of one measurement; [3, Lemma 6.15]).** For every traceless Hermitian X, E₀⟨S̃_f, X⟩² ≤ ‖X‖_F²/(t′d).

*Proof.* ⟨S_f, X⟩ = ⟨f|A_X|f⟩/t′ and ⟨f|A_X|f⟩² ≤ ⟨f|A_X²|f⟩, so E₀⟨S̃_f, X⟩² ≤ tr(A_X²)/(t′²d^{t′}). The cross
terms of A_X² have trace (tr X)²d^{t′−2} = 0, so tr(A_X²) = t′d^{t′−1}‖X‖_F². ∎

**Lemma 7 (average purity; [3, Lemma 6.13 and Claim 6.14]).** E₀‖S_f‖_F² ≤ μ_{t′}/t′, where μ_{t′} is the mean length of a longest weakly
increasing subsequence of a uniformly random word in {1, …, d}^{t′}, and μ_{t′} ≤ μ := 2e√t + 4e²t/d + 1.

*Proof.* R_f = t′S_f has entries (R_f)_{ba} = ⟨f|J_{ab}|f⟩ with J_{ab} = Σ_j (|a⟩⟨b|)_(j), the action of the Lie
algebra of U(d) on (C^d)^{⊗t′}. In the decomposition (C^d)^{⊗t′} = ⊕_λ V_λ ⊗ M_λ into irreducible representations
V_λ of U(d) (λ a partition of t′ with at most d parts) and multiplicity spaces M_λ, every J_{ab} is block diagonal and
acts on V_λ only. So R_f = Σ_λ p_λ R_λ, with p_λ = ⟨f|Π_λ|f⟩ and R_λ the matrix of the normalized component of f.
In an eigenbasis of R_λ its diagonal is a convex combination of weights of V_λ, all of which are majorized by λ, so
‖R_λ‖_F² ≤ Σ_iλ_i² ≤ t′λ₁. By convexity ‖R_f‖_F² ≤ Σ_λ p_λ t′λ₁, and averaging over the outcome,
Σ_f (ω_f/d^{t′}) p_λ = tr Π_λ/d^{t′}. This is the shape distribution of a uniformly random word under row insertion,
and λ₁ is the length of a longest weakly increasing subsequence, by the classical theorem of Schensted. Hence
E₀‖R_f‖_F² ≤ t′μ_{t′}. Finally P(λ₁ ≥ k) ≤ C(t,k)C(d+k−1,k)d^{−k} ≤ (e²t/k² + e²t/(dk))^k ≤ 2^{−k} for
k ≥ 2e√t + 4e²t/d, which gives the bound on μ. ∎

*Proof of Theorem 5.* Use the linear model q_G of Theorem 4 with ε = ε₀t, weights c = t′/t and mixed directions S_f.
Lemma 1 holds verbatim with x_i†Gx_i replaced by ⟨G, S_i⟩: the covariance is (d⟨S_a, S_b⟩ − 1)/d², and

    L(z)/L(z^{∼i}) = 1 + (ε²c_i/d²) ⟨S̃_i, H(z^{∼i})⟩,   H(w) = Σ_j c_j d S̃_j L(w^{∼j})/L(w).

Let Γ_T = Σ_{j∈T} c_j² |S̃_j⟩⟨S̃_j|, an operator on the real space of traceless Hermitian matrices, on which G is a
Gaussian vector with covariance I/d. Let N be the largest number of copies considered, P̄ = Nμ/t², γ̄ = N/(t²d),
A = dα√P̄ and g = 2γ̄ + 8 ln(d²/δ). By Lemma 7 the predictable compensator of tr Γ is at most P̄ and E‖K_t‖_F² ≤ d²P̄;
by Lemma 6 the compensator of Γ is at most γ̄ I, and its increments have norm at most 1. The good event 𝒢 asks,
for all t, ‖K_t‖_F ≤ A, ‖Γ_t‖_op ≤ g and tr Γ_t ≤ P̄/δ. By the maximal inequality, the matrix Freedman inequality (in
dimension d²) and Markov's inequality, P₀(𝒢^c) ≤ 3δ. On 𝒢 the steps of Lemmas 3 to 5 go through with these
replacements:

- Lemma 3: Σu_i = (ε/d)⟨G, K⟩ as before, and Σu_i² = ε²⟨G, ΓG⟩, so E e^{2Σu_i²} ≤ exp(4ε² tr Γ/d) when
  4ε²‖Γ‖_op/d ≤ 1/2. All exponents are O(ε₀²Nμ/(δd) + α²ε₀²Nμ/d) = O((μd)^{1/2}), below 0.1d for t ≤ d²/C.
- Lemma 4: unchanged, |r_i − 1| ≤ 11εc_i.
- Lemma 5: H_S − K_S = Σ_j c_j(r_j − 1) d S̃_j, and for any coefficients b, ‖Σ_j c_j b_j S̃_j‖_F ≤ ‖Γ_S‖^{1/2}‖b‖₂.
  The first stage gives ‖H_S‖_F ≤ ξ₀ = 1.01A + 11εd(gN)^{1/2}. In each later stage |r_j − 1| ≤ 2ε²c_j|⟨S̃_j, H′_j⟩|/d²
  with H′_j = H_{S∖j}, so |r_j − 1| ≤ 2ε²c_j‖S̃_j‖_F ξ/d², ‖b‖₂ ≤ (2ε²ξ/d²)(tr Γ_S)^{1/2} and
  ‖H_S − K_S‖_F ≤ (2ε²/d)(‖Γ_S‖_op tr Γ_S)^{1/2} ξ. On 𝒢 this factor is at most (2ε²/d)(gP̄/δ)^{1/2}; the part 2γ̄ of g
  gives exactly 2(2δ)^{1/2}, since ε⁴γ̄P̄/(δd²) = δ for N = δd^{3/2}/(ε₀²√μ), and the part 8 ln(d²/δ) is O(ln d/d²).
  So the factor is below 1/e. With D = ⌈ln(4 + ξ₀/A)⌉ = O(ln(d/ε)) stages, ‖H‖_F ≤ 3A.

By Lemma 6 the supermartingale step becomes E[(Ψ_t/Ψ_{t−1})² | past] ≤ 1 + 9ε⁴c²A²/(t′d⁵), and the product over all
measurements is at most exp(9ε₀⁴t²A²N/d⁵) = exp(9α²ε₀⁴μN²/d³). For N = δd^{3/2}/(ε₀²√μ) this is e^{9δ}, and the
end of the proof of Theorem 2 gives TV(p₀, E_G q_G) ≤ 0.11. The higher-order terms cost
TV ≤ (165ε₀⁴t³N)^{1/2} = O(ε₀ t^{3/2} d^{3/4}), as in Theorem 4. ∎

## Check

`sim/check.py` (one core, under a minute) checks the covariance identity, the weighted matching formula and the
recursion of Lemma 1 against Monte Carlo and exact evaluation, the Haar fourth moment, that the alternatives are
channels with ‖N − 𝒟‖_⋄ ≥ ε and step ratio 1 + ε₀c x†Gx, and, for random entangled inputs and measurements with
an ancilla, identity (1), the bound Λ′ ⪯ (κa/d)I, the Haar averages of c_f, and the Haar tail
P(c_f > x/m) ≤ 3e^{−0.193x} and E[c_f² 1{c_f > x/m}] ≤ 9e^{−x/11}/m² by Monte Carlo for rank-one and rank-three Q_f, and, for random bases of (C^d)^{⊗t}, the identity Σ_f p₀(f)S_f = I/d,
the refinement of Theorem 4 and its bounds on |r_f − ℓ_f| and on χ². Output in `sim/out_check.txt`.
`sim/tcopy_schurweyl.py` computes the bound of Lemma 7 exactly for small d, t and checks the bound on μ by Monte
Carlo; `sim/tcopy_purity_sdp.py` computes the semidefinite relaxation of the largest average purity
(X ⪰ 0 on two replicas, Tr₂X = I), which equals the bound of Lemma 7 for (d, t) = (2, 2), (3, 2), (2, 3).
`sim/constants_iv.py` recomputes the final bounds of Theorems 1 to 3 in interval arithmetic with outward rounding
and asserts them (output in `sim/out_constants_iv.txt`).

## Scope

- Theorem 4 holds for ε ≤ 0.07 t^{−1} d^{−3/4} and has a factor 1/t that the upper bound does not have.
- Theorem 5 is stated with absolute constants that are not computed; for t ≤ d it leaves a factor t^{1/4} to the upper bound.
  A sharper bound E λ₁ ≤ t/d + 2√t is used in [3]; the cruder μ of Lemma 7 changes only constants.
- Theorem 3 has a factor ln d_out that Theorem 1 does not have; it comes from the outcomes with large weight in
  the ancilla-assisted case.
- The constants are far from optimal.
- Not formalized in Lean.

## References

1. O. Fawzi, N. Flammarion, A. Garivier, A. Oufkir. Quantum channel certification with incoherent strategies.
   COLT 2023, arXiv:2303.01188.
2. S. Chen, B. Huang, J. Li, A. Liu. Tight bounds for quantum state certification with incoherent measurements.
   FOCS 2022, arXiv:2204.07155.
3. C. Wadhwa, S. Chen. Optimal quantum state testing even with limited entanglement. arXiv:2604.07460.
4. S. Chen, J. Cotler, H.-Y. Huang, J. Li. A hierarchy for replica quantum advantage. arXiv:2111.05874.
5. R. O'Donnell, J. Wright. Quantum spectrum testing. STOC 2015.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
