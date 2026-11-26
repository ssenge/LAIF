# Adaptive certification of the completely depolarizing channel needs Ω(d_in² d_out^{3/2}/ε²) channel uses

26 November 2026. Status: **Claim** (written proof below; the identities used in it are checked by script).

## Problem

An unknown quantum channel N maps d_in × d_in matrices to d_out × d_out matrices. The tester must decide
whether N equals the completely depolarizing channel 𝒟(ρ) = Tr(ρ) I/d_out or satisfies ‖N − 𝒟‖_⋄ ≥ ε,
with success probability at least 2/3 in both cases. An *incoherent ancilla-free* strategy uses the channel
once per step: it prepares an input state ρ_t on C^{d_in}, applies N, measures the output, and may choose
ρ_t and the measurement from all earlier outcomes (adaptive).

| Strategy class | Previous best upper bound | Previous best lower bound |
|---|---|---|
| non-adaptive | O(d_in² d_out^{3/2}/ε²), ancilla-free [1, Thm 4.4] | Ω(d_in² d_out^{3/2}/(log²(d_in d_out/ε) ε²)) [1, Thm 4.5] |
| adaptive | O(d_in² d_out^{3/2}/ε²) [1, Thm 4.4] | Ω(d_in² d_out/ε²) [1, Thm 4.6]; Ω(d_out^{3/2}/ε²) implied by [2] (d_in = 1) |

## Result

**Theorem 1.** There are absolute constants c, C₀, d₀ > 0 such that the following holds for 0 < ε ≤ 1/100,
d_out ≥ d₀ and d_out ≥ C₀ ln(d_in/ε). Every adaptive, incoherent, ancilla-free tester for 𝒟 against
‖N − 𝒟‖_⋄ ≥ ε uses at least

    n ≥ c · d_in² d_out^{3/2} / ε²

channel uses. The proof gives c = 7·10⁻⁹, d₀ = 10⁴, C₀ = 100 (not optimized).

With [1, Thm 4.4] this gives Θ(d_in² d_out^{3/2}/ε²) for ancilla-free strategies, adaptive or not, and
removes the logarithmic factor of the non-adaptive lower bound for them. For d_in = 1 it is the bound of [2].
The alternatives are ε-far already on a pure input without ancilla, ‖N(φφ†) − 𝒟(φφ†)‖₁ ≥ ε, so the same bound
holds for testing in the input-wise trace distance, where the tester of [1, Thm 4.4] also applies.

**On the condition d_out ≥ C₀ ln(d_in/ε).** The proof treats trees with n ≤ e^{d_out/20} steps. This is no loss:
under the condition, c d_in² d_out^{3/2}/ε² ≤ e^{d_out/20}, so a tester below the bound has fewer than
e^{d_out/20} steps (pad it with ignored uses).

**Non-vacuity.** The alternatives below are channels (completely positive, trace preserving) with
‖N − 𝒟‖_⋄ ≥ ε, and the matching ancilla-free tester of [1, Thm 4.4] shows the bound is attained.

## Instance

Write m = d_in, d = d_out and ε₀ = 10ε ≤ 1/10. Let H be a Hermitian Gaussian matrix with E|H_ab|² = 1/d,
G = H − (tr H/d) I, and U = {‖G‖_op ≤ 5, ‖G‖_F² ≥ d/2}. Then P(U^c) ≤ 2e^{−1.13d} + 2e^{−d²/32} + e^{−(d²−1)/36}
(a 1/10-net for ‖H‖_op ≤ 4.75, a Gaussian tail for tr H, and a χ² lower tail), U is symmetric under G ↦ −G,
and ‖G‖₁ ≥ ‖G‖_F²/‖G‖_op ≥ d/10 on U. Let φ be a Haar random unit vector in C^m and G be drawn from the law of G
conditioned on U. The alternative is

    N_{φ,G}(ρ) = Tr(ρ) I/d + (ε₀/d) ⟨φ|ρ|φ⟩ G.

It is trace preserving (tr G = 0), completely positive (its Choi matrix is I_m ⊗ I/d + (ε₀/d)|φ̄⟩⟨φ̄| ⊗ G ⪰ I/(2d) as
ε₀‖G‖_op ≤ 1/2), and ‖N_{φ,G} − 𝒟‖_⋄ ≥ ‖N_{φ,G}(φφ†) − I/d‖₁ = ε₀‖G‖₁/d ≥ ε.

A randomized tester is a mixture of deterministic trees, and refining a measurement only helps the tester,
so by convexity we may take a deterministic tree whose measurements are rank one, {ω_x d xx†}_x with unit x.
If the input at step t is ρ_t, the outcome x has probability ω_x under 𝒟 and ω_x(1 + ε₀ c_t x†Gx) under
N_{φ,G}, with **weight** c_t = ⟨φ|ρ_t|φ⟩ ∈ [0, 1]. For fixed φ the weight is a function of the earlier outcomes.

## Proof

### Step 1: averaging over φ and a budget

By convexity of the total variation distance, TV(p₀, E_{φ,G} p_{φ,G}) ≤ E_φ TV(p₀, p_φ) with p_φ = E_G p_{φ,G}.
Under 𝒟 the transcript does not depend on φ, so ρ_t is independent of φ and
E_φ c_t² = (tr ρ_t² + 1)/(m(m+1)) ≤ 2/(m(m+1)) (fourth moment of a Haar vector).

Fix φ, put B = δ d^{3/2}/ε₀² with δ = 10⁻⁵, and let τ be the first t with Σ_{s≤t} c_s² > B. Let p̃_φ be the
law in which every step t ≥ τ follows 𝒟; it is the tree with weights c̃_t = c_t 1{t < τ}, which still depend
only on earlier outcomes and satisfy Σ c̃_t² ≤ B. The two laws agree on every leaf with τ > n, so
TV(p_φ, p̃_φ) ≤ P_{p̃_φ}(τ ≤ n) ≤ P₀(τ ≤ n) + TV(p₀, p̃_φ), and

    TV(p₀, p_φ) ≤ 2 TV(p₀, p̃_φ) + P₀(τ ≤ n),   E_φ P₀(τ ≤ n) ≤ E_φ E₀ Σ_t c_t² / B ≤ 2n/(m(m+1)B).

Theorem 2 below gives TV(p₀, p̃_φ) ≤ 0.088. With n = δ' m² d^{3/2}/ε₀², δ' = 0.075 δ, the total is at most
0.176 + 0.15 < 1/3, so no tester with n uses succeeds. In terms of ε this is n ≥ 7.5·10⁻⁹ m² d^{3/2}/ε².

### Step 2: weighted adaptive mixedness testing

**Theorem 2.** Let d ≥ 10⁴, ε₀ ≤ 1/10, δ = 10⁻⁵, B = δd^{3/2}/ε₀², and consider an adaptive tree of n ≤ e^{d/20}
rank-one measurements on C^d whose step weights c_t ∈ [0,1] depend only on earlier outcomes and satisfy
Σ_t c_t² ≤ B on every path. Let p₀ be the law under I/d and p₁ = E_G p_G, where the step ratio under p_G is
1 + ε₀ c_t x†Gx and G is drawn as above. Then TV(p₀, p₁) ≤ 0.088.

The proof follows the likelihood-ratio martingale of [2, Sec. 6], with the weights carried through.
Write ε for ε₀, P_i = z_iz_i†, and set α = δ^{−1/2}, A = d√B α = d^{7/4}/ε.

**Lemma 1 (recursion).** For unit z₁,…,z_t let L(z) = E Π_i (1 + εc_i z_i†G z_i), with G = H − (tr H/d)I
*not* conditioned on U. Then E[(x†Gx)(y†Gy)] = (d|⟨x,y⟩|² − 1)/d², and by the Isserlis formula
L(z) is the sum over all matchings of Π_{pairs} ε²c_ac_b(d|⟨z_a,z_b⟩|² − 1)/d². Hence L is symmetric in its
arguments and, for every index i,

    L(z)/L(z^{∼i}) = 1 + (ε²c_i/d²) z_i† H(z^{∼i}) z_i,   H(w) = Σ_j c_j (dP_j − I) L(w^{∼j})/L(w).

Define K(w) = Σ_j c_j(dP_j − I) and K₂(w) = Σ_j c_j²(dP_j − I). Both have trace zero.

**Lemma 2 (maximal bounds).** Under p₀, K_t = K(x_{≤t}) and K₂(x_{≤t}) are matrix martingales with orthogonal
increments, since Σ_x ω_x d xx† = I. So E‖K_n‖_F² = d(d−1) E Σ c_i² ≤ d²B, likewise for K₂ (c⁴ ≤ c²), and the
maximal inequality for the submartingale ‖K_t‖_F gives E sup_t ‖K_t‖_F² ≤ 4d²B. The event
𝒢 = {sup_t ‖K_t‖_F ≤ A and sup_t ‖K₂(x_{≤t})‖_F ≤ A} has P₀(𝒢^c) ≤ 8/α² = 8δ.

**Lemma 3 (truncated against untruncated likelihood).** Let L̄(z) = E[1_U Π_i(1 + εc_i z_i†Gz_i)]. If
‖K(z)‖_F ≤ 2A and ‖K₂(z)‖_F ≤ 2A, then L(z) = L̄(z)(1 + η_z) with |η_z| ≤ η := 6e^{−0.56d + 8.1√d}.

*Proof.* Write u_i = εc_i z_i†Gz_i and L − L̄ = E[1_{U^c}Π(1 + u_i)]. By Cauchy-Schwarz its size is at most
P(U^c)^{1/2} E[Π(1+u_i)²]^{1/2}. Since (1+u)² ≤ e^{2u+u²} and Σu_i = (ε/d)⟨G, K(z)⟩ (trace zero),
Cauchy-Schwarz again gives E Π(1+u_i)² ≤ (E e^{4Σu_i})^{1/2}(E e^{2Σu_i²})^{1/2}. Here ⟨G,K⟩ = ⟨H,K⟩ is
Gaussian with variance ‖K‖_F²/d, so E e^{4Σu_i} = e^{8ε²‖K‖_F²/d³} ≤ e^{32√d}. For the second factor, the map
G ↦ e^{2ε²Σc_i²⟨P_i,G⟩²} is convex and H = G + (tr H/d)I with tr H independent of G, so by Jensen the expectation
is at most the same expectation over H. In an orthonormal basis of Hermitian matrices H has independent
N(0, 1/d) coordinates, and the quadratic form Σc_i²⟨P_i,·⟩² has trace Σc_i² ≤ B and largest eigenvalue at
most ‖Σc_i²P_i‖_op ≤ (‖K₂‖_op + B)/d. Since 4ε²(2A + B)/d² ≤ 8εd^{−1/4} + 4δd^{−1/2} ≤ 1/2, the expectation is
at most e^{4ε²B/d}. Together E Π(1+u_i)² ≤ e^{16√d + 2δ√d}. For the lower bound on L̄, let ν be the law of G
conditioned on U. On U every factor lies in [1/2, 3/2], E_ν u_i = 0 by symmetry, and log(1+u) ≥ u − u² for
|u| ≤ 1/2, so Jensen gives L̄ ≥ P(U) exp(−Σ E_ν u_i²) ≥ P(U) e^{−2ε²B/d} ≥ ½ e^{−2δ√d}, using
E(z†Gz)² = (d−1)/d². With P(U^c)^{1/2} ≤ 3e^{−0.56d} the claim follows. ∎

This comparison hints at a possible gap in the ratio step of [2, Lemma 6.13], where the range [1/2, 3/2] of the
factors, valid for G ∈ U, is applied to the untruncated likelihood. Lemmas 3 and 4 give that step here.

**Lemma 4 (one removed index).** Let z = x_{≤t} with ‖K(z)‖_F, ‖K₂(z)‖_F ≤ A, R ⊆ [t] with |R| ≤ D + 1 where D = ⌈ln(4 + d^{1/4})⌉,
S = [t] ∖ R and i ∈ S. Then ‖K(z^S)‖_F, ‖K₂(z^S)‖_F ≤ A + d(D+1) ≤ 1.01A, and
r_i := L(z^{S∖i})/L(z^S) satisfies |r_i − 1| ≤ 11εc_i + 5η.

*Proof.* ‖dP_j − I‖_F ≤ d, and d(D+1) ≤ 0.01A as A/d = d^{3/4}/ε ≥ 100(D+1) for d ≥ 10⁴. On U the factors of
L̄ are positive and the factor of index i lies in [1 − 5εc_i, 1 + 5εc_i], so L̄(z^S)/L̄(z^{S∖i}) lies there too.
Lemma 3 applies to z^S and z^{S∖i}, and |η| ≤ 10⁻¹⁰⁰⁰. ∎

**Lemma 5 (bootstrap).** If ‖K(x_{≤t})‖_F ≤ A and ‖K₂(x_{≤t})‖_F ≤ A, then ‖H(x_{≤t})‖_F ≤ 3A.

*Proof.* For a family of positive semidefinite P_j and |b_j| ≤ 1, ‖Σ b_jP_j‖_F ≤ ‖Σ P_j‖_F, since the
pairwise inner products are nonnegative. With H_S = H(z^S) = K(z^S) + Σ_{j∈S} c_j(r_j − 1)(dP_j − I) and
Σ_{j∈S} c_j²dP_j = K₂(z^S) + (Σ c_j²)I, this gives, for every set S of Lemma 4 with |R| ≤ D,

    ‖H_S‖_F ≤ ‖K(z^S)‖_F + 11ε(‖K₂(z^S)‖_F + 2√d B) + 5ηdn ≤ (3.3 + 22δd^{1/4})A =: ξ₀,

because 22ε√dB/A = 22δd^{1/4} and 5ηdn ≤ A for n ≤ e^{d/20}. If t < D, every S ⊆ [t] misses fewer than D indices, so Lemma 4 gives r_i ≤ 2
and directly ‖H‖_F ≤ 2dD ≤ 3A.
Otherwise induct on a = 0, …, D over the sets S with |R| = D − a: suppose ‖H_{S'}‖_F ≤ ξ_{a−1} whenever
|R'| = D − a + 1. For i ∈ S, Lemma 1 gives |L(z^S)/L(z^{S∖i}) − 1| ≤ ε²c_iξ_{a−1}/d² ≤ 1/2, hence
|r_i − 1| ≤ 2ε²c_iξ_{a−1}/d². The deviation is now proportional to c_i², and

    ‖H_S − K(z^S)‖_F ≤ (2ε²ξ_{a−1}/d²)(‖K₂(z^S)‖_F + 2√d B) ≤ (0.202 d^{−1/4} + 4δ) ξ_{a−1} ≤ ξ_{a−1}/e.

So ξ_a = 1.01A + ξ_{a−1}/e, and ξ_D ≤ 1.6A + e^{−D}ξ₀ ≤ 3A by the choice of D. The case a = D is S = [t]. ∎

The weights are the point of Lemma 5: the deviation of r_i is proportional to c_i, so only Σc_i² ≤ B enters.
The sum Σc_i, which can be as large as n, appears only in the term 5ηdn.

**Proof of Theorem 2.** Let Φ_t = L(x_{≤t}) and τ' the first t at which the condition of 𝒢 fails, and
Ψ_t = Φ_{t∧τ'}. By Lemma 1 and tr H = 0, E[Ψ_t/Ψ_{t−1} | x_{<t}] = 1, and since Σ_xω_x(x†Hx)² ≤ ‖H‖_F²/d,

    E[(Ψ_t/Ψ_{t−1})² | x_{<t}] ≤ 1 + ε⁴c_t²‖H(x_{<t})‖_F²/d⁵ ≤ 1 + 9ε²c_t² d^{−3/2}

by Lemma 5. As c_t depends only on x_{<t}, the process Ψ_t² Π_{s≤t}(1 + 9ε²c_s²d^{−3/2})^{−1} is a
supermartingale, so E(Ψ_n − 1)² = EΨ_n² − 1 ≤ e^{9ε²B d^{−3/2}} − 1 = e^{9δ} − 1 ≤ 10δ. On 𝒢 we have τ' = ∞ and
Ψ_n = L(x). The true likelihood ratio is L*(x) = L̄(x)/P(U) = L(x)/((1+η_x)P(U)) ≥ (1 − s)/(1 + η) whenever also
|Ψ_n − 1| ≤ s. Therefore

    TV(p₀, p₁) = E₀(1 − L*)₊ ≤ s + η + P₀(𝒢^c) + P₀(|Ψ_n − 1| > s) ≤ s + η + 8δ + 10δ/s²,

which is at most 0.088 for s = (20δ)^{1/3}. ∎

## Check

`sim/check.py` (one core, under a minute) checks the GUE covariance identity, the weighted matching formula and
the recursion of Lemma 1 against Monte Carlo and exact evaluation, the Haar fourth moment, and that the
alternatives are channels with ‖N − 𝒟‖_⋄ ≥ ε and step ratio 1 + ε₀c x†Gx. Output in `sim/out_check.txt`.

## Scope

- Ancilla-free strategies only. With an entangled ancilla the weight of a step depends on the outcome; the
  martingale property and the budget E_φ c² ≤ 2/(m(m+1)) still hold, but the quadratic increments need an
  operator-norm version of Lemma 5. The lower bounds of [1] hold with ancilla, so for ancilla-assisted adaptive
  strategies the gap between Ω(d_in² d_out/ε²) and O(d_in² d_out^{3/2}/ε²) is not closed here.
- The constants are far from optimal.
- Not formalized in Lean.

## References

1. O. Fawzi, N. Flammarion, A. Garivier, A. Oufkir. Quantum channel certification with incoherent strategies.
   COLT 2023, arXiv:2303.01188.
2. S. Chen, B. Huang, J. Li, A. Liu. Tight bounds for quantum state certification with incoherent measurements.
   FOCS 2022, arXiv:2204.07155.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
