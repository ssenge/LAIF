# Shadow norm of one-body observables for photonic classical shadows

2026-11-12

## Problem

In the photonic classical shadows of [1], a state of n photons in m modes is evolved by the passive linear-optical unitary ω(U) of a uniformly random U ∈ U(m) and measured by photon counting, with outcome s = (s_1, …, s_m), Σ s_i = n. The measurement channel is M = Σ_{k=0}^{n} s_{λ_k} Π_{λ_k} on the irreducible components λ_k of the operators on the n-photon space, with s_{λ_1} = 1/(m + 1) [1, eq. (B8)], and a snapshot estimates tr(Oρ) by ⟨s|ω(U) M^{−1}(O) ω(U)†|s⟩. The number of snapshots for T observables is O(max_t ‖O_t,0‖²_P log T/ε²) [1, Theorem 1], where O_0 is the traceless part and

‖O_0‖²_P = max_σ E_U Σ_s ⟨s|ω(U)σω(U)†|s⟩ ⟨s|ω(U)M^{−1}(O_0)ω(U)†|s⟩²   [1, eq. (C17)].

Previous best bound: ‖O_0‖²_P = O(‖O‖²_∞ m^{3d}) for observables of degree d in the a_i†a_j [1, Lemma 2]; its proof gives ‖O_0‖²_P ≤ d dim H_{λ_d} s_{λ_d}^{−1} ‖O_0‖²_∞, which is (m² − 1)(m + 1)‖O_0‖²_∞ for d = 1 [1, eqs. (C23), (C24)].

## Results

For a Hermitian m × m matrix h, let O = dΓ(h) = Σ_{ij} h_ij a_i†a_j on n photons, and h_0 = h − (tr h/m)·1. Then O_0 = dΓ(h_0) and ‖O_0‖_∞ = n‖h_0‖. Write ‖·‖ for the operator norm and ‖·‖₂ for the entrywise 2-norm.

**Theorem 1.** For every n ≥ 1, m ≥ 2 and Hermitian h,

n (m + 1)/(m + 2) · (‖h_0‖₂² + 2‖h_0‖²) + n(n − 1)‖h_0‖² ≤ ‖O_0‖²_P ≤ n² (m + 1)/(m + 2) · (‖h_0‖₂² + 2‖h_0‖²).

For n = 1 the two bounds coincide. For n ≥ 2 and h_0 ≠ 0 they differ by at most the factor min{n, 2(‖h_0‖₂²/‖h_0‖² + 2)}.

**Corollary 2.** ‖O_0‖²_P ≤ (m + 1)/(m + 2) · (‖h_0‖₂²/‖h_0‖² + 2) ‖O_0‖²_∞ ≤ (m + 1)‖O_0‖²_∞. For a hopping term a_i†a_j + a_j†a_i or an occupation number a_i†a_i, ‖h_0‖₂² ≤ 2‖h_0‖², so ‖O_0‖²_P ≤ 4‖O_0‖²_∞ for every m, and T such observables need O(n² log T/ε²) snapshots.

So for one-body observables the factor (m² − 1)(m + 1) of the previous bound becomes at most m + 1, and a constant for sparse h. The lower bound of Theorem 1 shows that a linear growth in m can occur at fixed n: for h_0 = diag(1, −1, 1, −1, …) with m even, ‖O_0‖²_P ≥ (m + 1)‖O_0‖²_∞/n. The analogue for fermions with a fixed particle number and random number-conserving bases is treated in [3].

## Proofs

*Setup.* With the convention ω(U) a_i† ω(U)† = Σ_j U_ji a_j†, one has ω(U) dΓ(h) ω(U)† = dΓ(UhU†). The traceless part of dΓ(h) on the n-photon space is dΓ(h_0), since dΓ(1) = n·1, and dΓ(h_0) lies in λ_1, so M^{−1}(O_0) = (m + 1) O_0. The eigenvalues of dΓ(h_0) are Σ_i s_i μ_i over the eigenvalues μ_i of h_0, so ‖O_0‖_∞ = n‖h_0‖.

For a sampled U let x_i = (U h_0 U†)_ii, the diagonal of the rotated matrix. Since |s⟩ is diagonal for dΓ of a diagonal matrix,

⟨s|ω(U)M^{−1}(O_0)ω(U)†|s⟩ = (m + 1) Σ_i s_i x_i.

The outcome s has the law of photon counting on ω(U)σω(U)†, and the occupation numbers have first moments E_s[s_i] = (UγU†)_ii, where γ_kj = tr(σ a_j†a_k) is the one-body matrix of σ (γ ⪰ 0, tr γ = n).

*Third moment.* The rows w_i = U†e_i of a uniformly random unitary are uniformly random unit vectors, x_i = w_i† h_0 w_i and (UγU†)_ii = w_i†γw_i. For a uniform unit vector w ∈ ℂ^m and matrices A, B, C,

E[(w†Aw)(w†Bw)(w†Cw)] = (tr A tr B tr C + tr A tr(BC) + tr B tr(AC) + tr C tr(AB) + tr(ABC) + tr(ACB)) / (m(m + 1)(m + 2)),

from the third moment of w w† on the symmetric subspace. With A = B = h_0, tr h_0 = 0 and C = γ, summing over the m rows gives

E_U Σ_i x_i² (UγU†)_ii = (n ‖h_0‖₂² + 2 tr(γ h_0²)) / ((m + 1)(m + 2)).   (∗)

*Upper bound.* For each outcome, (Σ_i s_i x_i)² ≤ (Σ_i s_i)(Σ_i s_i x_i²) = n Σ_i s_i x_i², since s_i ≥ 0. Taking the expectation over s and then over U, and using (∗) with tr(γh_0²) ≤ n‖h_0‖²,

E (m + 1)² (Σ_i s_i x_i)² ≤ n (m + 1)² (n‖h_0‖₂² + 2n‖h_0‖²) / ((m + 1)(m + 2)),

for every σ, which is the upper bound.

*Lower bound.* Let v be a unit eigenvector of h_0 with eigenvalue ±‖h_0‖, and σ the state of n photons in the mode v. Then ω(U)σω(U)† has all n photons in one mode, and s is multinomial with n trials and probabilities p_i = |(Uv)_i|², so E_s(Σ_i s_i x_i)² = n Σ_i p_i x_i² + n(n − 1)(Σ_i p_i x_i)² ≥ n Σ_i p_i x_i². Here γ = n vv† and n p_i = (UγU†)_ii, so (∗) with tr(γh_0²) = n‖h_0‖² gives (m + 1)² n E_U Σ_i p_i x_i² = n (m + 1)/(m + 2) · (‖h_0‖₂² + 2‖h_0‖²). For the second term, p_i = w_i†vv†w_i, and the second moment of a uniform unit vector, E[(w†Aw)(w†Bw)] = (tr A tr B + tr(AB))/(m(m + 1)), gives E_U Σ_i p_i x_i = v†h_0v/(m + 1) = ±‖h_0‖/(m + 1). By convexity, E_U (Σ_i p_i x_i)² ≥ ‖h_0‖²/(m + 1)². Together,

‖O_0‖²_P ≥ n (m + 1)/(m + 2) · (‖h_0‖₂² + 2‖h_0‖²) + n(n − 1)‖h_0‖².

For n = 1 the factor n² equals n. With c = (m + 1)/(m + 2) and r = ‖h_0‖₂²/‖h_0‖², the ratio of the bounds is n c(r + 2)/(c(r + 2) + n − 1), which is at most n, and for n ≥ 2 at most 2c(r + 2) ≤ 2(r + 2). ∎

*Corollary 2.* Divide by ‖O_0‖²_∞ = n²‖h_0‖², and use ‖h_0‖₂² ≤ m‖h_0‖². For a hopping term, h_0 = h has eigenvalues ±1 and 0, so ‖h_0‖₂² = 2‖h_0‖². For an occupation number, h_0 = e_ie_i† − 1/m has ‖h_0‖ = 1 − 1/m and ‖h_0‖₂² = 1 − 1/m, so ‖h_0‖₂² = ‖h_0‖² m/(m − 1) ≤ 2‖h_0‖². The sample bound follows from [1, Theorem 1]. ∎

For n = 1 the protocol is a classical shadow with uniformly random bases of ℂ^m, and Theorem 1 reproduces the shadow norm (d + 1)/(d + 2) · max_σ (tr O_0² + 2 tr(σO_0²)) of [2] at d = m.

## Check

`sim/deg1.py` builds ω(U) on the n-photon space from permanents in the occupation-number basis, for (n, m) ∈ {(1, 3), (2, 2), (2, 3), (2, 4), (3, 3), (2, 6)} and h a single occupation number, a hopping term and the alternating diagonal, and checks with asserts:

- ω(U) dΓ(h_0) ω(U)† = dΓ(Uh_0U†) and ‖O_0‖_∞ = n‖h_0‖;
- M(O_0) = O_0/(m + 1), by Monte Carlo of the channel;
- for every sampled U, the operator inequality behind the upper bound, Σ_s f_s² ω(U)†|s⟩⟨s|ω(U) ⪯ n(m + 1)² ω(U)†(Σ_i x_i² n_i)ω(U) with f_s = (m + 1) Σ_i s_i x_i;
- the identity (∗) for a random positive γ, within four standard errors;
- the lower bound for σ = n photons in the top eigenmode, within four standard errors;
- the exact shadow norm, the largest eigenvalue of E_U Σ_s f_s² ω(U)†|s⟩⟨s|ω(U) = (m + 1)² E_U dΓ(K_U)² with K_U = U†diag(Uh_0U†)U, computed from the exact fourth moments of a uniformly random unitary and compared with Monte Carlo within 5%: it lies between the two bounds of Theorem 1, with equality for n = 1.

Output in `sim/deg1_out.txt`. In these cases the exact ratio ‖O_0‖²_P/‖O_0‖²_∞ lies between 2.0 and 4.47, against (m² − 1)(m + 1) from 9 to 245.

## Scope

- Written proof with numerical checks. The form of the measurement channel and its eigenvalue s_{λ_1} = 1/(m + 1) are taken from [1].
- Only observables of degree 1 are covered. For n ≥ 2 the two bounds of Theorem 1 differ by at most the factor min{n, 2(‖h_0‖₂²/‖h_0‖² + 2)}.

## References

[1] H. Thomas, U. Chabaud, P.-E. Emeriau. Shedding light on classical shadows: learning photonic quantum states. arXiv:2510.07240.

[2] H.-Y. Huang, R. Kueng, J. Preskill. Predicting many properties of a quantum system from very few measurements. Nature Physics 16, 1050-1057 (2020). arXiv:2002.08953.

[3] G. H. Low. Classical shadows of fermions with particle number symmetry. arXiv:2208.08964.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
