# Learning a chain Hamiltonian from copies of its ground state needs Ω(n/ε²) copies

2026-11-25

## Problem

A local Hamiltonian H on a chain of n qubits is to be learned from copies of its unique ground state ψ. Since ψ does not change when H is multiplied by a positive number or shifted by a multiple of the identity, the coefficients can only be learned up to a common positive scale. The correlation-matrix method recovers H as the kernel of a matrix of ground-state correlations [1, 2]. It is known there that perturbations of the form Σ_x e^{iqx} h_x with small q make the smallest nonzero eigenvalues small, so that, without translation invariance, H is recovered only up to a slowly varying factor [1]. From Gibbs states at a fixed inverse temperature β, all coefficients are learned to ℓ∞ error ε with Õ(e^{O(β)} ε^{−2} log n) copies [3].

| | copies for ℓ∞ error ε |
|---|---|
| Gibbs states at fixed β [3] | Õ(e^{O(β)} log(n)/ε²) |
| Ground states, Theorem 1 (1D, gap Δ, normalized weights, any measurement on all copies) | Ω(nΔ²/(κε²)) |

## Setting

Let H_w = Σ_{x=1}^{n} w_x h_x, where each h_x is Hermitian, acts on the sites x, …, x + r and has ‖h_x‖ ≤ 1, and w ∈ [1, 1 + ε]^n is a vector of weights. The learner receives N copies of the ground state of H_w and has to output an estimate ŵ of the normalized weights w/‖w‖_∞. It may measure all N copies jointly.

Assumptions on the unweighted chain H = H_{(1,…,1)}:

- **(A1) Gap.** For every w ∈ [1, 1 + ε]^n, H_w has a unique ground state and spectral gap at least Δ > 0.
- **(A2) Clustering.** In the ground state ψ of H, |⟨AB⟩ − ⟨A⟩⟨B⟩| ≤ C‖A‖‖B‖e^{−d/ξ} for operators A, B, each supported on an interval of r + 1 consecutive sites, at distance d ≥ 1. For gapped finite-range chains this holds with ξ = O(1/Δ) and C depending on r [4, 5].

Let b_m = 2 for 1 ≤ m ≤ r and b_m = min{2, C e^{−(m−r)/ξ}} for m > r, and κ = 2 Σ_{m≥1} m² b_m, a constant that depends on r, C and ξ but not on n.

## Result

**Theorem 1.** Let n ≥ 3, 0 < ε ≤ 1/2, and assume (A1) and (A2) with 4π²κε² ≤ nΔ². A learner that, for every w ∈ [1, 1 + ε]^n, outputs with probability at least 2/3 an estimate ŵ with ‖ŵ − w/‖w‖_∞‖_∞ ≤ ε/7 uses at least

N ≥ ln(9/8) · nΔ² / (4π²κε²)

copies.

**Corollary 2** (transverse-field chain). Let H = −(1/4) Σ_x (b_x X_x + J_x Z_x Z_{x+1}) with fields b_x ∈ [2, 3] and couplings J_x ∈ [1/2, 1] (open chain, local terms −(b_x X_x + J_x Z_x Z_{x+1})/4 of norm at most 1, range r = 1). Then (A1) holds with Δ = (2 − (1 + ε))/2 ≥ 1/4 for ε ≤ 1/2, and (A2) by [4, 5], since the excitation energies of H_w are twice the singular values of the bidiagonal matrix with diagonal w_x b_x and off-diagonal w_x J_x [6], whose smallest singular value is at least min_x w_x b_x − max_x w_x J_x, before the factor 1/4. So ℓ∞ learning from ground states needs Ω(n/ε²) copies for this class, while O(log n) is the n-dependence for Gibbs states [3].

*Non-vacuity.* The class of Corollary 2 satisfies both assumptions, and the two weight vectors used in the proof lie in it. `sim/lower.py` confirms the gap bound and Lemma 3 on exact ground states, where the infidelity is at most 0.063 times the bound of Lemma 3, and `sim/ff.py` shows that n Var_ψ(V) stays between 0.66 and 0.75 for n = 100, …, 800, so the 1/n decay of Lemma 4 is attained. The scripts use the local terms without the factor 1/4, so these values are 16 times those of the normalized class.

## Proof

Let f(x) = sin(π(x − 1/2)/n), V = Σ_x f(x) h_x, and compare H_0 = H with H_1 = H + εV = H_{1+εf}. Both weight vectors lie in [1, 1 + ε]^n.

**Lemma 3** (fidelity). Let ψ_0, ψ_1 be the ground states of H_0, H_1, and Δ′ the smallest gap of H + tV over t ∈ [0, ε]. If 4ε² Var_{ψ_0}(V) ≤ Δ′², then 1 − |⟨ψ_0|ψ_1⟩|² ≤ 2ε² Var_{ψ_0}(V)/Δ′².

*Proof.* Let H_t = H + tV with ground energy E_t, and a(t) = ‖(H_t − E_t)ψ_0‖. Since H_0ψ_0 = E_0ψ_0, (H_t − E_t)ψ_0 = t(V − v)ψ_0 with v = (E_t − E_0)/t, so a² = t²(Var_{ψ_0}(V) + (⟨V⟩ − v)²). The vector φ = (H_t − E_t)ψ_0 is orthogonal to the ground state of H_t, and t(⟨V⟩ − v) = ⟨ψ_0|H_t − E_t|ψ_0⟩ = ⟨φ|(H_t − E_t)^{−1}|φ⟩ ≤ a²/Δ′, with the inverse taken on the excited subspace. Hence a² ≤ t² Var + a⁴/Δ′². For 4t² Var < Δ′² the two roots of this quadratic inequality in a² are separated, and a(t) is continuous with a(0) = 0, so a² ≤ (Δ′²/2)(1 − √(1 − 4t² Var/Δ′²)) ≤ 2t² Var. Finally 1 − |⟨ψ_t|ψ_0⟩|² is the squared norm of the part of ψ_0 orthogonal to ψ_t, which is at most a²/Δ′². ∎

**Lemma 4** (variance). Under (A2), Var_{ψ_0}(V) ≤ κ Σ_y (f(y + 1) − f(y))² ≤ κπ²/n.

*Proof.* Write c_x = (h_x − ⟨h_x⟩)ψ_0, so Σ_x c_x = (H − E_0)ψ_0 = 0, and S_{>y} = Σ_{x>y}(h_x − ⟨h_x⟩). Summation by parts gives (V − ⟨V⟩)ψ_0 = Σ_x f(x)c_x = Σ_y g_y S_{>y}ψ_0 with g_y = f(y + 1) − f(y). So Var(V) = Σ_{y,y′} g_y g_{y′} K(y, y′) with K(y, y′) = ⟨ψ_0|S_{>y}S_{>y′}|ψ_0⟩. For y ≤ y′, S_{>y}ψ_0 = −S_{≤y}ψ_0, so K(y, y′) = −Cov(S_{≤y}, S_{>y′}) is a sum of covariances of terms h_x, h_{x′} with x ≤ y ≤ y′ < x′. For x′ − x = m their supports are at distance m − r, so each covariance is at most b_m in absolute value (at most 2 when the supports overlap or touch, by (A2) otherwise), and at most m pairs have x′ − x = m. So |K(y, y′)| ≤ Σ_{m > y′−y} m b_m. Summing over y′ gives Σ_{y′} |K(y, y′)| ≤ κ, and the Schur test gives Var(V) ≤ κ Σ_y g_y². Finally |g_y| ≤ π/n for each of the n − 1 values of y. ∎

*Theorem 1.* By Lemma 4 and the assumption 4π²κε² ≤ nΔ², 4ε² Var ≤ Δ² ≤ Δ′², so Lemma 3 applies, and 1 − F ≤ 2π²κε²/(nΔ²) ≤ 1/2, where F = |⟨ψ_0|ψ_1⟩|². With f* = max_x f(x), the normalized weight vectors are (1, …, 1) and (1 + εf)/(1 + εf*). At x = 1 they differ by ε(f* − f(1))/(1 + εf*) ≥ ε/3, since f* − f(1) ≥ 1/2 for n ≥ 3 (f* = 1 for odd n, f* = cos(π/(2n)) for even n, and f(1) = sin(π/(2n))) and ε ≤ 1/2. So a learner with error ε/7 tells ψ_0^{⊗N} from ψ_1^{⊗N} with probability at least 2/3. For two pure states the smallest error probability is (1 − √(1 − F^N))/2, so F^N ≤ 8/9 and N ≥ ln(9/8)/ln(1/F) ≥ ln(9/8) F/(1 − F) ≥ ln(9/8)/(2(1 − F)) ≥ ln(9/8) nΔ²/(4π²κε²). ∎

## Check

- `sim/lower.py` (output `sim/out_lower.txt`) builds 15 random chains of Corollary 2 with n = 6, …, 14 by exact diagonalization. For each chain it asserts the gap bound of Corollary 2 along H + tV, t ∈ [0, ε], the bound of Lemma 3 for ε = 0.05, 0.2, 0.5, the summation-by-parts identity of Lemma 4 on the vectors, and the Schur bound with the exact matrix K. It prints n Var_ψ(V), which lies between 0.33 and 0.72 (local terms without the factor 1/4).
- `sim/ff.py` (output `sim/out_ff.txt`) computes Var_ψ(V) exactly for the same class by the free-fermion form of the chain. It asserts agreement with exact diagonalization at n = 6, 8, and prints n Var_ψ(V) for n up to 800.

## Scope

- The bound is for chains. For a D-dimensional lattice, the same perturbation with a profile of width n^{1/D} gives Σ|∇f|² of order n^{1−2/D}, so the argument gives no growth in n for D = 2.
- The constant κ grows with the correlation length, about as Cξ³, and ξ = O(1/Δ), so the dependence on the gap is about Δ⁵/C, and the bound exceeds the trivial Ω(1/ε²) only for n large compared with κ/Δ². The comparison with Gibbs states is for fixed β and constant gap; Gibbs states at β of order log(n)/Δ have e^{O(β)} = poly(n).
- The bound concerns ℓ∞ accuracy of the normalized weights. It says nothing about learning a Hamiltonian whose ground state is close to ψ, and no matching upper bound is given.
- The clustering assumption (A2) is taken from [4, 5] as stated; the constant κ depends on its constants.
- **Not formalized:** the theorem and lemmas have no Lean proof. Theorem 1 and Corollary 2 are Claims with the checks above.

## References

1. X.-L. Qi, D. Ranard. Determining a local Hamiltonian from a single eigenstate. Quantum 3, 159 (2019). arXiv:1712.01850.
2. E. Bairey, I. Arad, N. H. Lindner. Learning a local Hamiltonian from local measurements. Physical Review Letters 122, 020504 (2019). arXiv:1807.04564.
3. Near-optimal learning of quantum many-body systems from Gibbs and thermal metastable states via the stationarity test. arXiv:2611.01520 (2026).
4. M. B. Hastings, T. Koma. Spectral gap and exponential decay of correlations. Communications in Mathematical Physics 265, 781 (2006).
5. B. Nachtergaele, R. Sims. Lieb-Robinson bounds and the exponential clustering theorem. Communications in Mathematical Physics 265, 119 (2006).
6. E. Lieb, T. Schultz, D. Mattis. Two soluble models of an antiferromagnetic chain. Annals of Physics 16, 407 (1961).

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
