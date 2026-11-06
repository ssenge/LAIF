# Damped oscillator networks: where the exponential quantum speedup ends

Written 6 Nov 2026.

Babbush, Berry, Kothari, Somma and Wiebe [1] gave a quantum algorithm that simulates 2ⁿ coupled classical oscillators in time polynomial in n, proved that classical algorithms need 2^{Ω(n)} queries for the same task, and showed that estimating a kinetic energy is BQP-complete. Their networks are undamped. Krovi [7] showed that the hardness survives damping whose strength times the simulated time is at most an inverse polynomial. This folder treats uniform damping,

  M ẍ + 2γ M ẋ + K x = 0,

which is mass-proportional (Rayleigh) damping, or for circuits a conductance to ground at every node in proportion to its capacitance, and asks how many damping times γt the quantum advantage survives. Energies are measured relative to the initial energy E₀, and the kinetic-energy fraction of oscillator v is k_v(t) = ½ m_v ẋ_v(t)² / E₀. The vector µ of spring extensions, with entries √κ_jj x_j and √κ_jk (x_j − x_k), is the one of [1].

**Theorem 1 (damping by walls).** Let x⁰ solve the undamped network (K, M) with x(0) = 0 and ẋ(0) = v₀. Add a wall of stiffness γ² m_j at every mass, K' = K + γ²M, and damp the result uniformly at rate γ. With the same initial data, the damped solution is exactly

  x(t) = e^{−γt} x⁰(t),  ẋ(t) = e^{−γt} (ẋ⁰(t) − γ x⁰(t)),

and E₀ is unchanged. Hence every displacement is the undamped one times e^{−γt}, and the potential energy of any set of springs of K is the undamped one times e^{−2γt}. For the kinetic-energy fraction k_V of a set V of oscillators,

  | e^{γt} √k_V(t) − √k⁰_V(t) | ≤ γ c_V,  c_V = min( 1/√λ*, max_{v∈V} √(m_v / κ_vv) ),

where λ* is the smallest eigenvalue of M^{−1/2} K M^{−1/2} (the first term applies to gapped networks, the second when every oscillator in V has a wall). One query to K' costs one query to K. So an estimate of the damped k_V to additive error e^{−2γt} ε/4 yields the undamped √k⁰_V to error √ε whenever γ c_V ≤ √ε/2. For instances with x(0) = 0 and c_V ≤ poly(n), the hardness of [1] at inverse-polynomial precision therefore carries over to damping with γt up to Θ(log n), while Theorem 2 below, which holds for every instance, needs γt below the square root of the precision.

**Theorem 2 (weak damping, any network).** In the coordinates |ψ⟩ = (√M ẋ, iµ)/√(2E₀) of [1], damping adds −2γ times the projector on the velocity block, and ‖ψ_γ(t) − ψ₀(t)‖ ≤ 2γt, so |√k_v^γ(t) − √k_v^0(t)| ≤ 2γt. A gap of 1/p against e^{−√n} in the undamped kinetic-energy fraction becomes a gap of 1/(4p) against 1/(16p) when γt ≤ 1/(8√p). This sharpens the perturbative condition of [7] from γt = O(1/p) to γt = O(1/√p).

**Theorem 3 (kinetic energy dies out).** For every network, initial state and t > 0, the total kinetic energy at time t is at most min(1, 4/(γt)) E₀. Numerically the best constant is 0.255 in place of 4, and γt · KE(t)/E₀ tends to at most 1/(4e) ≈ 0.092. Relative to the current energy E(t) no such bound holds, since a single underdamped mode keeps a kinetic-energy fraction of order one.

**Theorem 4 (heat-flow limit).** For γt ≥ 1, the state (√M ẋ, µ) is within (7.5/(γt)) √(2E₀) in Euclidean norm of the heat-flow model

  x(t) ≈ e^{−(t/2γ) A} (x(0) + ẋ(0)/(2γ)),  ẋ(t) ≈ −(A/2γ) x(t),  A = M⁻¹K.

Numerically the constant is 0.47 in place of 7.5. This is a finite-dimensional, explicit-constant form of the diffusion phenomenon for abstract damped wave equations [8, 9, 10].

**Theorem 5 (classical algorithm for long times).** e^{−sA} is the transition operator of a continuous-time random walk with killing that jumps from j to k at rate κ_jk/m_j and is killed at rate κ_jj/m_j. With oracle access to K, M and the initial state, and y = x(0) + ẋ(0)/(2γ), a classical algorithm estimates

- a spring extension µ_e(t) to additive error (7.5/(γt)) √(2E₀) + 2√κ_e η ‖y‖_∞,
- a mass-weighted velocity √m_j ẋ_j(t) to additive error (7.5/(γt)) √(2E₀) + √m_j (a/γ) η ‖y‖_∞, with a = max_j K_jj/m_j,
- a spring energy µ_e²/2 to additive error (15/(γt))(1 + 3.75/(γt)) E₀ plus the corresponding sampling term,

with probability 1 − δ, from O(η⁻² log(d/δ)) walks per needed node, each with expected (t/2γ) a jumps and O(d) queries per jump. This is the random-walk method for the heat equation [11] applied to the heat-flow model.

**Theorem 6 (exact walk for strong damping).** If γ² ≥ a, that is, the damping rate exceeds the frequency of every oscillator with its neighbours held fixed, then P = I − A/γ² is entrywise nonnegative and substochastic, and

  x(t) = E[ P^{⌊N/2⌋} x(0) + 1{N odd} P^{(N−1)/2} ẋ(0)/γ ],  N ~ Poisson(γt),

so a classical random walk with O(γt) steps per sample estimates displacements without the bias of Theorem 4. This is the graph version of the telegraph-process representation of Goldstein and Kac [12, 6]. The walls of Theorem 1 violate its condition, as they must.

**Picture.** For kinetic energies, the separation of [1] survives for γt = O(√ε) on every instance (Theorem 2) and up to γt = Θ(log n) on gapped or walled instances (Theorem 1), and the decision problem becomes trivial once 4/(γt) is below its threshold (Theorem 3). For spring extensions and velocities, a classical random walk reaches additive error O(√E₀/(γt)) in time polynomial in t, 1/γ and the inverse precision (Theorem 5). On the walled family of Theorem 1 every observable decays like e^{−γt}, so there the boundary is exactly logarithmic.

Status: Claim. The identity of Theorem 1 is in Lean for any linear generator on a normed space. The closed forms of a damped mode, the scalar form of Theorem 3 for γt ≥ 8 with constant 8, the series identities behind Theorem 6 and the walk matrix facts are in Lean. Theorems 1, 4, 5 and 6 are checked numerically on random networks and on the glued trees of [1].

## Before and after

| Category | Problem | Before | After | Scope | Status |
|---|---|---|---|---|---|
| Quantum algorithms, classical dynamics | Damped coupled oscillators: hardness of kinetic energies | Exponential separation without damping [1]; BQP-hard for damping times time at most an inverse polynomial [7] | Exact reduction from undamped to damped networks by walls: displacements and potential energies scale by e^{−γt} and e^{−2γt}, and hardness of kinetic energies carries over up to γt = Θ(log n) on gapped or walled instances; kinetic energy at most 4E₀/(γt) in every network | Uniform (Rayleigh) damping | Claim; identity in Lean; simulation |
| Quantum algorithms, classical dynamics | Damped coupled oscillators: spring extensions and velocities | Diffusion phenomenon with unspecified constants [8, 9, 10]; classical methods on local graphs when every mode decays fast [3] | Classical random walk with additive error 7.5√(2E₀)/(γt) plus sampling error, polynomial in t, 1/γ and the inverse precision; exact walk when γ² exceeds every K_jj/m_j | Uniform damping, any sparse network | Claim; scalar lemmas in Lean; simulation |

## Prior work

The undamped setting, the classical lower bound and BQP-completeness are from [1]. Krovi [7] gives quantum algorithms for damped and forced oscillator networks with a general damping matrix and proves BQP-hardness of kinetic-energy estimation for damping of inverse-polynomial strength over the simulated time, by a Dyson-series bound; Theorem 2 sharpens that bound. Schade, Simon, Wiebe, Keating, Bösch and Fichtner [3] treat non-Markovian dissipation localized on a small fraction of the masses, prove BQP-completeness there, and remove the advantage on local graphs when every mode decays at a uniform rate; with uniform damping the slow diffusive modes decay only at rate about λ/(2γ), so that argument does not apply. Villanyi, Yanay and Mizel [4] simulate a few system oscillators coupled to an exponentially large bath. Sakamoto and Fujii [2] dequantize undamped dynamics with geometrically local interactions. For u'' + u' + Au = 0 with A self-adjoint and nonnegative, Ikehata and Nishihara [8] introduced the comparison with the heat equation v' + Av = 0 at rate 1/t, proved in general by Chill and Haraux [9] and by Radu, Todorova and Yordanov [10]; after rescaling time by 2γ this is the heat-flow model of Theorem 4. Linden, Montanaro and Shao [11] compare random-walk and quantum algorithms for the heat equation. The telegraph process behind Theorem 6 goes back to Goldstein [12] and Kac [6]. To our knowledge, the reduction of Theorem 1 and its use to carry the hardness of [1] to damped networks, the explicit constants of Theorems 3 and 4 in the setting of [1], and the classical algorithms of Theorems 5 and 6 for uniformly damped sparse networks are new.

## 1. Mode reduction

With u = M^{1/2} x and Ã = M^{−1/2} K M^{−1/2} ⪰ 0, ü + 2γu̇ + Ãu = 0 and E = ½(‖u̇‖² + ‖Ã^{1/2}u‖²) is nonincreasing. For an eigenvalue λ of Ã, write τ = γt and ℓ = λ/γ². In energy coordinates (p, w) = (√λ u_λ, u̇_λ) the mode evolves by

  R = [[F, √ℓ G], [−√ℓ G, Gd]],

where G solves G'' + 2G' + ℓG = 0, G(0) = 0, G'(0) = 1, Gd = G' and F = Gd + 2G is the displacement response, F(0) = 1, F'(0) = −ℓG(0) = 0. With ρ = √(1 − ℓ) (overdamped) and ω = √(ℓ − 1) (underdamped):

  G = e^{−τ} sinh(τρ)/ρ,  G = τe^{−τ} (ℓ = 1),  G = e^{−τ} sin(τω)/ω.

The vector µ satisfies ‖µ‖ = ‖Ã^{1/2}u‖, so the norm of (√M ẋ, µ) is the Euclidean norm of (p, w) over all modes.

## 2. Theorem 1

Write x = e^{−γt} y. Then ẍ + 2γẋ + (A + γ²)x = e^{−γt}(ÿ + Ay), so x solves the damped equation with generator A' = M⁻¹(K + γ²M) = A + γ² exactly when y solves the undamped one, with x(0) = y(0) and ẋ(0) = ẏ(0) − γy(0). For x(0) = 0 the initial data agree, and so does E₀ = ½ v₀ᵀMv₀. The coupling springs of K' are those of K. For the velocities, e^{γt}√M ẋ = √M ẋ⁰ − γ√M x⁰, so by the triangle inequality on V the error is at most γ‖(√M x⁰)_V‖. The undamped potential energy is at most E₀. In a gapped network it bounds ‖√M x⁰‖² ≤ 2E₀/λ*, and with walls on V it bounds Σ_{v∈V} m_v (x⁰_v)² ≤ max_V (m_v/κ_vv) Σ_V κ_vv (x⁰_v)² ≤ max_V (m_v/κ_vv) 2E₀. Dividing by √(2E₀) gives the bound on √k_V.

## 3. Theorem 2

d|ψ⟩/dt = (−iH − 2γΠ)|ψ⟩ with Π the projector on the velocity block. The generator is dissipative, so the evolution is a contraction, and Duhamel's formula gives ‖ψ_γ(t) − ψ₀(t)‖ ≤ 2γt. If the undamped fraction is at least 1/p, the damped one is at least 1/(4p) when 2γt ≤ 1/(2√p); if it is at most e^{−√n}, the damped one is at most 1/(16p) when 2γt ≤ 1/(8√p), for large n. Membership in BQP follows from the quantum algorithms of [7] or from the linear combination of Hamiltonian simulation [5], since the dissipative part 2γΠ is positive semidefinite.

## 4. Theorem 3

The kinetic energy of a mode at time t is |−√ℓ G p₀ + Gd w₀|²/2 ≤ (ℓG² + Gd²) E_mode by Cauchy-Schwarz, and summing over modes gives KE(t) ≤ κ(γt) E₀ with κ(τ) = sup_ℓ (ℓG² + Gd²) ≤ 1, the last by energy decay. With α = 1 − ρ, a = e^{−τα} and b = e^{−τ(1+ρ)}:

- ρ ≥ 1/2: ℓ ≤ 2α and G ≤ a, so ℓG² ≤ 2αa² ≤ 1/τ by y e^{−y} ≤ 1; |Gd| ≤ αa + 3b/2 gives Gd² ≤ 2α²a² + 4.5b² ≤ 2/τ. Total at most 3/τ.
- ρ < 1/2: G ≤ τa since 1 − e^{−2τρ} ≤ 2τρ, Gd = (a + b)/2 − G, a² ≤ e^{−τ}, so ℓG² + Gd² ≤ (τ² + (1+τ)²)e^{−τ}.
- ℓ > 1: |sin x| ≤ min(1, |x|) gives ℓG² + Gd² ≤ e^{−2τ}(τ² + 1 + (1+τ)²).

The last two are at most 4/τ for τ ≥ 4 and at most 8/τ for τ ≥ 8 (via e^τ ≥ τ⁷/7!, the version in Lean). For τ < 4, κ ≤ 1.

## 5. Theorem 4

The heat model replaces F, √ℓG, Gd by h, √ℓh/2, −ℓh/4 with h = e^{−τℓ/2}. Since α − ℓ/2 = ℓα/(2(1+ρ)) ≤ 2ℓ²/9 for ρ ≥ 1/2, |e^{−τα} − h| ≤ (2/9)τℓ²h ≤ 0.482/τ, and the entries of R − R_h are at most 1.34/τ, 1.06/τ and 2.06/τ there. For ℓ > 3/4 the entries of R are at most (1+τ)e^{−τ/2} ≤ 2.74/τ (the maximum of τ(1+τ)e^{−τ/2} is 2.7376) and those of R_h at most e^{−3τ/8} ≤ 0.99/τ. So every entry is at most 3.73/τ and ‖R − R_h‖ ≤ ‖R − R_h‖_F ≤ 7.46/τ for τ ≥ 1. Physically: modes with λ above γ² ring down at rate γ, and the slow modes follow ẋ ≈ −Ax/(2γ).

## 6. Theorems 5 and 6

−A has nonnegative off-diagonal entries κ_jk/m_j and row sums −κ_jj/m_j ≤ 0, so (e^{−sA}y)_j = E_j[y(X_s); X alive at s] for the walk X of Theorem 5. Each walk makes Poisson-many jumps with mean at most s·a. A spring extension needs the two endpoint values, a velocity needs the d + 1 values in Σ_k A_jk (e^{−sA}y)_k/(2γ) with Σ_k |A_jk| ≤ 2a, and Hoeffding's inequality gives the sampling terms. Each component of (√M ẋ, µ) is bounded by the norm in Theorem 4. For a spring energy, |µ² − µ_h²|/2 ≤ δ(2|µ| + δ)/2 with |µ| ≤ √(2E₀) and δ = 7.5√(2E₀)/τ.

For Theorem 6, substitute x = e^{−γt}y: ÿ = (γ²I − A)y = γ²Py, y(0) = x(0), ẏ(0) = ẋ(0) + γx(0). The series of cosh and sinh give

  x(t) = Σ_k e^{−γt}((γt)^{2k}/(2k)! + (γt)^{2k+1}/(2k+1)!) P^k x(0) + Σ_k e^{−γt}((γt)^{2k+1}/(2k+1)!) P^k ẋ(0)/γ,

and the weights are the probabilities that ⌊N/2⌋ = k (with N odd in the second sum) for N ~ Poisson(γt). When P is entrywise nonnegative and substochastic, P^k y is an expectation over a k-step walk with killing.

## 7. Measurements

[`sim/scalar_check.py`](sim/scalar_check.py) computes κ(τ) and sup_ℓ ‖R − R_h‖ on a fine grid of ℓ: sup_τ τκ(τ) = 0.2546, τκ(τ) → 0.0920 ≈ 1/(4e), sup_{τ≥1} τ‖R − R_h‖ = 0.469. [`sim/bounds_check.py`](sim/bounds_check.py) checks every intermediate inequality of Sections 4 and 5 on the grid ([log](sim/bounds_check.log)).

[`sim/network_check.py`](sim/network_check.py) ([log](sim/network_check.log)) builds random sparse networks with 60 masses and compares the exact solution with the series of Theorem 6 (agreement to 10⁻¹⁵), with the Poisson walk of Theorem 6 and the heat-flow walk of Theorem 5 (agreement within the sampling error of 2·10⁴ walks), and with the heat model, against the bound of Theorem 4.

[`sim/glued_trees.py`](sim/glued_trees.py) ([log](sim/glued_trees.log)) uses the glued trees of [1] (depth 8, 1022 masses, x(0) = 0, ẋ(0) at ENTRANCE, K = 3I − Adj). The largest kinetic-energy fraction at EXIT over t ∈ [0, 32] with uniform damping and no added walls is:

| γ | 0 | 0.001 | 0.003 | 0.01 | 0.03 | 0.1 | 0.3 | 1 |
|---|---|---|---|---|---|---|---|---|
| max k_EXIT | 0.324 | 0.311 | 0.286 | 0.213 | 0.091 | 4.8·10⁻³ | 2.8·10⁻⁶ | 7.1·10⁻¹¹ |
| γt at the maximum | 0 | 0.02 | 0.06 | 0.21 | 0.63 | 2.1 | 5.0 | 19.5 |

Up to γt ≈ 2 the signal falls like e^{−2γt}, as for the walled network of Theorem 1, and at every γ it stays far below the general bound of Theorem 3. With the walls of Theorem 1 added, the damped solution, computed from the damped mode formulas, matches e^{−γt} times the undamped one to 2·10⁻¹⁵ for γ from 0.03 to 1, and the deviation |e^{γt}√k_EXIT − √k⁰_EXIT| stays below its bound γ c_EXIT = γ (largest value 0.41γ).

## 8. Limits

- The damping is uniform in the sense M⁻¹D = 2γI. Non-uniform damping, damping on a few masses (as in [3]) and non-Markovian damping are not covered.
- Theorem 1 transfers the hardness of undamped instances with x(0) = 0. For kinetic energies it needs a spectral gap or walls on the observed set; the hard families of [1] are not shown here to have either (on the glued trees only ENTRANCE and EXIT carry walls, while the lower bound of [1] uses general sets).
- Theorem 5 estimates a bounded number of springs or velocities; a set of springs of size |V| costs |V| times more, while [1] handles exponentially large sets. Its error is additive relative to E₀ and ‖y‖_∞, and quantities exponentially small relative to E₀ are not resolved.
- For kinetic energies the classical complexity between γt = Θ(log n) and γt ≈ 4 times the inverse threshold is open, and for spring extensions and velocities it is open at precision finer than 1/(γt).
- Theorem 4 is first order; higher-order corrections in 1/(γt) would sharpen the error.

## 9. Formal verification

[`lean/`](lean/) is a Lean 4 library `DampedOsc` on Mathlib with 25 theorems, no `sorry`, and only the standard axioms (propext, Classical.choice, Quot.sound), as listed by `lean/DampedOsc/Axioms.lean`. Build with `lake build` in `lean/`.

| Part | Theorems |
|---|---|
| Theorem 1: if ÿ = −Ay for a continuous linear map A on a real normed space, then x = e^{−γt}y has derivative e^{−γt}(ẏ − γy) and solves ẍ = −2γẋ − (A + γ²)x | `damped_of_undamped` |
| Closed forms of a damped mode solve G'' + 2G' + ℓG = 0, G(0) = 0, G'(0) = 1 (overdamped, critical, underdamped) | `Gover_ode`, `Gunder_ode`, `Gcrit_ode`, `Gover_hasDerivAt`, `Gdover_hasDerivAt`, `Gunder_hasDerivAt`, `Gdunder_hasDerivAt` |
| Displacement response F = Gd + 2G: F(0) = 1 in all three cases, F' = −ℓG | `Fover_zero`, `Funder_zero`, `Fcrit_zero`, `Fover_deriv` |
| Theorem 3, scalar bound ℓG² + Gd² ≤ 8/τ for τ ≥ 8 (and ≤ 3/τ for all τ > 0 when ρ ≥ 1/2) | `ke_over_large`, `ke_over_small`, `ke_under`, `ke_crit`, `ke_all` |
| Theorem 6, series in β = 1 − ℓ with Poisson weights for β > 0, β = 0 and β < 0; weights sum to one | `hasSum_wx_over`, `hasSum_wv_over`, `hasSum_wx_crit`, `hasSum_wx_under`, `hasSum_wv_under`, `hasSum_wx_one` |
| Theorem 6, P = I − M⁻¹K/γ² is entrywise nonnegative and substochastic | `walkMatrix_nonneg`, `walkMatrix_row_le` |

**Not formalized.** The energy bound on the wall term in Theorem 1 and the reductions built on it; the reduction from the network to its modes (spectral theorem, energy coordinates), the Cauchy-Schwarz sum over modes and the energy decay κ ≤ 1; Theorems 2 and 4; the random walks and their Monte Carlo error; the matrix form of the series in Theorem 6; the quantum algorithms of [5, 7].

## References

1. R. Babbush, D. W. Berry, R. Kothari, R. D. Somma, N. Wiebe. Exponential quantum speedup in simulating coupled classical oscillators. Physical Review X 13, 041041, 2023. arXiv:2303.13012.
2. K. Sakamoto, K. Fujii. On the quantum computational complexity of classical linear dynamics with geometrically local interactions: dequantization and universality. arXiv:2505.10445, 2025.
3. M. Schade, S. Simon, N. Wiebe, S. Keating, C. Bösch, A. Fichtner. Quantum simulation of dissipative non-Markovian coupled classical oscillators. arXiv:2609.20721, 2026.
4. A. Villanyi, Y. Yanay, A. Mizel. Exponential quantum advantage for simulating open classical systems. arXiv:2503.11483, 2025.
5. D. An, J.-P. Liu, L. Lin. Linear combination of Hamiltonian simulation for nonunitary dynamics with optimal state preparation cost. Physical Review Letters 131, 150603, 2023. arXiv:2303.01029.
6. M. Kac. A stochastic model related to the telegrapher's equation. Rocky Mountain Journal of Mathematics 4, 497-509, 1974.
7. H. Krovi. Quantum algorithms to simulate quadratic classical Hamiltonians and optimal control. arXiv:2404.07303, 2024.
8. R. Ikehata, K. Nishihara. Diffusion phenomenon for second order linear evolution equations. Studia Mathematica 158, 153-161, 2003.
9. R. Chill, A. Haraux. An optimal estimate for the difference of solutions of two abstract evolution equations. Journal of Differential Equations 193, 385-395, 2003.
10. P. Radu, G. Todorova, B. Yordanov. Diffusion phenomenon in Hilbert spaces and applications. Journal of Differential Equations 250, 4200-4218, 2011.
11. N. Linden, A. Montanaro, C. Shao. Quantum vs. classical algorithms for solving the heat equation. Communications in Mathematical Physics 395, 601-641, 2022. arXiv:2004.06516.
12. S. Goldstein. On diffusion by discontinuous movements, and on the telegraph equation. Quarterly Journal of Mechanics and Applied Mathematics 4, 129-156, 1951.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
