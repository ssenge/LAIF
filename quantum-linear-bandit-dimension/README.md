# Quantum linear bandits with general action sets: the dimension factor d^{3/2} is necessary, and tight on the ball

Written 11 Nov 2026.

## Problem

This is the quantum linear bandit model of [1, Section 2]. The action set A lies in the unit ball of R^m, the unknown parameter θ' satisfies |θ'| ≤ 1, and every action x' has mean reward μ(x') = ⟨x', θ'⟩ ∈ [0, 1]. The learner cannot sample rewards. Instead, each action has a reward oracle, a unitary O_{x'} with

O_{x'} |0⟩ = Σ_ω √P(ω) |ω⟩ |y(ω)⟩,

whose reward has mean μ(x'). In round t the learner picks an action x'_t classically, may apply O_{x'_t} or its inverse once, and may keep a quantum memory from round to round. Unitaries that do not depend on the instance and measurements are free. The regret after T rounds is Σ_t (max_A μ − μ(x'_t)).

With quantum mean estimation, regret polylogarithmic in T is possible [1, 2]. For general (for example infinite) action sets, the best known regret bounds are O(m² polylog T) [2] and O(m^{3/2} log^{3/2} T log(mT)), the latter implied by [3] (as worked out in [1, Appendix C]). The best known lower bound is Ω(m log(1 + T/m)) [1, Theorem 3.6], from an action set with m actions. In [1] the optimal dependence on the dimension for general action sets is listed as open.

## Result

Take m = d + 1 with d ≥ 3, write D = d − 1, and use the action set

A = { (1, x)/√2 : x ∈ R^d, |x| ≤ 1 },

with parameters θ' = (1, θ)/√2, |θ| ≤ 1/2. Then μ = (1 + ⟨x, θ⟩)/2 ∈ [1/4, 3/4], so the model of [1] applies, and every action is reached through the two-outcome oracle of [1, Section 3].

**Theorem 1.** Let t₀ = ⌈1000 D^{3/2}⌉ and t₁ = 1000 D^{3/2} e^{D/2}. For every learner in the model above and every T ≥ t₀ there is a parameter θ with |θ| ≤ 1/2 such that

E[Regret(T)] ≥ 3.6 · 10⁻⁶ · D^{3/2} · ln( min(T, t₁) / t₀ ).

Here D = m − 2. So the worst-case regret is Ω(m^{3/2} log(T/(1000 m^{3/2}))) for T ≤ e^{c m}, and Ω(m^{5/2}) for larger T. The exponent 3/2 of the dimension in the bound implied by [3] cannot be lowered for general action sets. Previous best lower bound: Ω(m log(1 + T/m)) [1].

The bound covers learners with full quantum memory, adaptive classical choice of actions, and any use of the oracle and its inverse. Each query reveals information about one linear functional ⟨x, θ⟩ only. Coherent use of many queries gives the usual quadratic gain in the precision of that functional, but it cannot spread this gain over d − 1 directions at once.

**Theorem 2.** On the same action set, for every θ' = (1, θ)/√2 with |θ| ≤ 1 and any reward oracles of the model, the phase algorithm below has, for all T ≥ 2,

E[Regret(T)] ≤ (6923 d^{3/2} + 25 d) (log₂ T + 1).

So on this family the regret is Θ(d^{3/2} log T) for t₀² ≤ T ≤ t₁, with no further logarithmic factors. Previous best upper bound: O(m^{3/2} log^{3/2} T log(mT)), implied by [3] as shown in [1]; that bound holds for every parameter, while Theorem 2 uses the known first coordinate of θ'.

## Proof

### The hard family

Write θ = s n with |n| = 1 and n = (√(1 − |y|²), y), y ∈ R^D. The prior draws s and y independently. The radius s has density (2/τ) cos²(π(s − s_c)/τ) on [s₀, s₀ + τ] with s₀ + τ = 1/2 (s_c the midpoint), and y has density Π_j (1/h) cos²(π y_j/(2h)) on [−h, h]^D, h = 1/(4√D). So |y| ≤ 1/4. The Cartesian density is p(θ) = f(s) g(y) n₁ s^{−D}.

The oracle of action x is the two-outcome oracle O_μ = CNOT (R(φ) ⊗ 1), R(φ) the real rotation by φ = arcsin √μ. On [1/4, 3/4], |dφ/dμ| ≤ 2/√3. So the derivative of the oracle along a direction v of θ has norm at most γ |⟨x, v⟩| with γ = 1/√3, and the same holds for the inverse.

Regret and direction: with n = θ/|θ|, the regret of action x is r(x) = (|θ| − ⟨x, θ⟩)/2 ≥ (|θ|/4) |x − n|², because |x − n|² ≤ 2 − 2⟨x, n⟩ for |x| ≤ 1.

### Purification

A register Θ = L²(R^d) holds |θ⟩ with amplitude √p(θ). Measurements of the learner are deferred, and every outcome is also copied into two classical registers E and F that are never touched again. The record r is the sequence of outcomes. The action x_s(r) and the choice between oracle and inverse in round s depend only on the part of r before round s. Given θ, the joint state ψ_t(θ) of the learner L, of E and of F before round t is pure, and the global state is

Φ = ∫ √p(θ) |θ⟩ ⊗ ψ_t(θ) dθ.

If Π_π projects E onto the records that extend a prefix π, it commutes with every later operation, since later operations only append records and are controlled by earlier ones.

### Cells

For the analysis only, cover R^D by cubes of side 2ε with the partition of unity W_k(y) = Π_j cos²(π(y_j − k_j ε)/(2ε)) on |y_j − k_j ε| ≤ ε. Then Σ_k W_k = 1 and Σ_k |∇√W_k|² = D (π/(2ε))². Set w_k(θ) = W_k(y(θ)) and a_k = n(kε). On the support of w_k, |P_{a_k} n(θ)| ≤ δ := ε√D/n₁ with n₁ ≥ √3/2 for ε√D ≤ 1/4, where P_a is the projector onto a^⊥. Apply the instrument {√w_k} to Θ and copy k into E. This leaves the distribution of θ and its correlation with the learner unchanged.

### Uncertainty relation

**Assumption U** (entropic uncertainty relation with quantum memory for position and momentum, in the coarse-grained form of [5, Proposition 11, eq. (98)], see also [4]). For every state on Θ ⊗ B ⊗ C, every cubic grid of side δ_q in position and every cubic grid of side δ_p in momentum P = −i∇,

H(Q_{δ_q} | B) + H(P_{δ_p} | C) ≥ −log c,  c = max_{j,k} ‖Q_j P_k‖² ≤ (δ_q δ_p / (2π))^d,

where the bound on c comes from ‖Q_j P_k‖² ≤ tr(Q_j P_k Q_j) and |⟨θ|p⟩|² = (2π)^{−d} [5, eq. (112)]. The same position and momentum scheme, for a single parameter, gives the resolution limits of [7].

We apply it with B = (L, F) before round t and C = (E, k).

### Momentum side

For a record r and a cell k let Φ_{rk} = ∫ √(w_k p) |θ⟩ ⊗ Π_r ψ_t(θ) dθ, P_{rk} = ‖Φ_{rk}‖², and let M_{rk} = Re⟨∂_i Φ_{rk}, ∂_j Φ_{rk}⟩ / P_{rk} be the second-moment matrix of the momentum in this branch. The gradient splits into a prior part, ∫ ∂_v √(w_k p) |θ⟩ ⊗ Π_r ψ_t, and a query part,

Σ_{s<t} ⟨x_s(r), v⟩ ξ_{s,rk},  ξ_{s,rk} = ∫ √(w_k p) |θ⟩ ⊗ Π_r W_s (−i G_s) ψ_s(θ) dθ,

with ‖G_s‖ ≤ γ and W_s the evolution after query s. The key identity is

Σ_{r extends π} ‖Π_r W_s G_s ψ_s‖² = ‖G_s Π_π ψ_s‖² ≤ γ² P(π | θ).

So a coefficient that depends only on k and on the record before round s can be averaged over the records as if no later branching had happened. This handles the adaptivity.

Split M_{rk} along a_k with the block determinant inequality det M ≤ (a_kᵀ M a_k) · det(P_{a_k} M P_{a_k}).

*Radial direction.* Σ_{rk} P_{rk} a_kᵀ M_{rk} a_k ≤ X_t := 2(R + Tang + Cells) + 2γ² t², with

R = ∫ (∂_s √p)² ≤ π²/τ² + D²/(4 s₀²),  Tang = ∫ |∇_tan √p|² ≤ (D π²/(2h²) + 1/(32 n₁³)) / (s₀² n₁),  Cells = ∫ p Σ_k |∇√w_k|² ≤ D (π/(2ε))² / s₀².

*Tangential directions.* By the inequality of arithmetic and geometric means, (1/2) log det(2πe P M P) ≤ D log(√(2πe) tr((PMP)^{1/2}) / D). The trace of the square root is subadditive, and on the query part it is a nuclear norm, at most Σ_s |P_{a_k} x_s| ‖ξ_{s,rk}‖. On the support of w_k, |P_{a_k} x_s| ≤ |x_s − n(θ)| + δ. Averaging over the branches with the key identity and the triangle inequality in L² gives

E_{rk}[(1/2) log det(2πe M_{rk})] ≤ (1/2) log(2πe X_t) + D log(√(4πe) Y_t / D),

Y_t = √(D T_tan) + γ Σ_{s<t} √(E[(|x_s − n| + δ)²]),  T_tan ≤ 2 Cells + 4 δ² R + 4 Tang.

The binned momentum entropy of each branch is at most (1/2) log det(2πe M̃_{rk}) − d log δ_p, since the normal distribution has the largest entropy at a given second moment. Here M̃_{rk} is the second moment of the binned momentum, and M̃_{rk} ≤ (1 + η) M_{rk} + (1 + 1/η) d δ_p² I for every η > 0. So the whole chain runs with M_{rk} + ε I in place of M_{rk}, which adds ε to the radial part and at most D√ε to tr((P M P)^{1/2}), uniformly over the branches; then ε → 0.

The nuclear norm is where the factor √D comes from. A trace bound would allow information D times larger, as if every query could inform all directions at once.

### Position side

The action x_t is a function of the records in F, so H(Q_{δ_q} | L, F) ≤ H(Q_{δ_q} | x_t). Let θ̃ be the centre of the bin of θ plus an independent uniform point of the bin. Then H(Q_{δ_q} | x_t) = h(θ̃ | x_t) − d log δ_q, and the term d log δ_q cancels against the one in c. In polar coordinates dθ = s^D ds dy / n₁, the radius of θ̃ has a range of length τ + 2δ_q√d, and |θ̃ − θ| ≤ δ_q√d. All steps below are done for θ̃, and δ_q → 0 is taken only in the final moment inequality. This gives

h(y | x_t) ≥ d log 2π − (1/2) log(2πe X_t) − D log(√(4πe) Y_t / D) + log n₁ − D log(s₀ + τ) − log τ.

At fixed second moment the entropy is largest for the normal distribution, so E|y − ŷ|² ≥ (D/(2πe)) exp(2h(y|x_t)/D) for every estimator ŷ. Take ŷ from the direction x_t/|x_t|, with |ŷ − y| ≤ 2|x_t − n|. Then

E|x_t − n|² ≥ D³ b_t / (8 e² (s₀ + τ)² Y_t²),  b_t = (2π n₁² / (e X_t τ²))^{1/D}.

### Parameters and summation

Write t₀' = 1000 D^{3/2}. Choose τ = √D/(γ t₀'), so that γ t τ = √D t/t₀', and in round t ∈ [t₀', t₁] choose ε_t ∝ D^{1/4}/√t (exact value in `sim/lbconst.py`). Then Y_t ≤ γ S_t + β√t / √2 with S_t = Σ_{s<t} √(E|x_s − n|²), and b_t ≥ 0.2. With r_t the expected regret in round t and G_t = Σ_{s<t} √r_s, this gives

r_t ≥ q² / (c G_t² + β² t),  c = 8γ²/s₀,  β² ≤ 244.7 D^{3/2},  q² ≥ 0.00177 D³.

**Lemma S.** If r_t ≥ q²/(c G_t² + β² t) for all rounds t (integers) with t₀ ≤ t < t₁, then Σ_{t<t₁} r_t ≥ min{ L/(2K), β² L/(2c) } with L = ln(t₁/t₀) and K = 2√c/q + β²/q² + c/(β² t₀).

*Proof.* Let V_t = c G_t² + β² t. From r_t ≥ q²/V_t, √r_t ≤ r_t √V_t / q, and so ln(V_{t+1}/V_t) ≤ (2c G_t √r_t + c r_t + β²)/V_t ≤ K r_t. Also V_{t₁} ≥ β² t₁ and V_{t₀} ≤ t₀ (c R + β²), where R is the total, since G_{t₀}² ≤ t₀ R. So L − ln(1 + cR/β²) ≤ K R. Either ln(1 + cR/β²) ≥ L/2, which gives R ≥ β² L/(2c), or K R ≥ L/2. ∎

With the constants above, the minimum is at least 3.6 · 10⁻⁶ D^{3/2} L, which proves Theorem 1. The bound holds for the prior average, so some θ in the support of the prior attains it.

## Algorithm for Theorem 2

*Estimator.* For a mean μ and a register size M, amplitude estimation uses fewer than 2M queries of the oracle and its inverse and returns Y with P(|Y − μ| > πk/M + π²k²/M²) ≤ 1/(2(k − 1)) for k ≥ 2 [6]. The median of 5 independent runs has E(Y − μ)² ≤ 154/M² for every M, using fewer than 10M queries. The constant comes from integrating the binomial tail exactly (`sim/ubconst.py`).

*Phases.* Phase ℓ = 0, 1, 2, … has target error a = 2^{−ℓ}. Let θ̂ be the estimate from the previous phase (θ̂ = 0 at the start), c = θ̂/|θ̂| (any unit vector if θ̂ = 0), s = min(1, a/|θ̂|), and M = ⌈K√d/(s a)⌉ with K = 30.1. Pick an orthonormal basis u₁, …, u_{d−1} of c^⊥. Estimate the means of the 2d − 1 actions c and cos s · c ± sin s · u_j with the estimator above, and set

θ̂_new = (2μ̂(c) − 1) c + Σ_j (μ̂(x_j⁺) − μ̂(x_j⁻)) / sin s · u_j.

Since ⟨x_j⁺ − x_j⁻, θ⟩ = 2 sin s ⟨u_j, θ⟩, this gives E|θ̂_new − θ|² ≤ 4 · 154 d / (M² sin² s) ≤ a².

*Regret of a phase.* A pair has regret r(x_j⁺) + r(x_j⁻) = |θ| − cos s ⟨c, θ⟩ ≤ |θ|(s² + |c − n|²)/2, and the centre has regret at most |θ| |c − n|²/2. So a phase costs at most 5 M d |θ| (s² + |c − n|²). With the previous error e = θ̂ − θ, E|e|² ≤ 4a², one gets E[|θ| s / a] ≤ 6 and E[|θ| |c − n|² / (s a)] ≤ 40, so the expected regret of a phase is at most 5K(6 + 40) d^{3/2} + 25 d ≤ 6923 d^{3/2} + 25 d. Phase ℓ uses M ≥ 2^ℓ, and its centre estimate alone takes 5(2M − 1) ≥ 2^{ℓ+1} rounds, so phase ℓ starts only if 2^ℓ < T. At most log₂ T + 1 phases start before round T, which proves Theorem 2.

## Check

`sim/lbconst.py` recomputes every constant of the proof, with asserts: the choice of ε_t, the bound on Y_t, the factor b_t, the constants of Lemma S. Times are handled in logarithmic form, so the check runs for every D from 2 to 4999. For D ≥ 5000 the script bounds each scaled quantity by its closed form, which is monotone in D, and gets a constant of at least 6.3 · 10⁻⁶. The constant is smallest at D = 2 (3.608 · 10⁻⁶). Run `python sim/lbconst.py`.

`sim/ubconst.py` recomputes the constants of Theorem 2 with asserts: the mean squared error of the median estimator (at most 153.8/M² over the checked register sizes) and the phase constant 6923. `sim/regret_ball.py` runs the phase algorithm with the exact output law of amplitude estimation, for random θ with |θ| between 0.05 and 1, and asserts the bound of Theorem 2. For d = 2, 4, 8, 16 and T up to 10⁸, the mean regret divided by d^{3/2} ln T stays between 5 and 56 with K = 30.1, and between 2.9 and 10.4 with K = 3 (`sim/out_ball.txt`).

## Scope

- **Assuming:** the entropic uncertainty relation with quantum memory for position and momentum, in the coarse-grained form above [4, 5], for Theorem 1, and the error bound of amplitude estimation [6] for Theorem 2. Everything else is proved here on paper.
- **Not formalized:** Theorems 1 and 2 have no Lean proof.
- The lower bound grows like log T only up to T = t₁. The thin radial prior, which keeps the oracle at the best action uninformative, limits the range.
- The constant is small and t₀ ≈ 1000 D^{3/2}. The bound is stated for one action set, the ball above. For finite action sets with K actions, the bound O(m log T log(KT)) of [1] shows that the dimension enters differently.

## References

[1] M. Liu, Z. Li, J. C. S. Lui. Quantum Multi-Armed Bandits and Linear Bandits: Lower Bounds and Algorithms. arXiv:2608.14319.
[2] Z. Wan, Z. Zhang, T. Li, J. Zhang, X. Sun. Quantum Multi-Armed Bandits and Stochastic Linear Bandits Enjoy Logarithmic Regrets. AAAI 2023, arXiv:2205.14988.
[3] Y. Hikima, K. Murao, S. Takemori, Y. Umeda. Quantum kernelized bandits. UAI 2024.
[4] R. L. Frank, E. H. Lieb. Extended quantum conditional entropy and quantum uncertainty inequalities. Commun. Math. Phys. 323 (2013), arXiv:1204.0825.
[5] F. Furrer, M. Berta, M. Tomamichel, V. B. Scholz, M. Christandl. Position-momentum uncertainty relations in the presence of quantum memory. J. Math. Phys. 55 (2014) 122205, arXiv:1308.4527.
[6] G. Brassard, P. Høyer, M. Mosca, A. Tapp. Quantum amplitude amplification and estimation. Contemp. Math. 305 (2002), arXiv:quant-ph/0005055.
[7] M. J. W. Hall, H. M. Wiseman. Does nonlinear metrology offer improved resolution? Answers from quantum information theory. Phys. Rev. X 2 (2012) 041006, arXiv:1205.2405.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
