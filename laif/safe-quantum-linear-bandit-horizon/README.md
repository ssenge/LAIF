# Safe quantum linear bandits: regret O(d^{3/2} log T) with round-wise safety

2026-11-25

## Problem

The setting is the classical-action, coherent-feedback model of [1, Definition A.1]:

- The action set A ⊆ ℝ^d is compact and convex. Every action, the reward vector θ and each constraint row φ_i, i ≤ m, have ℓ₂ norm at most 1.
- At each query the learner picks an action a ∈ A classically and applies a unitary O_a or its inverse. O_a prepares a coherent sample of the feedback X(a) ∈ [0, 1]^{1+m}, whose mean is (⟨θ, a⟩, ⟨φ_1, a⟩, …, ⟨φ_m, a⟩).
- Each query counts as one round. The regret is Reg(T) = Σ_t Δ(a_t), where Δ(a) = ⟨θ, a*⟩ − ⟨θ, a⟩ and a* is the best feasible action.
- Round-wise mean safety requires ⟨φ_i, a_t⟩ ≤ α_i for every queried action and every i, with high probability.
- The learner knows the thresholds α and a baseline u ∈ A with slack Γ = min_i(α_i − ⟨φ_i, u⟩) > 0, but not Γ itself.
- Since the constraint means lie in [0, 1], replacing α_i by min{α_i, 1} changes no feasibility, so Γ ≤ 1.

In [1, Theorem B.17], an algorithm with exact global optimization is safe with probability 1 − δ and has Reg(T) = Õ(√(m + 1) d^{3/2} log^{3/2}(2T)(1 + Δ(u)/Γ)). The factor log^{3/2} T comes from a confidence radius that grows like √s over S = O(d log T) stages. The lower bound Ω(d^{3/2} log(1 + T/d^{3/2})) holds already with inactive constraints [1, Theorem B.18]. In [1, Section 5], one of the questions left open is whether log^{3/2} T can be sharpened to log T.

| | regret |
|---|---|
| Previous best bound, safe [1, Theorem B.17] | Õ(√(m + 1) d^{3/2} log^{3/2}(2T)(1 + Δ(u)/Γ)) |
| Theorem 1, safe, same Õ convention | Õ(√(m + 1) d^{3/2} log T · (1 + Δ(u)/Γ) + √(m + 1) Δ(u)/Γ) |
| Corollary 2, safe, explicit, in expectation | O((m + 1) d^{3/2} log T · log((m + 1)dT/Γ) · (1 + Δ(u)/Γ)) |
| No constraints, compact action sets, implied by [2, Theorem 4.5] and [3] on a 1/T-net | O(d^{3/2} log T log(dT)) in expectation |
| Lower bound [1, Theorem B.18] | Ω(d^{3/2} log(1 + T/d^{3/2})) |

For fixed m and Γ, Corollary 2 reaches with round-wise safety the rate O(d^{3/2} log T log(dT)) that is known without constraints.

## Results

Let Q(η, δ′) be the number of queries of a mean estimator that returns, with probability at least 1 − δ′, all 1 + m coordinates of the mean of X(a) within η. Two choices are available:

- the multivariate estimator of [1, Theorem 3.2], with Q = Õ(√(m + 1)/η), where Õ hides factors polylogarithmic in m, 1/η and 1/δ′;
- the scalar estimator [2, Lemma 2.1] for each coordinate, with failure probability δ′/(m + 1) each, which gives Q ≤ C(m + 1) log((m + 1)/δ′)/η for an absolute constant C.

The n-th call has failure probability δ_n = 6δ/(π² n²). The algorithm makes at most N = log₂(36/Γ) + 1 + 4d(log₂ T + 1) calls. Write q̄ ≥ 1 for the largest value of η max{Q(η, δ_n), 1/η} over n ≤ N.

**Theorem 1.** The algorithm below satisfies round-wise mean safety with probability at least 1 − δ. On the same event, for every T ≥ 2,

Reg(T) ≤ Δ(u)(72 q̄/Γ + log₂(36/Γ) + 1) + (368/7) d (6√d q̄ + 1)(1 + Δ(u)/Γ)(log₂ T + 1).

With the estimator of [1, Theorem 3.2] this is Õ(√(m + 1) d^{3/2} log T · (1 + Δ(u)/Γ)) plus a warm-up term Õ(√(m + 1) Δ(u)/Γ). Here Õ hides the factors of that estimator and of 1/δ, as in [1, Theorem B.17].

**Corollary 2.** With the scalar estimator, q̄ ≤ C(m + 1) log((m + 1)π² N²/(6δ)). So, with probability at least 1 − δ, every queried action is feasible and

Reg(T) = O((m + 1) d^{3/2} log T · log((m + 1) d log(T)/(Γδ)) · (1 + Δ(u)/Γ)).

With δ = 1/T, the regret on the failure event is at most 2T, so it adds at most 2 in expectation, and

E[Reg(T)] = O((m + 1) d^{3/2} log T · log((m + 1)dT/Γ) · (1 + Δ(u)/Γ)).

## Algorithm

Write e_ℓ = 2^{−ℓ} for the target accuracy of phase ℓ, with e_0 = 1, and set C_1 = A.

**Warm-up.** For j = 1, 2, …, estimate the mean of X(u) within ω_j = 2^{−j}, and set Γ̂_j = min_i(α_i − ĉ_i(u)) − ω_j. Stop at the first j with Γ̂_j ≥ 16ω_j, and keep Γ̂ = Γ̂_j, ω = ω_j and the estimates ŵ = (ŵ_θ, ŵ_1, …, ŵ_m) of the mean at u.

**Phase ℓ = 1, 2, … (until T queries are used).**

1. *Mixtures.* Set ρ_ℓ = Γ̂/(Γ̂ + 2e_{ℓ−1}) and M_ℓ = (1 − ρ_ℓ)u + ρ_ℓ C_ℓ, and let r ≤ d be the dimension of span(M_ℓ).
2. *Design.* Choose a design π on M_ℓ with support S ⊆ M_ℓ, |S| ≤ 4r, and V = Σ_{a ∈ S} π_a a aᵀ such that Range(V) = span(M_ℓ) and g(π) = max_{y ∈ M_ℓ} ‖y‖²_{V⁺} ≤ 9r. Such a design exists by Lemma 0.
3. *Estimation.* At every a ∈ S, run the mean estimator with accuracy η_ℓ = ρ_ℓ e_ℓ/(6√d), padded with further queries at a to at least ⌈1/η_ℓ⌉ queries, obtaining Y_a. For each coordinate g ∈ {θ, φ_1, …, φ_m} set ĝ = V⁺ Σ_a π_a a Y_a(g) and, for x ∈ C_ℓ,

   ĝ_ℓ(x) = (⟨ĝ, (1 − ρ_ℓ)u + ρ_ℓ x⟩ − (1 − ρ_ℓ) ŵ_g)/ρ_ℓ,

   which is affine in x.
4. *Elimination.* Let R*_ℓ be the largest value of the pessimistic reward

   L(s, z) = s(ŵ_θ − ω) + (1 − s)(θ̂_ℓ(z) − e_ℓ)

   over s ∈ [0, 1] and z ∈ C_ℓ, subject to s(ŵ_i + ω) + (1 − s)(φ̂_{i,ℓ}(z) + e_ℓ) ≤ α_i for every i. In the variables (s, (1 − s)z) this is a linear program over a convex set. Then set

   C_{ℓ+1} = {x ∈ C_ℓ : φ̂_{i,ℓ}(x) ≤ α_i + e_ℓ for all i, θ̂_ℓ(x) ≥ R*_ℓ − e_ℓ}.

Every set C_ℓ is compact and convex. As in [1, Theorem B.17], computation is not counted: the design and the linear program are taken as exact.

## Proof

All statements below hold on the event that every call of the estimator meets its accuracy. That event has probability at least 1 − Σ_n δ_n = 1 − δ.

**Lemma 0 (designs).** Let M be a compact set spanning a space of dimension r. Then there is a design on M with support at most 4r points of M, Range(V) = span(M) and g ≤ 9r.

*Proof.* Work in coordinates of span(M).

1. By the equivalence theorem for optimal designs [4, Theorem 21.1], there is a design π* with support at most r(r + 1)/2 points, V* invertible and g(π*) = r. Since Σ_a π*_a aᵀV*⁻¹a = tr(I_r) = r and every term is at most r, every support point has aᵀV*⁻¹a = r.
2. Put v_a = √π*_a V*^{−1/2} a. Then Σ_a v_a v_aᵀ = I_r and ‖v_a‖² = π*_a r. By the spectral sparsification theorem [5, Theorem 3.1] with parameter 4, there are s_a ≥ 0, at most 4r of them nonzero, with I_r ≼ Σ_a s_a v_a v_aᵀ ≼ 9 I_r.
3. Taking traces, σ := Σ_a s_a π*_a ≤ 9. The design π_a = s_a π*_a/σ then has V = V*^{1/2}(Σ_a s_a v_a v_aᵀ)V*^{1/2}/σ ≽ V*/9.
4. So V is invertible on span(M), and g(π) ≤ 9 g(π*) = 9r.

**Lemma 1 (warm-up).** Γ̂ ≤ Γ, ω ≤ Γ̂/16 ≤ Γ/16 and Γ̂ ≥ 7Γ/8. The warm-up uses at most 72 q̄/Γ + log₂(36/Γ) + 1 queries, all at u.

*Proof.* Every ĉ_i(u) lies within ω_j of ⟨φ_i, u⟩, so Γ − 2ω_j ≤ Γ̂_j ≤ Γ. The stopping rule gives ω ≤ Γ̂/16, so Γ̂ ≥ Γ − 2ω ≥ Γ − Γ/8. The rule triggers as soon as 18ω_j ≤ Γ, so, as Γ ≤ 1, the last ω is above Γ/36. The costs q̄/ω_j + 1 then form a geometric sum.

**Lemma 2 (accuracy).** For every phase ℓ, every x ∈ C_ℓ and every coordinate g, |ĝ_ℓ(x) − ⟨g, x⟩| ≤ e_ℓ.

*Proof.* Since Range(V) = span(M_ℓ), for y ∈ M_ℓ we have ⟨ĝ, y⟩ − ⟨g, y⟩ = Σ_a π_a (yᵀV⁺a)(Y_a(g) − ⟨g, a⟩).

- The inner-product inequality for the weights π bounds this by ‖y‖_{V⁺} η_ℓ ≤ 3√d η_ℓ = ρ_ℓ e_ℓ/2.
- For x ∈ C_ℓ, apply this at y = (1 − ρ_ℓ)u + ρ_ℓ x. Then |ĝ_ℓ(x) − ⟨g, x⟩| ≤ e_ℓ/2 + ((1 − ρ_ℓ)/ρ_ℓ) ω.
- Here (1 − ρ_ℓ)/ρ_ℓ = 2e_{ℓ−1}/Γ̂ = 4e_ℓ/Γ̂, and ω ≤ Γ̂/16, so the second term is at most e_ℓ/4.

The bound uses only the accuracy of each estimate, not independence or zero mean of the errors. Each phase starts afresh, so its confidence width does not grow with the number of phases.

**Lemma 3 (safety).** Every queried action is feasible.

*Proof.* The warm-up queries u. For ℓ ≥ 2 and x ∈ C_ℓ, the elimination of phase ℓ − 1 and Lemma 2 give ⟨φ_i, x⟩ ≤ α_i + 2e_{ℓ−1}. For ℓ = 1 the same holds with e_0 = 1, since ⟨φ_i, x⟩ ≤ ⟨φ_i, u⟩ + 2 ≤ α_i + 2. A queried action y = (1 − ρ_ℓ)u + ρ_ℓ x therefore satisfies

⟨φ_i, y⟩ ≤ (1 − ρ_ℓ)(α_i − Γ) + ρ_ℓ(α_i + 2e_{ℓ−1}) ≤ α_i,

because (1 − ρ_ℓ)Γ ≥ (1 − ρ_ℓ)Γ̂ = 2ρ_ℓ e_{ℓ−1}.

**Lemma 4 (elimination).** For every ℓ ≥ 1: a* ∈ C_ℓ, and every x ∈ C_ℓ has Δ(x) ≤ (30/7) e_{ℓ−1}(1 + Δ(u)/Γ).

*Proof.* For ℓ = 1, Δ(x) ≤ 2 ≤ 30/7. Assume the claim for ℓ and write e = e_ℓ.

- *Every feasible pair is truly feasible.* By Lemmas 1 and 2, each pair (s, z) allowed in the linear program gives an action y = su + (1 − s)z that is truly feasible, with ⟨θ, y⟩ ≥ L(s, z). So R*_ℓ ≤ ⟨θ, a*⟩.
- *a* survives.* The estimates at a* lie within e of the truth, so a* passes both tests: φ̂_{i,ℓ}(a*) ≤ α_i + e, and θ̂_ℓ(a*) ≥ ⟨θ, a*⟩ − e ≥ R*_ℓ − e.
- *R*_ℓ is close to the optimum.* Take z = a* and s = 2e/(Γ − 2ω + 2e) ≤ 16e/(7Γ). The constraint of the program holds, since

  s(ŵ_i + ω) + (1 − s)(φ̂_{i,ℓ}(a*) + e) ≤ α_i − s(Γ − 2ω) + (1 − s)2e ≤ α_i.

  Its reward is L ≥ ⟨θ, a*⟩ − sΔ(u) − 2sω − 2e ≥ ⟨θ, a*⟩ − (16/7)(e Δ(u)/Γ) − (16/7)e.
- *Every survivor is near-optimal.* A survivor x has ⟨θ, x⟩ ≥ θ̂_ℓ(x) − e ≥ R*_ℓ − 2e. Hence Δ(x) ≤ 2e + (16/7)e(1 + Δ(u)/Γ) ≤ (30/7)e(1 + Δ(u)/Γ).

**Proof of Theorem 1.**

- *Gap of a queried mixture.* By Lemma 4 and 1 − ρ_ℓ ≤ 2e_{ℓ−1}/Γ̂ ≤ 16e_{ℓ−1}/(7Γ), a queried mixture y = (1 − ρ_ℓ)u + ρ_ℓ x has Δ(y) = (1 − ρ_ℓ)Δ(u) + ρ_ℓΔ(x) ≤ (46/7) e_{ℓ−1}(1 + Δ(u)/Γ). Slightly infeasible points x with Δ(x) < 0 only lower this.
- *Queries of a phase.* Phase ℓ makes at most |S| ≤ 4d calls, each with at most q̄/η_ℓ + 1 = 6√d q̄/(ρ_ℓ e_ℓ) + 1 queries.
- *Regret of a phase.* Using (1 − ρ_ℓ)/ρ_ℓ ≤ (32/7)e_ℓ/Γ, the main part is at most

  4d · 6√d q̄ [((1 − ρ_ℓ)/ρ_ℓ)Δ(u)/e_ℓ + (30/7)(e_{ℓ−1}/e_ℓ)(1 + Δ(u)/Γ)] ≤ (92/7) · 24 d^{3/2} q̄ (1 + Δ(u)/Γ).

  The extra query per call adds at most 4d (46/7) e_{ℓ−1}(1 + Δ(u)/Γ).
- *Number of phases.* Phase ℓ uses at least 1/η_ℓ ≥ 2^ℓ queries, by the padding, so at most log₂ T + 1 phases start, the last possibly truncated.
- *Total.* Adding the warm-up of Lemma 1 gives the bound.

**Corollary 2.** The number of calls is at most N, so the scalar estimator gives q̄ ≤ C(m + 1) log((m + 1)π² N²/(6δ)), and log N = O(log(d log(T)/Γ)). Inserting this into Theorem 1 gives the high-probability bound. For the expectation, note Δ ≤ 2.

## Check

`sim/phased.py`, output in `sim/out_phased.txt`, runs the algorithm in d = 2 with one constraint on random octagons in the unit disc, with slack Γ ∈ {0.02, 0.1, 0.4}.

- The mean estimator is replaced by its guarantee: each estimate is off by exactly η in every coordinate, and costs ⌈1/η⌉ queries. The signs either alternate between calls or are drawn at random per coordinate.
- The design is a conditional-gradient design on the vertices of M_ℓ with g ≤ 2r. The script asserts g ≤ 2r and the range condition. The support bound of Lemma 0 is not used.
- The script asserts the following for 10 seeds, both sign patterns, and T up to 10⁷:
  - every queried action is feasible;
  - Lemma 1 holds, including its query count;
  - the estimates are within e_ℓ on every vertex of C_ℓ;
  - a* survives every phase;
  - Lemma 4 holds on C_ℓ;
  - every queried mixture has gap at most (46/7) e_{ℓ−1}(1 + Δ(u)/Γ);
  - each phase stays within its regret bound.
- The ratio Reg(T)/((1 + Δ(u)/Γ) log₂ T) is at most 106.8 at T = 10⁶ and 10⁷ for both sign patterns, and at most 93.7 at T = 10⁵.
- Double precision limits the check to T ≤ 10⁷: at T = 10⁸, C_ℓ has diameter about 10⁻⁶ and the design matrix has condition number about 10¹¹.

## Scope

- Theorem 1 counts queries. As in [1, Theorem B.17], the design over M_ℓ is assumed to be computed exactly. The elimination step is a linear program over C_ℓ. The efficient algorithm of [1, Theorem 1.4] is not matched.
- The bound keeps the factor (1 + Δ(u)/Γ) on the main term, as in [1]. Whether the inverse slack must multiply the dimension and horizon factors is left open in [1, Section 5], and Theorem 1 does not address it.
- The explicit form of Corollary 2 has the factor m + 1 of coordinatewise estimation in place of √(m + 1).
- The mean estimators, the equivalence theorem for optimal designs [4] and the spectral sparsification theorem [5] are used as stated. The statements are Claims with the listed checks.

## References

1. Safe Quantum Stochastic Linear Bandits. arXiv:2611.29904 (2026).
2. M. Liu, Z. Li, J. C. S. Lui. Regret Bounds for Quantum Linear Bandits. arXiv:2611.15237 (2026).
3. M. Liu, Z. Li, J. C. S. Lui. Quantum multi-armed bandits and linear bandits: lower bounds and algorithms. arXiv:2608.14319 (2026).
4. T. Lattimore, C. Szepesvári. Bandit Algorithms. Cambridge University Press, 2020, Chapter 21.
5. J. Batson, D. A. Spielman, N. Srivastava. Twice-Ramanujan sparsifiers. SIAM Journal on Computing 41(6), 2012.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
