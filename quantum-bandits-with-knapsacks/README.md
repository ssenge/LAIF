# Quantum bandits with knapsacks: polylogarithmic regret without gap assumptions

2026-11-11

## Problem

In bandits with knapsacks [1, 2] a learner has m arms, d resources with budget B each, and T rounds. Pulling arm i earns reward r_i ∈ [0, 1] in expectation and uses a vector C_i ∈ [0, 1]^d of resources in expectation. The process ends after T rounds or when some resource exceeds its budget. As in [1], time is resource 1 with C_{1,i} = b := B/T for every arm, and the benchmark is the value of the linear program

OPT_LP = max { rᵀξ : Cξ ≤ B·1, ξ ≥ 0 }.

The regret is OPT_LP minus the total reward.

In the quantum version of [1] (Definition 2 there) every arm has a quantum reward oracle O_i^r and a quantum consumption oracle O_i^C that prepare superpositions over the outcomes. In each round the learner queries both oracles of one arm, or their inverses, once. A coherent query earns the expected reward r_i and uses the expected consumption C_i. This is the accounting of [1] for rewards, and for consumption in the estimation rounds of its Algorithm 2. Between rounds the learner keeps its quantum memory.

The problem-independent bound of [1, Theorem 1] is O(√(log(dT)) · OPT_LP √(m/B)) + O(m log(dT) log T). For B and OPT_LP of order T it grows like √(mT). The problem-dependent bound of [1, Theorem 3] grows like log T, but it assumes a unique nondegenerate LP solution and scales with the inverse of an LP gap δ and with b^{−2}. The optimality of these bounds is left open in [1].

## Result

**Theorem 1.** In the model above, the algorithm below has, for every instance and every T ≥ 2,

E[Regret] = O( (1 + OPT_LP/B) · (m √d log(dmT) log² T + m²) ).

The bound depends on T only through logarithms, needs no assumption on the LP and has no gap parameter. Since OPT_LP ≤ T, the factor 1 + OPT_LP/B is at most 1 + 1/b. Previous best bounds: O(√(log(dT)) · OPT_LP √(m/B) + m log(dT) log T) without gap assumptions [1, Theorem 1], and Õ((2 + 1/b) m √d log T/(bδ) + d⁴/(b² min{χ², δ²} min{1, σ²})) for a unique nondegenerate LP with gap δ [1, Theorem 3].

## Algorithm

Add a null arm 0 with r_0 = 0 and C_0 = (b, 0, …, 0). Rounds in which the null arm is chosen are skipped, which only leaves more time. Write x for a distribution over the m + 1 arms.

1. *Estimation.* Each arm i ≥ 1 runs quantum mean estimation [1, Lemmas 2 and 3] on its own rounds, in consecutive blocks of N_0, N_0, 2N_0, 4N_0, … of its rounds. When a block of N rounds ends, the estimates r̂_i and Ĉ_i satisfy |r̂_i − r_i| ≤ ε(N) and ‖Ĉ_i − C_i‖_∞ ≤ ε(N), with ε(N) ≤ a/N and a = O(√d log(dmT) log T), except with probability 1/(T · m(log₂ T + 2)). Until its first block ends an arm has radius ε_i = 1, and afterwards ε_i is the radius of its last completed block. The learner keeps the quantum registers of all running blocks, so blocks of different arms interleave.
2. *Optimistic program.* After every block, solve

   x = argmax { r^Uᵀx : C^L x ≤ b(1 − γ) on the resources j ≥ 2, Σ_i x_i = 1, x ≥ 0 },

   with r^U_i = min(1, r̂_i + ε_i), C^L_i = max(0, Ĉ_i − ε_i), and the slack γ = (W̄ + m + 2)/B, where W̄ = 2m(m + 1 + 4a(1 + ln T)).
3. *Rounding.* In round t add the current x to a running total X(t) and play the arm with the largest deficit X_i(t) − n_i(t − 1), where n_i counts the pulls of arm i.

## Proof

Assume all estimates lie within their radii. The complementary event has probability at most 1/T and costs at most OPT_LP ≤ T.

*Step 1 (rounding).* The deficits D_i(t) = X_i(t) − n_i(t) sum to zero. The chosen arm has the largest deficit before its pull, which is at least 1/(m + 1). So every deficit stays above −1, and every deficit stays below m. The negative parts sum to at most m + 1, and so do the positive parts.

*Step 2 (optimism).* Since r ≤ r^U and C ≥ C^L, the distribution (1 − γ)x* + γ e_0, built from an optimal solution x* = ξ*/T of the per-round program, is feasible for the optimistic program. Hence r^Uᵀx_t ≥ (1 − γ) OPT_LP/T in every round.

*Step 3 (widths).* Let w_t = 2 Σ_i x_{t,i} ε_{i,t}. Then rᵀx_t ≥ r^Uᵀx_t − w_t and C_j x_t ≤ C^L_j x_t + w_t ≤ b(1 − γ) + w_t for every resource. After n pulls of arm i its last completed block has more than n/4 rounds, so ε_{i,t} ≤ min(1, 4a/n_i(t − 1)), and n_i(t − 1) ≥ X_i(t − 1) − m by Step 1. Since x_{t,i} ≤ 1 and the bound decreases,

Σ_t x_{t,i} ε_{i,t} ≤ ∫₀^T min(1, 4a/(u − m − 1)⁺) du ≤ m + 1 + 4a(1 + ln T),

so W := Σ_t w_t ≤ W̄.

*Step 4 (budget and reward).* After t ≤ T rounds resource j has used Σ_i n_i(t) C_{j,i} ≤ Σ_{s≤t} C_j x_s + (m + 1) ≤ B(1 − γ) + W + m + 1 < B. So no resource is exceeded, and all T rounds earn their reward. The total reward is

Σ_i n_i(T) r_i ≥ Σ_t rᵀx_t − (m + 1) ≥ (1 − γ) OPT_LP − W − (m + 1).

So the regret is at most γ OPT_LP + W + m + 1 ≤ (W̄ + m + 2)(1 + OPT_LP/B), which gives Theorem 1. If W̄ + m + 2 ≥ B the bound exceeds OPT_LP and holds trivially.

## Check

`sim/bwk.py` runs the algorithm on three random instances with m = 6 arms, three resources besides time, b = 1/4 and T up to 10⁶. Quantum mean estimation is modelled by its guarantee: a block of N rounds returns estimates within a/N with a = 2. The script asserts that no resource is exceeded, that every deficit stays in [−1, m], that W ≤ W̄, and that the regret stays below γ OPT_LP + W + m + 1. The regret grows by about 300 for each factor 10 in T, from 1500 at T = 10⁴ to 2100 at T = 10⁶ on the first instance (output in `sim/bwk_out.txt`).

## Scope

- **Assuming:** the quantum mean estimators of [1, Lemmas 2 and 3].
- **Not formalized:** the theorem has no Lean proof.
- **Model:** consumption is charged in expectation for coherent queries, as in the estimation rounds of [1, Algorithm 2]. The setting of [1, Algorithm 1], where every consumption query is measured and the sample is charged, is not covered.
- The rounding of Step 3 uses the simple greedy schedule, whose deficits are at most m; the online greedy schedule is known to keep them at O(log m) [3], which would reduce the m² term to m log m.

## References

[1] Y. Su, Z. Yang, P. Huang, T. Li, Y. Ye. Quantum Algorithms for Bandits with Knapsacks with Improved Regret and Time Complexities. arXiv:2507.04438.
[2] A. Badanidiyuru, R. Kleinberg, A. Slivkins. Bandits with knapsacks. FOCS 2013, arXiv:1305.2545.
[3] D. Coppersmith, T. Nowicki, G. Paleologo, C. Tresser, C. W. Wu. The optimality of the online greedy algorithm in carpool and chairman assignment problems. ACM Transactions on Algorithms 7(3):37 (2011).

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
