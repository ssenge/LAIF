# Capped constant escapement for annual hunting seasons

Written 25 Nov 2026.

**Setting.** Hunting happens once a year. Let Y_t be the population before the season. The season leaves
an escapement S_t with max(0, Y_t − Q) ≤ S_t ≤ Y_t, so the cull Y_t − S_t is at most a quota cap Q (Q = ∞
means no cap). Next year's population is Y_{t+1} = F(S_t, ξ_{t+1}), where the ξ_t are independent and
identically distributed environmental factors. Two criteria are used: the expected discounted yield
E Σ αᵗ (Y_t − S_t), and the long-run average yield. A threshold rule culls min(Q, (Y − w)⁺): it leaves the
population at the target w when the cap allows, culls Q when the population is too far above w, and culls
nothing at or below w.

It is stated in [1, Section 3.3] that, to the authors' knowledge, it has not been shown in discrete time in
general that the expected steady-state yield is maximized by such a threshold (bang-bang) rule. Without a
cap, constant escapement maximizes the expected discounted revenue [2].

## Results

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Optimal cull rule for annual seasons with a quota cap | Without a cap: constant escapement maximizes the discounted revenue [2]. For the long-run average yield in discrete time, optimality of threshold rules in general is stated as not shown in [1, Section 3.3] | With a cap Q, for every horizon and discount factor the optimal rule is the threshold rule min(Q, (y − w)⁺). This holds when (a) each F(·, ξ) is concave and nondecreasing, or (b) each F(·, ξ) is nondecreasing and concave up to a level ĥ, never larger beyond ĥ than at ĥ, and all populations stay at most ĥ + Q. Case (b) includes Ricker recruitment (ĥ = 1/r); without a cap it covers overcompensating recruitment in general. The long-run average optimum has the same form | Lean: the Bellman step (the threshold rule is optimal, and concavity and monotonicity of the value carry over to the next step), for (a) and (b). Claim: the induction over horizons and the limit to the long-run average |
| Table | Optimal target w* and yield | | w* and the long-run yield for Beverton–Holt and Ricker recruitment with lognormal noise, 240 parameter sets; in every set the optimal policy found over all policies is the threshold rule, within the grid spacing | Numerical |

## Statements

Write φ(s) = −s + α E V(F(s, ξ)) for the continuation value of escapement s. The value of escapement s at
population y is y + φ(s). The threshold rule with target w leaves esc(w, Q, y) = max(max(0, y − Q), min(w, y)).

**Lemma 1 (clamp).** Let φ be concave on [0, ∞) with a maximizer w ≥ 0. Over the feasible interval
[max(0, y − Q), y], the maximum of y + φ(s) is attained at esc(w, Q, y).

*Proof.* Suppose w lies below the interval and s is in it. Then the left end lies between w and s, and by
concavity φ there is at least min(φ(w), φ(s)) = φ(s). The case of w above the interval is symmetric. ∎

**Lemma 2 (the value step).** Under Lemma 1, V(y) = y + φ(esc(w, Q, y)) is concave. If s + φ(s) is
nondecreasing, V is nondecreasing.

*Proof.* Take two states y₁, y₂ with optimal escapements e₁, e₂. The same convex combination of e₁ and e₂
is feasible for the combined state, so concavity of φ and Lemma 1 give concavity of V. For monotonicity,
compare y₁ ≤ y₂ through the feasible escapement max(e₁, y₂ − Q) at y₂. ∎

**Lemma 3 (the next step).** If V is concave and nondecreasing and each F(·, ξ) is concave and
nondecreasing, then the next φ is concave and s + φ(s) = α E V(F(s, ξ)) is nondecreasing.

**Lemma 4 (hump-shaped recruitment).** Lemmas 1 to 3 hold with [0, ĥ] in place of [0, ∞) for φ and F, and
with [0, ĥ + Q] for the states. The hypotheses are: each F(·, ξ) is concave and nondecreasing on [0, ĥ],
F(s, ξ) ≤ F(ĥ, ξ) for s ≥ ĥ, and 0 ≤ F ≤ ĥ + Q. Under these, the next φ also satisfies φ(s) ≤ φ(ĥ) for s ≥ ĥ.

**Theorem 1.** Starting from V₀(y) = y, value iteration keeps the hypotheses of Lemmas 1 to 3 (or of
Lemma 4). The maximizer of each φ exists when F is continuous and bounded. So the optimal rule for every
horizon is a threshold rule. The discounted value is the limit, and the threshold rule is discount-optimal
with a target w_α. For the long-run average yield, take w̄ as a limit point of w_α as α → 1. The
vanishing-discount argument for average-reward Markov control [3, Chapter 5] makes the threshold rule with
target w̄ average-optimal, under bounded rewards and relative values that stay bounded on compact subsets
of the persisting states.

**Properties of w\*.** These were computed for both families with lognormal noise, mean 1:
- Without a cap, small noise gives w* close to the deterministic optimum x₁ (where ∂ₛE F = 1). For
  Beverton–Holt and for Ricker with r ≤ 1.5, w* stays nondecreasing in σ. For Beverton–Holt R = 2 it is
  0.41 at σ = 0.1 and 0.46 at σ = 0.6, with x₁ = 0.414. For Ricker r = 2.5 it decreases to 0.31 at σ = 0.6,
  below x₁ = 0.326.
- With a cap, w* is never above the uncapped value in the table, and often far lower. For Beverton–Holt R = 2, σ = 0.3, Q = 0.15 it is 0.24, with
  x₁ = 0.414.
- When the cap is reached every year (the yield equals Q), every low enough target gives the same yield, so
  w* is not unique; the table lists the largest.

Units: populations and Q are in units of the carrying capacity K. Beverton–Holt F = ξ R s / (1 + (R − 1) s);
Ricker F = ξ s e^{r(1 − s)}; ξ = e^{σZ − σ²/2}.

## Scope

- Lemmas 1 to 4 are machine-checked as single Bellman steps. The induction over horizons, the existence of
  the maximizers, the discounted limit and the vanishing-discount limit are written arguments (Claim).
- Case (b) with a cap needs F ≤ ĥ + Q, that is bounded noise. In the table, Ricker cases with a cap also give
  threshold rules where this bound fails.
- The table uses noise truncated by 31-point Gauss–Hermite quadrature, a log-spaced grid of 1201 states on
  [0, 4], and 1500 steps of relative value iteration.
- One population class, the season after the count, and exact knowledge of the population.

## Lean

`lean/SeasonalEscapement/`, built against Mathlib, standard axioms only (`lean/axioms.txt`):

- `Bellman.lean`:
  - `le_clamp`, `esc_optimal`: Lemma 1.
  - `value_concave`, `value_monotone`: Lemma 2.
  - `next_concave`: Lemma 3, with the expectation as an integral over any measure.
  - `nonvacuous`: φ(s) = min(s, 2 − s) satisfies all hypotheses. A worked case shows that the cap changes
    the cull: target 1, cap 1/2 and population 3 leave 5/2.
- `Hump.lean`:
  - `le_clamp_on`: Lemma 1 on any convex set.
  - `esc_optimal_hump`, `value_concave_hump`, `value_monotone_hump`, `next_hump`: Lemma 4.
  - `nonvacuous_hump`: an instance of the hypotheses on [0, 1].

## Scripts

- `sim/avg_dp.py`: relative value iteration for the long-run average yield over all policies, on a log grid
  with the escapement y − Q taken off the grid, and the check that the optimal policy is a threshold rule.
- `sim/table.py`: writes `sim/data/wstar.csv`. Each row holds the model, parameter, σ, Q, w*, the yield and
  the largest deviation of the optimal policy from the threshold rule.
- `sim/escapement.py`: w* and this year's cull for given parameters
  (`python escapement.py bh 2.0 0.3 0.15 0.8`). The self-check compares the yield of the threshold rule with
  the optimum over all policies.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check
proofs, to write the Lean files and the scripts, and to draft the text.

## References

1. A. Hening. Coexistence, extinction, and optimal harvesting in discrete-time stochastic population models.
   J. Nonlinear Sci. 31 (2021), article 1. arXiv:1911.08398.
2. W. J. Reed. Optimal escapement levels in stochastic and deterministic harvesting models. J. Environ. Econ.
   Manag. 6 (1979) 350–363.
3. O. Hernández-Lerma, J. B. Lasserre. Discrete-Time Markov Control Processes. Springer, 1996.
