# Unique optimal threshold for harvesting a fluctuating population at a bounded rate

Written 25 Nov 2026.

**Setting.** A population in a random environment follows the stochastic logistic equation of [1],
dX = X(μ − κX − h) dt + σX dB, with growth rate μ, competition κ, noise σ and a harvesting rate h(t) ∈ [0, M]
that is capped at M, as hunting or fishing effort is in practice. The goal is the largest long-run average yield
lim (1/T) ∫₀ᵀ X h dt. For μ > σ²/2 (the population persists without harvesting), an optimal strategy is of
threshold type [1, Theorem 2.1]: harvest at the full rate M when X is above a threshold η, and not at all below it.
The long-run yield H(η) of the threshold η is an explicit ratio of integrals [1, eq. (4.4)]. It was conjectured in
[1, Conjecture 4.1], with numerical support, that H has exactly one critical point, so that the optimal threshold
is unique.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Is the optimal harvesting threshold unique? | Conjectured in [1, Conjecture 4.1]; a uniqueness lemma for harvesting quotas that depend on the population [2, Lemma 5.4] assumes ∫₀ m₀ < ∞, which here means μ − M > σ²/2, and a natural boundary at ∞ | Yes, for all μ > σ²/2, κ > 0, M > 0: H has exactly one critical point η*, it increases before η* and decreases after it, and η* is the optimal threshold. This includes μ − M ≤ σ²/2, the case of Figure 1 of [1] | Uniqueness of the critical point: Lean, for all parameters. Existence of the maximizer: Lean assuming [1, Theorem 2.1], and a written proof below (Claim). Monotonicity on each side and optimality among all strategies: Claim |
| Prop 2 | Computing the optimal threshold | none known to us | H in closed form with incomplete gamma functions; η* = σ²ξ/(2κ), where ξ depends only on a = 2μ/σ² and β = 2M/σ²; bisection on an explicit sign function S finds ξ | Claim; checked by script |

## 1. The yield as a mean of the growth

Write s = 2/σ², f(y) = y(μ − κy) for the total growth, and

m(y) = y^{sμ−2} e^{−sκy},  m₀(y) = y^{s(μ−M)−2} e^{−sκy},  λ(η) = η^{sM},

so that m(η) = λ(η) m₀(η). Multiplying both branches of the stationary density (4.3) of [1] by the same constant
shows that it is proportional to m on (0, η] and to λ(η) m₀ on (η, ∞). With A = ∫₀^η m, B = ∫_η^∞ m₀,
P = ∫₀^η f m and Q = ∫_η^∞ f m₀, the yield (4.4) of [1] is H(η) = Mλ ∫_η^∞ y m₀(y) dy / (A + λB).

**Lemma 1.** H(η) = (P + λQ)/(A + λB): the yield equals the stationary mean of the growth.

*Proof.* (y²m)′ = s f m and (y²m₀)′ = s(f − My) m₀. Integrating, with y²m → 0 at 0 (since sμ > 1) and y²m₀ → 0 at
∞, gives sP = η²m(η) and s(Q − M∫_η^∞ y m₀) = −η²m₀(η). Multiply the second by λ and add, using λm₀(η) = m(η). ∎

**Lemma 2.** With G = P/A and K = Q/B, the mean growth below and above the threshold,
H′(η) = λ′AB(K − G)/(A + λB)², so the sign of H′ is the sign of K − G.

*Proof.* The terms from the moving endpoint cancel because m(η) = λm₀(η): (P + λQ)′ = λ′Q and (A + λB)′ = λ′B. ∎

**Lemma 3.** Every zero of D = K − G is a strict down-crossing.

*Proof.* G′ = (m/A)(f − G) and K′ = (m₀/B)(K − f). At a zero with common value v, D′ = (v − f(η))(m₀/B + m/A). If η
is at most the peak μ/(2κ) of f, then f increases on (0, η], so its mean G is below f(η). If η is beyond the peak,
f decreases on [η, ∞), so its mean K is below f(η). In both cases v < f(η) and D′ < 0. ∎

A differentiable function whose derivative is negative at every zero has at most one zero, so H has at most one
critical point.

**Lemma 4 (a maximizer exists).** H > 0 on (0, ∞) and H → 0 as η → ∞. If ∫₀ m₀ < ∞ (μ − M > σ²/2), then G → 0 and
K → M∫₀^∞ y m₀ / ∫₀^∞ m₀ > 0 as η → 0, so H increases near 0. Otherwise H(η) ≤ M∫_η^∞ y m₀ / ∫_η^∞ m₀, the mean of y
under m₀ restricted to (η, ∞), which tends to 0 because ∫_η^∞ m₀ → ∞. In both cases H attains its maximum inside
(0, ∞). ∎

**Theorem 1.** For all μ > σ²/2, κ > 0 and M > 0, H has exactly one critical point η* ∈ (0, ∞). H increases on
(0, η*] and decreases on [η*, ∞), η* is the unique optimal threshold, and harvesting at rate M above η* and not
below is an optimal strategy.

*Proof.* Lemmas 2 to 4. By [1, Theorem 2.1], some threshold strategy is optimal among all admissible strategies;
every threshold strategy is admissible, so its threshold maximizes H and equals η*. ∎

The same argument works for a general growth function whose total growth f is strictly increasing and then
strictly decreasing, and for harvesting rates capped by a positive function k(X) of the population, as in [2]:
there λ(η) = exp(∫^η 2k(z)/σ²(z) dz) is again increasing.

## 2. Closed form and algorithm

Let a = 2μ/σ², β = 2M/σ², α = a − β and x = 2κη/σ². With the lower and upper incomplete gamma functions γ and Γ,

H(η) = (Mσ²/(2κ)) · x^β Γ(α, x) / (γ(a − 1, x) + x^β Γ(α − 1, x)),

and the recurrences of γ and Γ turn the sign of K − G into the sign of

S(x) = (βΓ(α, x) − x^α e^{−x}) γ(a − 1, x) − x^a e^{−x} Γ(α − 1, x).

So the optimal threshold is η* = σ²ξ/(2κ), where ξ = ξ(a, β) is the unique zero of S, and the optimal yield is
(Mσ²/(2κ)) h(a, β). H and S are elementary when a and α are integers with a ≥ 2 and α ≥ 2; for integer α ≤ 1 the
exponential integral enters.

**Proposition 2.** S(a) < 0, and S > 0 on (0, ξ). Starting from hi = a and lo = a/2^k for the first k with S(lo) > 0,
bisection on the sign of S finds ξ to relative accuracy ε with ⌈log₂(1/ε)⌉ + k evaluations of S.

*Proof.* At x = a, that is η = μ/κ, the growth f is positive below and negative above, so K < 0 < G. By Theorem 1,
D has exactly one zero, and D > 0 before it. ∎

Some values of ξ and h (rows from `sim/data/xi_table.csv`):

| a = 2μ/σ² | β = 2M/σ² | ξ | h |
|---|---|---|---|
| 1.25 | 1 | 0.492788 | 0.082387 |
| 2 | 0.5 | 0.390607 | 0.638548 |
| 2 | 2 | 0.928659 | 0.281628 |
| 3 | 1 | 0.773581 | 1.175154 |
| 5 | 2 | 1.564222 | 2.207911 |
| 10 | 4 | 3.374603 | 5.130319 |

For the parameters of Figure 1 of [1] (μ = M = κ = σ² = 1), η* = 0.4643297 and the optimal yield is 0.1408139, within
the bounds (μ − σ²/2)²/(4κ) ≤ ρ* ≤ μ²/(4κ) of [1, Theorem 2.1]. For a small cap, h approaches α − 1, which is the
yield M(μ − M − σ²/2)/κ of harvesting at the constant rate M.

## Lean

`lean/HarvestThreshold/`, built against Mathlib, standard axioms only (`lean/axioms.txt`):

- `Crossing.lean`: a function on (0, ∞) whose derivative is negative at each zero has at most one zero
  (`zero_unique_of_deriv_neg`); the derivative of (P + λQ)/(A + λB) (`ratio_hasDerivAt`); uniqueness of its
  critical point from the derivative relations and the mean inequality (`critical_point_unique`).
- `Model.lean`: the model of [1] (`Params`, with μ > σ²/2, κ > 0, M > 0, σ² > 0), the yield exactly as in
  equation (4.4) of [1] with the density (4.3) and its normalizing constant (`yieldH`), Lemma 1
  (`yieldH_eq_mean`), the derivative of the yield (`yieldH_hasDerivAt`), and Theorem 1:
  - `yieldH_critical_point_unique`: two critical points of the yield (4.4) in (0, ∞) coincide, for all parameters;
  - `conjecture_4_1`: assuming `Theorem21`, there is exactly one x* > 0 with H′(x*) = 0, and it maximizes H.
- Content lemmas: `yieldH_deriv_neg_at_zero_of_growth` (H′ < 0 at η = μ/κ, so H is not flat) and `fig1_case`
  (the parameters of Figure 1 of [1] satisfy the hypotheses and lie in the case μ − M ≤ σ²/2).

**Assuming.** `Theorem21`: some threshold x̂ > 0 maximizes H over all thresholds. This follows from [1, Theorem 2.1],
which states that an optimal strategy among all admissible ones is a threshold strategy with x̂ ∈ (0, ∞), together
with two facts stated in [1]: every threshold strategy is an admissible stationary Markov strategy [1, Remark 2.3],
and its long-run yield is H(η) by ergodicity [1, Remark 2.2 and eq. (4.4)]. Lemma 4 gives the same statement directly.

**Not formalized:** Lemma 4 (existence of the maximizer from the limits at 0 and ∞), the monotonicity of H on each
side of η*, the optimality of the threshold strategy among all admissible strategies (from [1, Theorem 2.1] and
Theorem 1), the closed form and Proposition 2, and the extension to general growth and state-dependent caps.

## Scripts

- `sim/check.py`: the yield (4.4) as printed against the closed form and against the rescaled form of Section 1,
  Lemma 1, the sign rule of Lemma 2, and unimodality of H on 400 random parameter sets (212 with μ − M > σ²/2,
  188 with μ − M ≤ σ²/2), with 40-digit incomplete gamma functions.
- `sim/optimal_threshold.py`: the bisection of Proposition 2, checked against a grid search, and the table of ξ and h.
- `sim/simulate.py`: sample paths of the harvested population with an Euler step for log X, a step-size check, and
  Monte Carlo long-run yields against the exact H at seven thresholds; data for figures in `sim/data/`.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs,
to write the Lean files and the scripts, and to draft the text.

## References

1. A. Hening, D. H. Nguyen, S. C. Ungureanu, T. K. Wong. Asymptotic harvesting of populations in random environments.
   J. Math. Biol. 78 (2019) 293–329. arXiv:1710.01221.
2. E. Ekström, D. Mata, H. Saarinen. Resource extraction from a stochastic population with harvesting quotas.
   arXiv:2608.17778 (2026).
