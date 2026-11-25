# Which cull raises tree regeneration: an exact criterion for stage-structured herbivores

Written 25 Nov 2026.

**Setting.** A herbivore (deer) has life stages 1, ..., n, with stage 1 the newborns. Every stage may browse tree
saplings S, with per-capita browsing weights β_j. Reproduction is regulated by one or more resources Z_1, ..., Z_r
(for example summer forage) that the population depletes, Z_ℓ = g_ℓ(α_ℓ·x) with weights α_ℓ. Saplings at equilibrium
decrease with the browsing pressure β·x. A cull, or a predator, adds mortality to one stage.

It is known that higher mortality can raise the biomass of a single stage when the stages are limited by different
resources [1, 2]. Here this becomes an exact condition for the sign of the effect on the browsed saplings.

## Results

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Sign of the effect of a cull on stage j on the browsed saplings | Qualitative: overcompensation of stage biomass needs different limiting resources for different stages [1, 2] | A small extra mortality on a cut stage j lowers the saplings if and only if U^β_j − Σ_ℓ w_ℓ U^{α_ℓ}_j > 1/E. A cull of newborns never lowers them. When the saplings are the only regulating resource, no cull lowers them | Claim. Numerical: the criterion matches the computed sign in all tested cases |
| Obs. 1 | Effect of environmental noise on the sign | | In an annual two-stage model, a 2 % adult cull raises the long-run mean of the saplings in a constant environment, and lowers it when summer forage varies from year to year with σ = 0.3. The equilibrium is stable at σ = 0 | Numerical |

## Statement

Write v for the expected time per newborn spent in each stage at equilibrium. Stage j is a cut: every path from
stage 1 to a fecund stage passes through j, and the stages after j are entered only through j.
- U^β_j is the share of the browsing β·v done by the stages before j, and U^{α_ℓ}_j is the same share for α_ℓ.
- ε_ℓ is the elasticity of the fecundity in Z_ℓ, and η_ℓ < 0 is the elasticity of Z_ℓ in α_ℓ·x.
- E = −Σ ε_ℓ η_ℓ, and w_ℓ = ε_ℓ η_ℓ / Σ_m ε_m η_m.

**Theorem 1 (Claim).** Suppose the equilibrium is regular: the scalar equilibrium equation in S crosses transversally.
Then a small extra mortality on stage j lowers the saplings if and only if

U^β_j − Σ_ℓ w_ℓ U^{α_ℓ}_j > 1/E.

*Proof sketch.* Extra mortality on stage j multiplies the residence times after j by a factor λ < 1 and leaves
those before j unchanged. At fixed S, the condition R_0 = λ F(Z) = 1 and the regulator equations
d log Z_ℓ = η_ℓ (d log B + (1 − U^{α_ℓ}_j) d log λ) give d log B / d log λ = 1/E − (1 − Σ w_ℓ U^{α_ℓ}_j). Here B is
the birth rate, so d log(β·x) / d log λ = 1/E + Σ w_ℓ U^{α_ℓ}_j − U^β_j. The browsing pressure rises with the cull
exactly when this is negative. A transversal crossing keeps the sign through the feedback of S on the stage
rates. ∎

**Special cases.**
- Culling newborns: U = 0, so the saplings never fall.
- Saplings as the only regulator (α ∝ β): U^β = U^α, so the saplings never fall.
- One logistic forage G with fecundity linear in G: 1/E = G*/(K_G − G*). Reversal needs a heavily depleted forage
  and a cull that separates the browsing stages (before it) from the forage-depleting stages (after it).

## Scope

- Theorem 1 is a first-order (small cull) statement at a regular equilibrium. For a predator with a linear numerical
  response, the prey stage densities are pinned instead of the mortality rate, and the same sign holds near the
  invasion threshold of the predator.
- In the checks, the criterion holds at stable equilibria. At unstable equilibria the regularity condition can fail.
- Observation 1 is numerical, for one model and one parameter set: the sign changes smoothly between σ = 0.1 and
  σ = 0.2.

## Scripts

- `sim/stage_cascade.py`: one regulating resource. Calf, adult and mixed predation always raise the saplings.
- `sim/two_resource.py`: summer forage regulates reproduction. Adult predation can lower the saplings, calf
  predation never does.
- `sim/nstage_cull.py`, `sim/criterion.py`: n = 2 to 5 stages, one regulator. `criterion.py` asserts that
  Theorem 1 gives the computed sign.
- `sim/criterion2.py`: two regulators, stable equilibria, with the same assertion.
- `sim/noise_sign.py`, `sim/noise_flip.py`: the annual model with weather noise. `noise_flip.py` asserts the sign
  change.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check
proofs, to write the scripts, and to draft the text.

## References

1. A. M. de Roos, T. Schellekens, T. van Kooten, K. van de Wolfshaar, D. Claessen, L. Persson. Food-dependent
   growth leads to overcompensation in stage-specific biomass when mortality increases: the influence of maturation
   versus reproduction regulation. Am. Nat. 170 (2007).
2. A. M. de Roos, L. Persson. Population and Community Ecology of Ontogenetic Development. Princeton University
   Press, 2013.
