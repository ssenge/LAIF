# Closed-form credit valuation adjustment of a quantum benchmark instance

_18 November 2026_

In [1], a quantum algorithm with Bayesian amplitude estimation computes the credit valuation adjustment (CVA) of a single European call, and a fault-tolerant runtime estimate places its break-even with classical Monte Carlo at a relative error of 0.0067%. The instance [1, Table I] is a call on geometric Brownian motion with S₀ = 5, strike K = 5.5, volatility σ = 0.25, drift μ = 0.02, maturity T = 184/360, recovery 0.415, and M = 4 exposure dates tᵢ = iT/M:

CVA = (1 − R) Σᵢ p(tᵢ) q(tᵢ) E(tᵢ),  E(t) = E[max(S_t − K e^{−r(T − t)}, 0)],

with discount factors p and default probabilities q from an interest-rate curve and a hazard curve bootstrapped from CDS quotes. The classical reference of [1] is Monte Carlo with 10⁵ paths, CVA = (5.599 ± 0.002) · 10⁻⁵.

## Result

The expected exposures of the instance in [1] have a closed form. With F = S₀ e^{μt}, K′ = K e^{−r(T − t)} and s = σ√t,

E(t) = F Φ(d₁) − K′ Φ(d₁ − s),  d₁ = (ln(F/K′) + s²/2)/s,

so the CVA is a sum of M = 4 such terms, exact to machine precision at the cost of four normal distribution evaluations, for any accuracy target. The discretized quantity estimated by the quantum circuit in [1, Eq. 6] is likewise a finite sum over the 2^{n+m} grid points of price and time, at most 2¹⁶ in the experiments there.

With a flat rate r = −0.45% and a flat hazard rate from the one-year CDS quote, λ = s₁/(1 − R_CDS) = 0.001596, the closed form gives CVA = 5.536 · 10⁻⁵. Monte Carlo with 4 · 10⁶ paths per date agrees to a relative 5 · 10⁻⁴. The value of [1] is 1.1% higher; the CVA is proportional to the default probabilities in this range, and a change of ±10% in λ moves it by ±10%.

## Scope

- The rate curve and the bootstrapped hazard rates of [1] are not tabulated there, so the flat values above stand in for them. They enter only through p and q, never through E(t).
- The statement concerns the instance of [1]. Netting sets with path-dependent trades or many risk factors have no closed form, and there Monte Carlo or quasi-Monte Carlo is the classical baseline.

## Files

- `sim/cva_closed_form.py`: the closed form, a Monte Carlo check with asserts, and the sensitivity to r and λ (`data/cva_closed_form.txt`).

## References

1. J. Alcazar, A. Cadarso, A. Katabarwa, M. Mauri, B. Peropadre, G. Wang, Y. Cao. Quantum algorithm for credit valuation adjustments. arXiv:2105.12087.
