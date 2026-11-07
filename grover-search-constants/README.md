# Grover search with an unknown number of solutions: certified constants

_7 November 2026_

Quantum search for one of t marked items among N, with t unknown, is the subroutine behind quantum minimum finding and Grover adaptive search for binary optimization (QUBO). The algorithm repeats rounds: k Grover iterations on the uniform state, a measurement, and a classical check of the measured item, which costs one oracle query. It stops at the first marked item. Its expected number of oracle queries is c·√(N/t), and c enters every resource estimate built on it. The constant proved for the standard schedule is 9/4 as t/N → 0 [1], and the best numerical value known to us is about 1.32 [3].

This folder gives a schedule with a random geometric offset and a certified constant of 1.1341 as t/N → 0, with the checks counted. The bound comes from an exact computation over all N and t, in double precision with safety margins.

## Results

| Quantity | Previous best bound | This folder |
|---|---|---|
| Search, unknown t, expected oracle queries divided by √(N/t), as t/N → 0 | 9/4, proved, Grover iterations only [1, Theorem 3]; about 1.32, numerical [3]; about 1.434, conjectured, for fixed-point search [4] | **≤ 1.1341**, checks included |
| The same, for every N and every t ≤ N/4 | 9.2/3 ≈ 3.07, proved, checks included [2, Eq. (10)] | **≤ 1.1676** (parameters S) |
| The same bound uniformly for every t ≤ N | | **≤ 1.6740** (parameters U) |
| Minimum finding of N distinct values, expected queries until the minimum is found, divided by √N, as N → ∞ | 5.3801, proved, leading term [2, Section 2.3]; about 2.46, numerical [3] | **≤ 2.0942** |
| The same, for every N | 6.3505√N + 2.8203, proved [2] | **≤ 2.293√N + 69** |

For t ≥ N/4, [2] proves an absolute bound of 2.0344 expected queries, which the bound of parameters U does not improve.

Among schedules that use a fixed number of iterations in each round, with ratios repeating with period at most 3 and a random offset, numerical optimization of the limit t/N → 0 gives 1.1315 at ratio 1.594 (`sim/cont2.py`). The certified schedule uses a narrow random window for the number of iterations, which costs 0.2 percent and makes the tail of the series provably geometric.

## The algorithm

Parameters λ = 1.59, α = 0.95, M = 64, a start value c, a minimum window h₀ and a number k₀ of initial classical samples.

1. Draw u uniformly from {0, ..., M − 1} and set U = (u + 1/2)/M.
2. Make k₀ classical samples: a uniformly random item, checked with one query.
3. For i = 0, 1, 2, ...: set m = c·λ^(i+U), a = ⌊αm⌋, h = max(h₀, ⌈m⌉ − a). Draw k uniformly from {a, ..., a + h − 1}, apply k Grover iterations to the uniform superposition, measure, and check the result. This costs k + 1 queries.
4. Stop at the first marked item.

Parameters S: c = 1, h₀ = 1, k₀ = 0. Parameters U: c = 0.2, h₀ = 2, k₀ = 2. Both have the same limit as t/N → 0.

For minimum finding, the threshold method of [5] calls this search repeatedly, each time with a fresh offset, for the items below the current threshold.

## The certificate

Write t/N = sin²θ. A round with k iterations succeeds with probability sin²((2k + 1)θ), so a round of the algorithm fails with probability

  q = 1/2 + (sin(4(a + h)θ) − sin(4aθ)) / (4h·sin 2θ),

and E(θ) = (1/M) Σ_u Σ_i w_i Π_{j<i} q_j with w_i = a_i + (h_i − 1)/2 + 1. The bound covers all θ ∈ (0, π/2] in four parts.

- **Small θ ≤ 10⁻⁸.** With y = mθ, the rounds of all M offsets form one geometric lattice with ratio λ^(1/M), and replacing θ by θλ^(1/M) only permutes the offsets. Up to explicit error terms of order 10⁻⁶, θE(θ) is then bounded by a function of y that is periodic in log y. Its supremum over one period is bounded with interval arithmetic on 4000 cells: 1.13406. Rounds with m < 60 enter only through their cost, and rounds with y ≥ 400 through a geometric series with ratio at most λ·(1/2 + 1/(4(1 − α)y)) < 1.
- **10⁻⁸ ≤ θ ≤ π/4**, and θ ≥ π/4 written in d = π/2 − θ, where q = 1/2 − (sin(4(a + h)d) − sin(4ad)) / (4h·sin 2d): interval bounds on 1.8·10⁵ geometric cells of relative width 10⁻⁴, and 6.7·10⁴ cells in d. Once every later round has q ≤ 0.58, the rest is bounded by a geometric series, since λ·0.58 < 1.
- **d ≤ 10⁻³** (parameters U): the two classical samples fail with probability sin²d ≤ d² each, and a crude bound on the rest gives E ≤ 1.0000033.

**Numerics.** All bounds are in double precision. Every interval end of a sine, and every failure probability, is widened by 10⁻¹². The final bounds are multiplied by 1 + 10⁻⁹. The computation is not in interval arithmetic with directed rounding.

**Minimum finding.** In the threshold method, the item of rank r becomes the threshold with probability 1/r, and then the search runs with t = r − 1. So the expected number of queries until the minimum is found is at most 1 + Σ_{t=1}^{N−1} E(N, t)/(t + 1). Dominated convergence with the uniform bound 1.6740 gives the limit 1.1341·Σ_{t≥1} 1/((t + 1)√t) = 1.1341·1.84658 = 2.0942. For every N, the bounds 1.2412 for t/N ≤ 10⁻⁴, 1.5675 for t/N ≤ 10⁻² and 1.6740 otherwise give 2.293√N + 69, using Σ_{t>T} 1/((t + 1)√t) ≤ 2/√T.

## Status and checks

Numerical certificate, for every N and t. No part is formalized in Lean.

- `sim/cert.py S` and `sim/cert.py U` compute the bounds in `data/cert_S.json` and `data/cert_U.json`, each in a few minutes.
- On cells of width zero, the cell bound agrees with the exact expectation at random θ to within the factor 1 + 10⁻⁹, and is never below it.
- `sim/sim.py` runs the algorithm with sampled outcomes, 20000 runs per case, and agrees with the exact expectation within the statistical error, for example 1.1376 ± 0.0049 against 1.1471 for N = 2²⁰, t = 1 with parameters U.

**Not covered:**
- lower bounds for this problem with explicit constants; the known-t optimum of restarting search is about 0.690 [1];
- a closed-form proof of the constant;
- minimum finding with repeated values;
- noise on the hardware.

## Files

- `sim/cert.py`: the certificate.
- `sim/sim.py`: Monte Carlo of the algorithm and its exact expectation.
- `sim/cont.py`, `sim/cont2.py`: the limit t/N → 0 and its optimization over schedules.
- `data/cert_S.json`, `data/cert_U.json`: the certified values.

## References

1. M. Boyer, G. Brassard, P. Høyer, A. Tapp. Tight bounds on quantum searching. Fortschritte der Physik 46, 493-505 (1998), arXiv:quant-ph/9605034.
2. C. Cade, M. Folkertsma, I. Niesen, J. Weggemans. Quantifying Grover speed-ups beyond asymptotic analysis. Quantum 7, 1133 (2023), arXiv:2203.04975.
3. W. P. Baritompa, D. W. Bulger, G. R. Wood. Grover's quantum algorithm applied to global optimization. SIAM Journal on Optimization 15(4), 1170-1184 (2005).
4. Á. Nagy, J. Park, C. Zhang, A. Acharya, A. Khan. Fixed-point Grover adaptive search for quadratic binary optimization problems. arXiv:2311.05592.
5. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014.
