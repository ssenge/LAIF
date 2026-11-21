# A classical seed for memetic tabu search on LABS

_21 November 2026_

The low-autocorrelation binary sequence (LABS) problem asks for a sequence s ∈ {±1}ᴺ that minimizes E(s) = Σₖ (Σᵢ sᵢ sᵢ₊ₖ)². In [1], memetic tabu search (MTS) with a population of K = 100 is started from the lowest of 10⁵ shots of a digitized counterdiabatic quantum circuit, copied K times (QE-MTS). Over N = 27 to 37, the median time to solution then grows as 1.24ᴺ (95% CI [1.23, 1.25]), against 1.37ᴺ ([1.36, 1.37]) for MTS from a random population [1, Table I], and the fits project a crossover at N ≳ 47.

Here the same MTS is started from the lowest of 10⁵ uniformly random sequences, copied K times. No quantum circuit is involved.

## Result

Fitted base κ of the median time to solution, log Q = α + N log κ over N = 27 to 37, with the statistic and the two-stage bootstrap of [1] (median over seeds per replicate, quantile Q over replicates, B = 5000):

| Initial population | Q0.50 | Q0.90 | R² (Q0.50) | Values of [1] |
|---|---|---|---|---|
| Random (MTS) | **1.375** [1.365, 1.392] | 1.386 [1.373, 1.414] | 0.77 | MTS: 1.37 [1.36, 1.37], Q0.90 [1.37, 1.39] |
| Best of 10⁵ random sequences | **1.274** [1.251, 1.290] | not exact | 0.73 | QE-MTS: 1.24 [1.23, 1.25] |

MTS from a random population reproduces the base of [1]. The classical seed lowers the fitted base from 1.375 to 1.274, about 73% of the way to the QE-MTS value on the log scale.

The seeded runs are slower than MTS from a random population at every N in the range. Median of medians, in children (offspring generated) per run:

| N | 27 | 28 | 29 | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| Random | 507 | 170 | 287 | 241 | 227 | 744 | 1641 | 1985 | 3820 | 3454 | 3092 |
| Best of 10⁵ random | 883 | 386 | 682 | 522 | 381 | 968 | 1836 | 2238 | 4683 | 4289 | 3442 |
| Ratio | 1.74 | 2.28 | 2.38 | 2.17 | 1.68 | 1.30 | 1.12 | 1.13 | 1.23 | 1.24 | 1.11 |

The smaller base comes from a gap that shrinks with N, not from fewer evaluations at any N. The two fit lines cross at N ≈ 37.5. This hints at a possible gap in reading the base of [1] as a quantum effect: a lower fitted base alone need not show a quantum contribution, since a seed with no quantum input lowers it by most of the same amount. [1] notes that other classical heuristics may also serve as seed sources; the best of random sequences is the simplest one at the same sample count.

## Counting unit

[1] measures the time to solution as the number of objective evaluations until the known optimum first appears. The table above counts children. The same runs in two other units:

| Unit | Random | Best of 10⁵ random | Best of 10⁵ random, seed cost included |
|---|---|---|---|
| Children | 1.375 | 1.274 | |
| Tabu steps | 1.420 | 1.316 | |
| One-flip neighbour evaluations | 1.465 | 1.358 | 1.326 |

The per-child count is the one that reproduces the MTS base of [1]. The difference between the two populations is about 0.10 in every unit.

## Scope

- **Runs.** 50 replicates (initial populations) × 50 MTS seeds per N and population, against 100 × 100 in [1]. Sequence lengths 27 to 37, optima E(s) from the literature, the optima for N ≤ 20 checked by exhaustive search.
- **MTS.** As in [1, Algorithms 1 to 3]: K = 100, p_comb = 0.9, p_mut = 1/N, tournament size 2, tabu budget M uniform in [N/2, 3N/2), tenure M/10 plus a uniform integer in [0, M/50], aspiration on a new best, a child replaces a uniformly random member. Single thread, stopped when the known optimum first appears.
- **Caps at N = 36 and 37.** There each run is stopped at 34 514 (N = 36) or 33 225 (N = 37) children, four times the larger median extrapolated from N − 5 to N − 1. A stopped run counts as above the cap. Every median lies below the cap, so the medians are exact; 18% to 28% of the runs at these N are capped. The Q0.90 of the seeded population is not exact (62.5% of the bootstrap draws reach the cap) and is not reported.
- **Fit quality.** The per-N medians are not monotone in N, and R² of the Q0.50 fits is 0.73 to 0.83 across units and populations.
- **Not run.** The quantum seed of [1] itself.

## Files

- `sim/mts.py`: LABS energy, memetic tabu search and the two initial populations (also a simulated-annealing seed).
- `sim/test_mts.py`: the one-flip energy update against recomputation, and the optima for N = 10 to 20 by exhaustive search.
- `sim/run_arms.py`: uncapped runs, N = 27 to 35; `sim/run_adaptive.py`: the capped runs at N = 36 and 37 (`python -I run_adaptive.py test` checks the capped median and the cap flag).
- `sim/analyze.py`: the fits and the bootstrap (`python -I analyze.py ../data/runs.jsonl.gz 5000 children`; `python -I analyze.py test` checks the fit on exact exponential data).
- `sim/per_n.py`: the per-N table and the crossing of the fit lines (`python -I per_n.py ../data/runs.jsonl.gz`).
- `data/runs.jsonl.gz`: one line per run: N, population, replicate, seed, evaluations, tabu steps, children, seed cost and, at N = 36 and 37, the cap flag.

## References

1. A. Gomez Cadavid, P. Chandarana, S. V. Romero, J. Trautmann, E. Solano, T. L. Patti, N. N. Hegade. Scaling advantage with quantum-enhanced memetic tabu search for LABS. arXiv:2511.04553.
