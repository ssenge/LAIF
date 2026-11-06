# Amplitude estimation without phase estimation: certified worst-case constants

_6 November 2026_

Amplitude estimation is the quantum subroutine behind quadratic speedups for Monte Carlo estimation, for example in option pricing and risk analysis. Given a circuit A with A|0⟩ = √a |good⟩ + √(1 − a) |bad⟩, the task is to output â with |â − a| ≤ ε with probability at least 1 − α. The cost is counted in applications of the Grover operator Q = A S₀ A† S_good. Versions without phase estimation [1, 2, 3] need O(1/ε) applications up to logarithmic factors and are the ones used on current hardware. Their cost in practice is set by the constant in front of 1/ε. The analytic constants proved for them are in the hundreds, and 77 to 88 at α = 0.05 with a numerical step, while the typical cost in simulations is below 10/ε.

This folder gives a version with exact Clopper-Pearson intervals and a worst-case number of Q applications certified by a computation in double precision with safety margins, for ε ∈ {10⁻², 10⁻³, 10⁻⁴} and α from 0.1 to 10⁻⁶. The certified values are 4.5 to 15 times below the previous best bounds.

## Results

Worst case over all amplitudes a and all measurement outcomes, as a multiple of 1/ε. "Previous best bound" is the smallest of the stated bounds of [1, Theorem 1 and Theorem 2], [2, Theorem 2] and [3] at the given ε and α.

**Applications of Q**

| α | Previous best bound, ε = 10⁻² | This folder | Previous best bound, ε = 10⁻³ | This folder | Previous best bound, ε = 10⁻⁴ | This folder |
|---|---|---|---|---|---|---|
| 0.1 | 213.8 [2] | **13.99** | 213.8 [2] | **15.84** | 213.8 [2] | **16.31** |
| 0.05 | 77.4 [1, Thm 2] | **16.51** | 83.3 [1, Thm 2] | **18.36** | 87.5 [1, Thm 2] | **18.76** |
| 0.01 | 342.0 [2] | **22.35** | 342.0 [2] | **25.07** | 342.0 [2] | **25.72** |
| 10⁻³ | 470.2 [2] | **31.90** | 470.2 [2] | **34.86** | 470.2 [2] | **35.79** |
| 10⁻⁴ | 587.2 [1, Thm 1] | **40.91** | 598.4 [2] | **45.16** | 598.4 [2] | **45.61** |
| 10⁻⁶ | 817.4 [1, Thm 1] | **58.71** | 838.6 [1, Thm 1] | **65.83** | 853.4 [1, Thm 1] | **67.34** |

The bound of [1, Theorem 2] holds for α = 0.05 only and uses a numerical step, as ours does. The others are analytic and hold for all ε.

**Calls to A or A†**, which [1, 2, 3] do not count separately: one shot at Q^k A uses 2k + 1 of them.

| α | ε = 10⁻² | ε = 10⁻³ | ε = 10⁻⁴ |
|---|---|---|---|
| 0.1 | 43.49 | 34.73 | 33.10 |
| 0.05 | 50.66 | 40.37 | 38.03 |
| 0.01 | 69.81 | 54.30 | 52.06 |
| 10⁻³ | 93.96 | 75.35 | 72.34 |
| 10⁻⁴ | 119.99 | 97.38 | 92.12 |
| 10⁻⁶ | 173.32 | 141.43 | 135.91 |

## The algorithm

Write a = sin²θ with θ ∈ [0, π/2]. One shot of Q^k A, measured, gives "good" with probability sin²(Kθ), K = 2k + 1. The algorithm keeps an interval [l, u] that contains θ with high probability, starting from [0, π/2], with width w = u − l.

1. **Choice of K.** K is the largest odd number at most max(1, ⌊π/(2w)⌋) such that K·[l, u] lies in one branch [jπ/2, (j + 1)π/2]. On such a branch, p = sin²(Kθ) is monotone in θ.
2. **Choice of the level and the number of shots.** The width w lies in a cell (g_c, g_{c+1}] of the geometric grid g_c = arcsin(2ε)·1.02^c. The stage uses the level α_c = α_last·(arcsin(2ε)/g_{c+1}), rounded down to a power of 1.1. The number of shots N is the smallest N on the grid {round(1.08^i)} for which every Clopper-Pearson interval at level α_c, over all outcomes h = 0..N, has width at most K·max(g_c/2, 0.999·arcsin(2ε)) in the angle Kθ.
3. **Update.** N shots give h successes. The exact Clopper-Pearson interval for p at level α_c is mapped back through the branch to an interval for θ, which is intersected with [l, u]. If the intersection is empty, the mapped interval is kept.
4. **Stop** when w ≤ arcsin(2ε), and output â = (sin²l + sin²u)/2.

The single parameter α_last is the largest value for which the bound below on the sum of the levels is at most α.

## The certificate

**Correctness.** The Clopper-Pearson interval covers p with probability at least 1 − α_c for every p, and N, K and α_c depend only on earlier outcomes. So the probability that some stage misses is at most the expected sum of the levels used, which is at most the largest sum along any run. If no stage misses, θ stays in [l, u]. At the end, sin²u − sin²l = sin(u + l)·sin(u − l) ≤ sin w ≤ 2ε, so |â − a| ≤ ε.

**Cost.** Every stage, missed or not, ends with a width at most min(w, W/K), where W is the largest Clopper-Pearson width in the angle over all outcomes. The choice of N gives W/K ≤ max(g_c/2, 0.999·arcsin(2ε)) < g_c, so every stage moves to a lower cell. A width in the cell c lets the algorithm choose K only between kg(g_{c+1}) and ⌊π/(2g_c)⌋. Here kg(v) is the smallest, over all positions of an interval of width v in [0, π/2], of the largest admissible K that fits. It is computed exactly by a sweep over the positions. A recursion over the cells, from small widths to large ones, takes the maximum over all admissible K of the cost of the stage plus the bound for the cell of the next width. With running maxima over the cells, it bounds the number of Q applications, the number of calls to A, and the sum of the levels, for every amplitude and every sequence of outcomes.

**Numerics.** The Clopper-Pearson endpoints come from the inverse regularized incomplete beta function in double precision, the upper one through its complement so that it stays accurate at small levels, and are widened by 10⁻¹² before use. In spot checks against exact binomial tails, the levels this gives agree with the nominal ones to a relative 10⁻¹⁴. The widths in kg are inflated by a factor 1 + 10⁻⁹. The computation is not in interval arithmetic.

## Status and checks

Numerical certificate for the listed ε and α. No part is formalized in Lean.

- `sim/ae_core.py` checks kg against the largest fitting K at random interval positions, and the vectorized intervals against the scalar ones.
- `sim/ae_alg.py` runs the algorithm with exactly sampled outcomes, half of the amplitudes uniform and half near a = 1/4:

  | ε, α | Runs | Failure rate | Largest Q count | Mean Q count |
  |---|---|---|---|---|
  | 10⁻², 0.05 | 20000 | 0.0011 | 12.28/ε | 6.12/ε |
  | 10⁻³, 0.05 | 10000 | 0.0011 | 11.56/ε | 6.39/ε |

- **Not covered:**
  - values of ε other than the listed ones. The scripts compute the bound for any ε; the cost of kg grows with 1/ε;
  - a closed-form bound valid for all ε;
  - lower bounds on the constant for this class of algorithms;
  - noise on the hardware.

## Files

- `sim/ae_core.py`: Clopper-Pearson intervals and kg.
- `sim/ae_bound.py`: the recursion over the cells. Usage `ae_bound.py eps alpha 2 1 1`.
- `sim/ae_table.py`: all α for one ε, as JSON lines.
- `sim/ae_alg.py`: the algorithm itself, with the simulation check.
- `data/ae_table.jsonl`: the certified values in the tables above.

## References

1. D. Grinko, J. Gacon, C. Zoufal, S. Woerner. Iterative quantum amplitude estimation. npj Quantum Information 7, 52 (2021), arXiv:1912.05559.
2. A. Roux, T. Zastawniak. Accelerated quantum amplitude estimation without QFT. arXiv:2407.16795 (2024).
3. S. Fukuzawa, C. Ho, S. Irani, J. Zion. Modified iterative quantum amplitude estimation is asymptotically optimal. ALENEX 2023, 135-147, arXiv:2208.14612.
