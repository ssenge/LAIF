# Quantum mean estimation with bounded variance: certified worst-case constants

_12 November 2026_

A random variable y is given by its code: a circuit that prepares Σ_v √p(v) |v⟩ ⊗ |garbage_v⟩, and that can also be run backwards. Its variance is at most a known σ². The task is to output μ̂ with |μ̂ − E[y]| ≤ ε, with probability at least 1 − δ. Quantum algorithms do this with O((σ/ε) log(1/δ)) calls to the code [1], against Θ((σ/ε)² log(1/δ)) samples classically. To our knowledge, the constant in front of σ/ε is not stated in [1, 2, 3]. That constant decides from which σ/ε on the quantum algorithm needs fewer calls than classical sampling.

This folder gives an algorithm and certifies its worst-case number of calls for σ/ε from 10 to 1000 and δ ∈ {0.05, 0.01}. The certificate holds for every distribution with variance at most σ², every value of the mean and every sequence of measurement outcomes.

## Result

Worst-case number of calls to the code of y or its inverse, including the classical samples of the first step. In the table, "per σ/ε" is that number times ε/σ.

| σ/ε | δ = 0.05: calls | per σ/ε | δ = 0.01: calls | per σ/ε |
|---|---|---|---|---|
| 10 | 30 526 | 3053 | 39 357 | 3936 |
| 33.3 | 114 445 | 3433 | 148 260 | 4448 |
| 100 | 465 865 | 4659 | 605 616 | 6056 |
| 333.3 | 2 186 612 | 6560 | 2 799 278 | 8398 |
| 1000 | 7 374 212 | 7374 | 9 435 688 | 9436 |

Previous best bound: O((σ/ε) log(1/δ)) [1], with the constant not stated.

For comparison, every classical algorithm needs at least z²(σ/ε)² samples on Gaussian y, where z is the 1 − δ/2 quantile of the standard normal distribution: 3.84 (σ/ε)² for δ = 0.05 and 6.63 (σ/ε)² for δ = 0.01, since the sample mean is minimax for the Gaussian location family. At σ/ε = 1000 this is 3.84 · 10⁶ and 6.63 · 10⁶. So at σ/ε = 1000 the certified quantum count is 1.9 times the classical minimum for δ = 0.05, and 1.4 times for δ = 0.01. The ratio falls as σ/ε grows, because the quantum count grows like (σ/ε) times a slowly growing factor.

## The algorithm

Scale so that σ = 1. All amplitude estimation (AE) runs use the algorithm of [amplitude-estimation-constants](../amplitude-estimation-constants/), which ends with an interval [l, u] of width at most η that contains the angle θ, a = sin²θ, except with probability α. One AE run counts every call to its state preparation A or A†. Each such call uses the code of y once, plus a comparison and a controlled rotation.

1. **Centring.** Draw k·g classical samples, take the median m₀ of the k group means of g samples each. By the variance inequality P(|Y − μ| > r) ≤ Var Y / r², a group mean misses μ by more than r = 1/4 with probability at most p = 1/(g r²), so m₀ misses with probability at most P(Bin(k, p) ≥ (k + 1)/2) ≤ δ/10. The values (k, g) are the cheapest pair with this property, for example 7 × 136 = 952 samples for δ = 0.05. From now on x = y − m₀, and S = E[x²] ≤ 1 + r².
2. **Central band.** One AE run on W = (1 + x·1{|x| ≤ b}/b)/2, a variable in [0, 1] with E[W] = 1/2 + E[x·1{|x| ≤ b}]/(2b).
3. **Outer bands.** With t₁ = b and t_j = bρ^{j−1} for j = 2, ..., L, one AE run for each band (t_{j−1}, t_j] and each sign s = ±1, on Z = s·x·1{t_{j−1} < s·x ≤ t_j}/t_j in [0, 1].
4. **Output.** μ̂ = m₀ + 2b(â_W − 1/2) + Σ_{j,s} s·t_j·â_{j,s}, with â = (sin²l + sin²u)/2 for each run.

The parameters b, ρ, L and η come from a search that minimizes the certified cost under the error bound below. For example, at σ/ε = 1000 and δ = 0.05: b = 2, ρ = 32, L = 3, so there are five AE runs, each with η = 7.08 · 10⁻⁵ and α = 0.009.

## The certificate

**Error.** Suppose the centring and all AE runs succeed.

- **Central band.** The error in E[W] is at most sin(u + l)·sin(u − l)/2 ≤ η/2, so the error in E[x·1{|x| ≤ b}] is at most bη.
- **An outer band.** Let a = E[Z] = sin²θ. Then sin(u + l) ≤ sin 2θ + η ≤ 2√a + η, so the error in a is at most √a·η + η²/2. On the band, |x|/t_j ≤ x²/(t_{j−1} t_j). So with m_{j,s} the part of E[x²] that lies in the band, a ≤ m_{j,s}/(t_{j−1} t_j), and t_j √a ≤ √(ρ m_{j,s}).
- **Sum over the bands.** By the inequality Σ √(c_i m_i) ≤ √(Σ c_i · Σ m_i), summed over the 2(L − 1) outer runs, the error is at most √(2(L − 1)ρη²·M) + Σ_{j,s} t_j η²/2, where M is the part of E[x²] in the outer bands.
- **Tail.** The part with |x| > T = t_L contributes at most M_T/T, where M_T is the part of E[x²] there, and M + M_T ≤ S.
- **Total.** The bound is maximized over the split of S between M and M_T, in closed form. It is required to be at most ε.

**Failure.** The levels add up by the union bound: δ/10 + (2L − 1)·α ≤ δ.

**Calls.** The total is k·g plus (2L − 1) times the certified worst-case calls of one AE run at width η and level α. That certificate covers every amplitude and every sequence of outcomes, and is computed by `ae_bound.py` of [amplitude-estimation-constants](../amplitude-estimation-constants/), in double precision with safety margins and not in interval arithmetic.

## Status and checks

Numerical certificate for the listed σ/ε and δ. No part is formalized in Lean.

- `sim/certify.py` recomputes every row of the table (`data/certified.jsonl`). It checks that the error bound is at most ε and that the AE levels add up to at most α.
- `sim/me_sim.py` runs the whole algorithm with exactly sampled outcomes, at δ = 0.05, on four distributions with variance 1 and mean 3.7: a two-point distribution, a three-point distribution with mass just above b, a distribution with a far point at 3T, and a discretized Gaussian (`data/sim_sigma_eps_*.txt`):

  | σ/ε | Runs | Failures | Largest error | Largest calls per σ/ε | Mean calls per σ/ε | Certified |
  |---|---|---|---|---|---|---|
  | 10 | 4000 | 0 | 0.57 ε | 1139 | 737 to 970 | 3053 |
  | 100 | 2000 | 0 | 0.63 ε | 1842 | 1157 to 1439 | 4659 |
- **Not covered:**
  - σ/ε outside the table, and other δ. The scripts compute the bound for any σ/ε and δ, at a cost that grows with σ/ε;
  - a closed-form bound valid for all σ/ε;
  - lower bounds on the quantum constant;
  - noise on the hardware, and the cost of the arithmetic inside A.

## Files

- `sim/me_design.py`: the error bound, the centring and the parameter search.
- `sim/certify.py`: the certified totals. Usage `certify.py delta inv_eps...`.
- `sim/me_sim.py`: the algorithm with sampled outcomes. Usage `me_sim.py eps delta alpha_last runs [seed]`.
- `sim/ae/`: `ae_core.py` and `ae_bound.py`, unchanged copies from [amplitude-estimation-constants](../amplitude-estimation-constants/).
- `data/certified.jsonl`: the parameters and totals of the table.
- `data/sim_sigma_eps_10.txt`, `data/sim_sigma_eps_100.txt`: the simulation output.

## References

1. R. Kothari, R. O'Donnell. Mean estimation when you have the source code; or, quantum Monte Carlo methods. SODA 2023, arXiv:2208.07544.
2. A. Montanaro. Quantum speedup of Monte Carlo methods. Proceedings of the Royal Society A 471, 20150301 (2015), arXiv:1504.06987.
3. Y. Hamoudi. Quantum sub-Gaussian mean estimator. ESA 2021, arXiv:2108.12172.
