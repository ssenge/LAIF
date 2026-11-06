# Binary paint shop and Max-Cut on 4-regular graphs

_6 November 2026_

In the binary paint shop problem, a sequence of 2n cars contains each of n car models twice. The two cars of a model get different colours, and the goal is to minimize the number of colour changes along the sequence. It comes from automotive paint shops. The usual figure of merit is the expected number of colour changes per car model, the paint swap ratio of [1], on a uniformly random sequence as n → ∞.

## Results

| Quantity | Previous best bound | This folder |
|---|---|---|
| Binary paint shop, random sequences, expected colour changes per car model as n → ∞ | 0.334, QAOA at depth 17, exact [1]; 0.4 proved for recursive greedy [6], and below 0.4 proved as quoted in [1] | **≤ 0.3120** (Monte Carlo, confidence 1 − 10⁻⁴), classical local algorithm, O(n) time |
| Max-Cut on 4-regular graphs of large girth, expected cut fraction of a local algorithm | above 5/6 ≈ 0.8333 by an unquantified margin, proved [4] | **≥ 0.8440** (Monte Carlo, confidence 1 − 10⁻⁴), radius 163, girth ≥ 328 |

Both values are Monte Carlo bounds on the tree value. The confidence 1 − 10⁻⁴ refers to our random samples (details below). The rounding alone gives 5/6 in the limit of large m; the gain comes from the three flip rounds. For random 4-regular graphs, a maximum bisection of at least 5/6 of the edges is known with high probability [5]. Since local algorithms concentrate on random regular graphs [4], our value also gives, with high probability as the number of vertices N → ∞, a cut of at least 0.8440 − o(1) of the edges of a random 4-regular graph. This is an asymptotic statement: at radius 163, the neighbourhoods are trees only for astronomically large N.

For comparison: numerical simulations of a mean-field algorithm in [1] give about 0.280 colour changes per model on sequences of up to 10⁴ models. That algorithm is not local, and its value is a finite-size estimate. The optimum is predicted at about 0.263 [7, 8].

## From paint shop sequences to Max-Cut on the 4-regular tree

Let x_c ∈ {0, 1} be the colour of the first car of model c, and o_i ∈ {0, 1} say whether position i holds the first or the second car of its model. Neighbouring positions i, i + 1 with models a ≠ b give a colour change exactly when x_a ⊕ o_i ≠ x_b ⊕ o_{i+1}. So the colour changes are the unsatisfied edges of a signed graph G on the models, with one edge per neighbouring pair and sign o_i ⊕ o_{i+1}. Neighbouring cars of the same model always cost one change; on a random sequence there are O(1) of them.

Each model has two positions, and each position has two neighbours, so G has degree at most 4, with degree 3 only at the two ends. On a uniformly random sequence, the radius-R neighbourhood of a model in G is the 4-regular tree of radius R with probability 1 − O(9^R/n), by the usual exploration argument. On a tree, flipping x_c for a suitable set of models turns every edge into one that wants different colours, which is Max-Cut. Consider a local algorithm that commutes with flipping a variable together with the signs of its edges. Its expected number of colour changes per edge of G then tends to 1 − c, where c is its expected cut fraction for Max-Cut on the 4-regular tree. G has 2n − 1 edges, so

  expected colour changes per model → 2 (1 − c).

As a check: QAOA at depth 7 gives 0.393 for the paint shop [2] and 0.803 for Max-Cut on the 4-regular tree [3, Table 3], and 2(1 − 0.803) = 0.394. [1] uses the same conversion for QAOA.

## The algorithm

On G, with signs s = +1 for edges that want different colours and s = −1 for edges that want equal ones:

1. **Gaussian field.** Draw g_c independent standard normal. Set D = Σ_{l<m} α_l B_l g, where B_l counts non-backtracking walks of length l with the product of their signs (B_1 = A_s, B_2 = A_s² − 4I, B_l = A_s B_{l−1} − 3 B_{l−2}), and α are the coefficients of [3, eq. 21] for d = 4.
2. **Rounding.** y_c = sign(D_c − (τ/2) Σ_w s_cw D_w). For k = 2 this is Algorithm 1 of [3] with parameter m.
3. **Three flip rounds.** In each round, every model whose two cars cause at least 3 of its 4 neighbouring colour changes swaps its two colours, all at once.

We use m = 160 and τ = 1. The radius is m + 3 = 163, and the running time is O(mn). The rounding and the flip rounds commute with flipping a variable together with the signs of its edges. The Gaussian field does so in distribution, as g_c is symmetric.

## Status and checks

Numerical results. No part is formalized in Lean.

- **Value on the tree:** Monte Carlo over the joint Gaussian scores of the vertices within distance 4 of an edge, with the exact tree covariances of [3]. 10⁶ fresh samples, seed 2026, independent of the runs used to choose m, τ and the rounds, give a cut fraction of 0.84566 ± 0.00036. The empirical Bernstein bound [9] at confidence 1 − 10⁻⁴, for 0/1 samples, gives c ≥ 0.8440, so at most 0.3120 colour changes per model.
- **Real sequences:** `sim/bpsp_check.py` runs the algorithm on random sequences of 10⁶ models and counts the colour changes directly:

  | m, rounds | Tree value, 2(1 − c) | One sequence of 10⁶ models |
  |---|---|---|
  | 6, none | 0.4067 ± 0.0025 | 0.4052 |
  | 6, one | 0.3717 ± 0.0025 | 0.3732 |
  | 6, two | 0.3701 ± 0.0025 | 0.3710 |
  | 80, three | 0.307 ± 0.002 | 0.3099 |
  | 160, three | 0.3087 ± 0.0007 | 0.3097 |

- **Cross-checks:** the covariances converge to the limit −√3/2 as m grows; with no flip rounds the program returns the Local Vector values of [3].
- **Not covered:**
  - the rate of convergence in n: at m = 160 the neighbourhoods of a sequence of 10⁶ models are far from trees, although the measured value agrees;
  - sequences that are not uniformly random, such as real production orders;
  - worst-case sequences, for which the problem is APX-hard;
  - plain Max-Cut on finite random 4-regular graphs, where all edges want different colours: there the eigenvector of the eigenvalue 4 dominates the field from about m = 18 at 10⁶ vertices, and the algorithm as written fails. Paint shop sequences have mixed signs and are not affected;
  - in `sim/bpsp_check.py`, a pair of models that are neighbours twice gets one merged edge, which affects O(1) models.

## Files

- `sim/lv_baseline.py`: the coefficients α and the tree covariances of [3].
- `sim/lv_rounds.py`: the Monte Carlo on the tree; `python lv_rounds.py 4 160 1.0 3,3,3 1e6 2026` gives the certified row.
- `sim/bpsp_check.py`: the algorithm on random paint shop sequences.
- `data/certified.json`: the certified run.

Requirements: Python 3 with numpy and scipy.

## References

1. M. Goh, L. C. Pereira dos Santos, T. Müller, M. Sperl. Beyond Quantum Advantage: Improved Classical Algorithms for the Binary Paint Shop Problem. arXiv:2604.00607, 2026.
2. M. Streif, S. Yarkoni, A. Skolik, F. Neukart, M. Leib. Beating classical heuristics for the binary paint shop problem with the quantum approximate optimization algorithm. Phys. Rev. A 104, 012403, 2021, arXiv:2011.03403.
3. A. Apte, A. Khan, E. Farhi, K. Marwaha, S. Boulebnane, R. Shaydulin. Provable Classical and Quantum Local Algorithms for Max-k-Cut and Quantum Advantage at Moderate Girth. arXiv:2609.39042, 2026.
4. R. Lyons. Factors of IID on trees. Combin. Probab. Comput. 26, 2017, arXiv:1401.4197.
5. J. Díaz, N. Do, M. J. Serna, N. C. Wormald. Bounds on the max and min bisection of random cubic and random 4-regular graphs. Theoret. Comput. Sci. 307, 2003.
6. S. D. Andres, W. Hochstättler. Some heuristics for the binary paint shop problem and their expected number of colour changes. J. Discrete Algorithms 9, 2011.
7. L. Zdeborová, S. Boettcher. A conjecture on the maximum cut and bisection width in random regular graphs. J. Stat. Mech. 2010, arXiv:0912.4861.
8. A. Coja-Oghlan, P. Loick, B. F. Mezei, G. B. Sorkin. The Ising antiferromagnet and max cut on random regular graphs. SIAM J. Discrete Math. 36, 2022, arXiv:2009.10483.
9. A. Maurer, M. Pontil. Empirical Bernstein Bounds and Sample Variance Penalization. COLT 2009, arXiv:0907.3740.
