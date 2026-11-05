# Local algorithms for Max-k-Cut on regular graphs of large girth

_6 November 2026_

Max-k-Cut asks for a colouring of the vertices with k colours that leaves as many edges as possible with two different colours. We study local algorithms on d-regular graphs whose girth is large compared with the radius of the algorithm. There the expected cut fraction is the same on every such graph and can be evaluated on the d-regular tree. Reference [1] computes this value for QAOA with the Grover mixer and for a classical Local Vector algorithm (its Algorithm 1). We compare against its Tables 4 and 5 at the same girth.

Both algorithms below add one classical round to a known local algorithm. In that round every vertex sees its own colour and the colour counts of its neighbours, and may change its colour. The round adds one to the radius, so a base algorithm valid at girth 2m is compared at girth 2m + 2.

## Results

### 1. Classical: Local Vector algorithm plus one round

Run Algorithm 1 of [1] with parameter m (radius m, girth ≥ 2m). Then apply one round of a rule that maps (own colour, colour counts of the neighbours) to a new colour, the same rule at every vertex. At girth 2m + 2, [1] reports QAOA at depth m and the Local Vector algorithm with parameter m + 1.

"Lower bound" is the empirical Bernstein bound [4] at confidence 1 − 10⁻⁴ per row. It is computed from 10⁶ fresh samples of the edge neighbourhood, independent of the samples used to choose τ and the rule. Bold marks a lower bound above the previous best bound.

| k | d | girth | Previous best bound [1] | Lower bound | Mean ± s.e. |
|---|---|---|---|---|---|
| 3 | 4 | 12 | 0.954 (Local Vector) | **0.9678** | 0.9686 ± 0.0002 |
| 3 | 4 | 14 | 0.961 (QAOA) | **0.9711** | 0.9719 ± 0.0002 |
| 3 | 4 | 16 | 0.968 (QAOA) | **0.9734** | 0.9741 ± 0.0002 |
| 3 | 4 | 18 | 0.973 (QAOA) | **0.9750** | 0.9757 ± 0.0002 |
| 3 | 6 | 12 | 0.915 (Local Vector) | **0.9277** | 0.9289 ± 0.0003 |
| 3 | 6 | 14 | 0.918 (Local Vector) | **0.9321** | 0.9332 ± 0.0003 |
| 3 | 6 | 16 | 0.924 (QAOA) | **0.9351** | 0.9362 ± 0.0002 |
| 3 | 6 | 18 | 0.930 (QAOA) | **0.9374** | 0.9384 ± 0.0002 |
| 3 | 6 | 20 | 0.934 (QAOA) | **0.9390** | 0.9401 ± 0.0002 |
| 3 | 6 | 22 | 0.938 (QAOA) | **0.9401** | 0.9412 ± 0.0002 |
| 3 | 8 | 14 | 0.890 (Local Vector) | **0.9029** | 0.9042 ± 0.0003 |
| 3 | 8 | 16 | 0.894 (QAOA) | **0.9058** | 0.9071 ± 0.0003 |
| 3 | 8 | 18 | 0.899 (QAOA) | **0.9080** | 0.9093 ± 0.0003 |
| 3 | 8 | 20 | 0.904 (QAOA) | **0.9095** | 0.9108 ± 0.0003 |
| 3 | 8 | 22 | 0.908 (QAOA) | **0.9106** | 0.9119 ± 0.0003 |
| 4 | 4 | 10 | 0.989 (Local Vector) | **0.9964** | 0.9966 ± 0.0001 |
| 4 | 4 | 12 | 0.993 (QAOA) | **0.9972** | 0.9974 ± 0.0001 |
| 4 | 4 | 14 | 0.996 (QAOA) | **0.9976** | 0.9979 ± 0.00005 |
| 4 | 8 | 12 | 0.952 (Local Vector) | **0.9641** | 0.9650 ± 0.0002 |
| 4 | 8 | 14 | 0.956 (QAOA) | **0.9675** | 0.9683 ± 0.0002 |
| 4 | 8 | 16 | 0.961 (QAOA) | **0.9684** | 0.9692 ± 0.0002 |
| 4 | 8 | 18 | 0.966 (QAOA) | **0.9710** | 0.9718 ± 0.0002 |

For larger degree the full rule space is too big to search, so we restrict to a threshold rule: move to a least-used colour (ties at random) if it is used by at least t fewer neighbours than the own colour. For Max-3-Cut on 20-regular graphs, with m = 10, τ = 3 and t = 2:

| k | d | girth | Previous best bound [1] | Lower bound | Mean ± s.e. |
|---|---|---|---|---|---|
| 3 | 20 | 22 | 0.825 (QAOA, depth 10) | **0.8282** | 0.8304 ± 0.0005 |

This lower bound uses 6 · 10⁵ fresh samples, again independent of the samples used to choose τ and t.

So for Max-3-Cut on 6- and 8-regular graphs and Max-4-Cut on 8-regular graphs, this classical algorithm is above every value of [1, Tables 4, 5] at each girth in the table, which includes QAOA up to depth 10. On 4-regular graphs the same holds up to girth 18 for k = 3 and up to girth 14 for k = 4.

### 2. Quantum: QAOA plus one round

Run QAOA with the Grover mixer at depth q (radius q, girth ≥ 2q + 2), measure every vertex, then apply one round of a rule as above. The radius is q + 1, so the comparison is with QAOA at depth q + 1, at girth 2q + 4. The angles are optimized for the value after the round. The values are exact tree contractions at the stated parameters.

| k | d | girth | QAOA [1], depth (girth − 2)/2 | QAOA at depth (girth − 4)/2 plus one round |
|---|---|---|---|---|
| 3 | 4 | 6 | 0.891 | **0.9057** |
| 3 | 4 | 8 | 0.921 | **0.9303** |
| 3 | 4 | 10 | 0.940 | **0.9478** |
| 3 | 4 | 12 | 0.952 | **0.9593** |
| 3 | 4 | 14 | 0.961 | **0.9671** |
| 3 | 6 | 6 | 0.851 | **0.8635** |
| 3 | 6 | 8 | 0.878 | **0.8864** |
| 3 | 6 | 10 | 0.895 | **0.9041** |
| 3 | 6 | 12 | 0.907 | **0.9164** |
| 3 | 6 | 14 | 0.917 | **0.9250** |
| 3 | 8 | 6 | 0.827 | **0.8400** |
| 3 | 8 | 8 | 0.851 | **0.8618** |
| 3 | 8 | 10 | 0.867 | **0.8741** |
| 3 | 8 | 12 | 0.878 | **0.8874** |
| 3 | 8 | 14 | 0.887 | **0.8951** |
| 4 | 4 | 6 | 0.953 | **0.9614** |
| 4 | 4 | 8 | 0.977 | **0.9850** |
| 4 | 4 | 10 | 0.988 | **0.9928** |
| 4 | 4 | 12 | 0.993 | **0.9958** |
| 4 | 8 | 6 | 0.903 | **0.9179** |
| 4 | 8 | 8 | 0.925 | **0.9366** |
| 4 | 8 | 10 | 0.939 | **0.9487** |
| 4 | 8 | 12 | 0.949 | **0.9568** |

In every case computed, one measured QAOA layer fewer plus one classical round gives a higher value than QAOA at the same girth. To our knowledge these are the highest values for a quantum local algorithm on these graphs at these girths. The classical algorithm of Table 1 gives higher values still where both are computed. For Max-Cut on 3-regular graphs, QAOA followed by classical post-processing was studied in [2].

### 3. The Local Vector algorithm of [1], evaluated by Monte Carlo

Algorithm 1 of [1], with τ optimized and evaluated on fresh samples, gives values at or above the Local Vector column of [1, Table 4]. The τ = 0 values (TPM) agree with [1] to the three digits shown there. At d = 4 the difference is visible:

| k = 3, d = 4, girth | 6 | 8 | 10 | 12 | 14 |
|---|---|---|---|---|---|
| [1, Table 4] | 0.930 | 0.944 | 0.949 | 0.954 | 0.957 |
| Monte Carlo here, s.e. ≤ 0.00016 | 0.9320 | 0.9457 | 0.9532 | 0.9581 | 0.9610 |

Table 1 compares against the values of [1].

## The rules

The rule space is every deterministic rule that is equivariant under renaming the colours. A rule chooses, for each pair (count of neighbours with my colour, sorted counts of the other colours), whether to keep the colour or to move to the colour with a given count rank, splitting ties at random. The rules were optimized by exact coordinate ascent, on the tree value for the quantum algorithm and on Monte Carlo samples for the classical one.

All optimized rules share one shape. A vertex moves only to a least-used colour among its neighbours, and only if that colour is used by fewer neighbours than its own. For k = 3 and d = 4, for example, the rule is: move to a colour that no neighbour has, if there is one and some neighbour shares my colour. Three rarely visited states in the classical rules for k = 4, d = 8 move to the second or third least-used colour instead. The exact rules and all angles are in `data/`.

## Status and checks

Numerical results. No part is formalized in Lean.

- **Quantum values** (Table 2): exact contraction of the tree tensor network [1, 3, 5] at the angles in `data/hybrid_params.json`, in double precision. The edge phase splits into one k × k matrix per index of the label string, so one level costs (2q + 1)·k^(2q+2).
- **Classical values** (Tables 1 and 3): Monte Carlo over the joint Gaussian scores of the vertices within distance 2 of an edge. The covariances are the exact tree overlaps of the vectors of [1, eq. 21, 23]. The lower bounds hold with probability at least 1 − 10⁻⁴ per row over the random samples.
- **Cross-checks:**
  - The contraction reproduces the QAOA values of [1]: for k = 3 at d = 4, 6, 8 up to depth 5 or 6, and for k = 4 at d = 4, 8 up to depth 5. It also gives 0.6925 and 0.7559 for Max-Cut on 3-regular graphs.
  - The value after the round agrees with a full 14-qutrit state vector to 10⁻¹² (k = 3, d = 3, q = 1, random angles and rules).
  - With the rule "keep", the classical program returns the Local Vector value.
- **Not covered:**
  - degrees above 8, except the one row for d = 20;
  - the infinite-degree limit, where [1] reports its largest QAOA advantage;
  - more than one classical round;
  - randomized rules.

## Files

- `sim/treeqaoa.py`: tree contraction for depth-p local algorithms with diagonal edge phases and single-qudit gates.
- `sim/optimize.py`, `sim/chain.py`: QAOA angle optimization with warm starts.
- `sim/hybrid.py`, `sim/hybrid_opt.py`: joint distribution of the measured colours on an edge neighbourhood, and the joint optimization of angles and rule.
- `sim/check_hybrid.py`: re-evaluates every row of Table 2 from `data/hybrid_params.json`.
- `sim/check_hybrid_bruteforce.py`: the state-vector cross-check.
- `sim/lv_baseline.py`, `sim/lv_plus_rule.py`, `sim/lv_certify.py`: Algorithm 1 of [1], the rule search and the fresh-sample evaluation.
- `sim/lv_threshold.py`, `sim/lv_threshold_certify.py`: the threshold rule for large d, and its fresh-sample evaluation (`data/lvthr_cert_3_20.json`).
- `sim/make_tables.py`: builds Tables 1 and 2 from `data/`.

Requirements: Python 3.12 with numpy, scipy and jax. Run the scripts from `sim/`, with the files from `data/` copied in.

## References

1. A. Apte, A. Khan, E. Farhi, K. Marwaha, S. Boulebnane, R. Shaydulin. Provable Classical and Quantum Local Algorithms for Max-k-Cut and Quantum Advantage at Moderate Girth. arXiv:2609.39042, 2026.
2. L. Caha, A. Kliesch, R. Koenig. Twisted hybrid algorithms for combinatorial optimization. arXiv:2203.00717, 2022.
3. E. Farhi, S. Gutmann, D. Ranard, B. Villalonga. Lower bounding the MaxCut of high girth 3-regular graphs using the QAOA. arXiv:2503.12789, 2025.
4. A. Maurer, M. Pontil. Empirical Bernstein Bounds and Sample Variance Penalization. COLT 2009, arXiv:0907.3740.
5. J. Basso, E. Farhi, K. Marwaha, B. Villalonga, L. Zhou. The Quantum Approximate Optimization Algorithm at High Depth for MaxCut on Large-Girth Regular Graphs and the Sherrington-Kirkpatrick Model. TQC 2022, arXiv:2110.14206.
