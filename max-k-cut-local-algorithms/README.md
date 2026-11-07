# Local algorithms for Max-k-Cut on regular graphs of large girth

_6 November 2026_

Max-k-Cut asks for a colouring of the vertices with k colours that leaves as many edges as possible with two different colours. We study local algorithms on d-regular graphs whose girth is large compared with the radius of the algorithm. There the expected cut fraction is the same on every such graph and equals its value on the d-regular tree. Reference [1] computes this value for QAOA with the Grover mixer and for a classical Local Vector algorithm (its Algorithm 1). We compare against its Tables 4 and 5 at the same girth, and for Max-Cut against its Table 3.

Both algorithms below add one classical round to a known local algorithm. In that round every vertex sees its own colour and the colour counts of its neighbours, and may change its colour. The round adds one to the radius. An algorithm of radius R has the tree value on every d-regular graph of girth at least 2R + 2, since then the radius-R neighbourhood of an edge is a tree.

## Results

### 1. Classical: Local Vector algorithm plus one round

Run Algorithm 1 of [1] with parameter m. Then apply one round of a rule that maps (own colour, colour counts of the neighbours) to a new colour, the same rule at every vertex.

With τ > 0, the colour that Algorithm 1 gives a vertex depends on the scores of its neighbours, whose vectors reach distance m − 1. So we count it as radius m, valid at girth 2m + 2, and the algorithm with the round as radius m + 1, valid at girth 2m + 4. [1, Theorem 2] states girth max(2m, 6) for Algorithm 1. As far as we can see, the covariance of the scores of a neighbour of u and a neighbour of v, for an edge uv, can differ from its tree value at girth 2m and 2m + 1, so we use the more cautious count. This may only be a difference in conventions. It does not affect the comparisons below, which use the values of [1] at the girths stated there.

"Lower bound" is the empirical variance bound [4] at confidence 1 − 10⁻⁴ per row, rounded down. It is computed from 10⁶ fresh samples of the edge neighbourhood, independent of the samples used to choose τ and the rule. The rows shown are selected from 29 certified rows (`data/`). All 29 hold together with probability at least 1 − 2.9 · 10⁻³. The values of [1] are rounded to three digits, so a row counts only if its lower bound exceeds them by at least 0.0005.

| k | d | girth | m | Previous best bound [1] | Lower bound | Mean ± s.e. |
|---|---|---|---|---|---|---|
| 3 | 4 | 14 | 5 | 0.961 (QAOA) | **0.9677** | 0.9686 ± 0.0002 |
| 3 | 4 | 16 | 6 | 0.968 (QAOA) | **0.9711** | 0.9719 ± 0.0002 |
| 3 | 6 | 14 | 5 | 0.918 (Local Vector) | **0.9277** | 0.9289 ± 0.0003 |
| 3 | 6 | 16 | 6 | 0.924 (QAOA) | **0.9320** | 0.9332 ± 0.0003 |
| 3 | 6 | 18 | 7 | 0.930 (QAOA) | **0.9351** | 0.9362 ± 0.0002 |
| 3 | 6 | 20 | 8 | 0.934 (QAOA) | **0.9373** | 0.9384 ± 0.0002 |
| 3 | 6 | 22 | 9 | 0.938 (QAOA) | **0.9390** | 0.9401 ± 0.0002 |
| 3 | 8 | 16 | 6 | 0.894 (QAOA) | **0.9028** | 0.9042 ± 0.0003 |
| 3 | 8 | 18 | 7 | 0.899 (QAOA) | **0.9058** | 0.9071 ± 0.0003 |
| 3 | 8 | 20 | 8 | 0.904 (QAOA) | **0.9079** | 0.9093 ± 0.0003 |
| 3 | 8 | 22 | 9 | 0.908 (QAOA) | **0.9094** | 0.9108 ± 0.0003 |
| 4 | 4 | 12 | 4 | 0.993 (QAOA) | **0.9963** | 0.9966 ± 0.0001 |
| 4 | 4 | 14 | 5 | 0.996 (QAOA) | **0.9971** | 0.9974 ± 0.0001 |
| 4 | 8 | 14 | 5 | 0.956 (QAOA) | **0.9641** | 0.9650 ± 0.0002 |
| 4 | 8 | 16 | 6 | 0.961 (QAOA) | **0.9675** | 0.9683 ± 0.0002 |
| 4 | 8 | 18 | 7 | 0.966 (QAOA) | **0.9684** | 0.9692 ± 0.0002 |

For larger degree the full rule space is too big to search, so we restrict to a threshold rule: move to a least-used colour (ties at random) if it is used by at least t fewer neighbours than the own colour. For Max-3-Cut on 20-regular graphs, with τ = 3 and t = 2, from 6 · 10⁵ fresh samples:

| k | d | girth | m | Previous best bound [1] | Lower bound | Mean ± s.e. |
|---|---|---|---|---|---|---|
| 3 | 20 | 22 | 9 | 0.825 (QAOA, depth 10) | **0.8271** | 0.8294 ± 0.0005 |

With two rounds, first at the vertices within distance 1 of the edge and then at its endpoints, the radius is m + 2, valid at girth 2m + 6 (`sim/lv2rounds.py`, 2 · 10⁶ fresh samples):

| k | d | girth | m | Previous best bound [1] | Lower bound | Mean ± s.e. |
|---|---|---|---|---|---|---|
| 3 | 4 | 18 | 6 | 0.973 (QAOA) | **0.9751** | 0.9756 ± 0.0001 |

So for Max-3-Cut on 6- and 8-regular graphs and Max-4-Cut on 8-regular graphs, this classical algorithm, with one round, is above every value of [1, Tables 4, 5] at each girth in the table, which includes QAOA up to depth 10 for k = 3 and up to depth 8 for k = 4. On 4-regular graphs the same holds at girth 14 to 18 for k = 3 and at girth 12 and 14 for k = 4, and on 20-regular graphs at girth 22 for k = 3. Girth 18 for k = 3, d = 4 uses two rounds.

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

### 3. The Local Vector algorithm of [1], evaluated by random sampling

Algorithm 1 of [1], with τ optimized and evaluated on fresh samples, gives values at or above the Local Vector column of [1, Table 4]. The τ = 0 values (TPM) agree with [1] to within 0.001. At d = 4 the difference is visible:

| k = 3, d = 4, parameter m | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|
| [1, Table 4] | 0.930 | 0.944 | 0.949 | 0.954 | 0.957 |
| Random sampling here, s.e. ≤ 0.00016 | 0.9320 | 0.9457 | 0.9532 | 0.9581 | 0.9610 |

[1] lists these at girth 2m. Table 1 compares against the values of [1].

### 4. Max-Cut: Local Vector algorithm plus one round

For k = 2 the colour that Algorithm 1 of [1] gives a vertex v is the sign of z_v = Y_v − (τ/√d)·Σ_{w∼v} Y_w, where Y is the difference of the two coordinates of the normal score vectors. So only the 2d scores of the vertices within distance 1 of the edge are sampled, from their exact covariance, and 10⁷ samples per cell are cheap (`sim/lv2.py`). One round of a rule as in Section 1 follows. The optimized rules change the side of a vertex if the number of its neighbours on its own side lies in a band from t to t′, with t just above d/2 and t′ ≤ d. For d = 30 and 40 the search is restricted to thresholds, t′ = d.

Each cell gives the lower bound, at confidence 1 − 10⁻⁴ per cell from 10⁷ fresh samples, and in brackets the previous best bound: the largest value of [1, Table 3] at that girth, over QAOA up to depth (girth − 2)/2 and the Local Vector algorithm. A cell is shown if the lower bound exceeds it by at least 0.0005. The cells shown are selected from 86 certified rows (`data/lv2_k2.jsonl`). All 86 hold together with probability at least 1 − 8.6 · 10⁻³.

| girth | d = 4 | d = 6 | d = 8 | d = 10 | d = 20 | d = 30 | d = 40 |
|---|---|---|---|---|---|---|---|
| 12 |  | **0.7428** (0.742) | **0.7111** (0.709) | **0.6874** (0.686) | **0.6315** (0.631) | **0.6076** (0.606) | **0.5936** (0.592) |
| 14 |  | **0.7517** (0.747) | **0.7186** (0.712) | **0.6945** (0.690) | **0.6364** (0.634) | **0.6110** (0.608) | **0.5968** (0.594) |
| 16 | **0.8127** (0.810) | **0.7580** (0.751) | **0.7237** (0.716) | **0.6994** (0.693) | **0.6398** (0.635) | **0.6137** (0.611) | **0.5991** (0.595) |
| 18 | **0.8186** (0.814) | **0.7624** (0.754) | **0.7275** (0.719) | **0.7028** (0.695) | **0.6422** (0.637) | **0.6156** (0.612) | **0.6006** (0.597) |
| 20 | **0.8230** (0.816) | **0.7657** (0.757) | **0.7302** (0.722) | **0.7053** (0.698) | **0.6438** (0.639) | **0.6168** (0.614) | **0.6018** (0.598) |
| 22 | **0.8263** (0.820) | **0.7682** (0.761) | **0.7323** (0.725) | **0.7072** (0.701) | **0.6451** (0.642) | **0.6179** (0.616) | **0.6027** (0.600) |
| 24 | **0.8289** (0.823) | **0.7701** (0.764) | **0.7339** (0.728) | **0.7086** (0.704) | **0.6461** (0.644) | **0.6180** (0.617) | **0.6033** (0.601) |
| 26 | **0.8310** (0.826) | **0.7716** (0.767) | **0.7352** (0.731) | **0.7097** (0.706) | **0.6468** (0.646) |  | **0.6037** (0.603) |
| 28 | **0.8327** (0.829) | **0.7729** (0.769) | **0.7362** (0.733) | **0.7104** (0.709) |  |  | **0.6041** (0.603) |
| 30 | **0.8341** (0.832) | **0.7739** (0.772) | **0.7370** (0.735) | **0.7112** (0.710) |  |  | **0.6045** (0.603) |

For d = 4, 6, 8, 10 and 40 this covers every girth from 16 (d = 4) or 12 (d = 6, 8, 10, 40) up to 30, the largest girth in [1, Table 3]. For d = 20 it covers girth 12 to 26, and for d = 30 girth 12 to 24. At the smaller girths the Local Vector column of [1] is above QAOA. So is, by at least 0.0025, the best linear factor of the same radius (see Status and checks), which holds under the cautious radius count of Section 1. So at every girth of [1, Table 3], for d = 4, 6, 8, 10 and 40, a classical local algorithm has a value at least as high as QAOA. For d = 3 this was shown in [6] with a different classical algorithm, which also asked about higher degree.

### 5. Classical: colour-vector dynamics, Max-3-Cut on 4-regular graphs

Every vertex carries a unit vector ψ in ℂᵏ. It starts at cos α · u + sin α · w_c, where u is the uniform vector, c is a uniformly random colour, the only randomness, and w_c is the unit vector along e_c − u/√k. Each of the p layers multiplies ψ(c) by exp(−iγ_n h(c)), where h(c) is the sum of |ψ_j(c)|² over the neighbours j, and then applies exp(−iβ_n |u⟩⟨u|). The output colour is the c with the largest |ψ(c)|. For k = 2 this is the rotation dynamics VIRAL of [6]. In general it is the classical counterpart of QAOA with the Grover mixer, with one vector per vertex in place of the quantum state. Its radius is p, so its tree value holds at girth 2p + 2, as for QAOA at depth p.

The 2p + 1 parameters are trained by gradient descent on the radius-p tree itself, on a smooth version of the cut fraction (`sim/cdyn_train.py`), after a first training on a random 4-regular graph (`sim/cdyn.py`). Depth 10 uses the depth-9 schedule with its last layer repeated. The tree value is then estimated from fresh seeds (`sim/cdyn_tree.py`), with the lower bound of Section 1 at confidence 1 − 10⁻⁴ per row. All 9 rows hold together with probability at least 1 − 9 · 10⁻⁴.

| girth | p | QAOA [1], depth p | Previous best bound [1] | Lower bound | Mean ± s.e. | Samples |
|---|---|---|---|---|---|---|
| 6 | 2 | 0.891 | 0.930 (Local Vector) | 0.8992 | 0.9006 ± 0.0003 | 10⁶ |
| 8 | 3 | 0.921 | 0.944 (Local Vector) | 0.9335 | 0.9346 ± 0.0002 | 10⁶ |
| 10 | 4 | 0.940 | 0.949 (Local Vector) | **0.9521** | 0.9531 ± 0.0002 | 10⁶ |
| 12 | 5 | 0.952 | 0.954 (Local Vector) | **0.9621** | 0.9630 ± 0.0002 | 10⁶ |
| 14 | 6 | 0.961 | 0.961 (QAOA) | **0.9709** | 0.9717 ± 0.0002 | 10⁶ |
| 16 | 7 | 0.968 | 0.968 (QAOA) | **0.9754** | 0.9761 ± 0.0002 | 10⁶ |
| 18 | 8 | 0.973 | 0.973 (QAOA) | **0.9801** | 0.9808 ± 0.0001 | 10⁶ |
| 20 | 9 | 0.977 | 0.977 (QAOA) | **0.9836** | 0.9845 ± 0.0002 | 5 · 10⁵ |
| 22 | 10 | 0.980 | 0.980 (QAOA) | **0.9848** | 0.9858 ± 0.0002 | 3 · 10⁵ |

So for Max-3-Cut on 4-regular graphs this classical local algorithm is above QAOA at every girth of [1, Table 4], from 6 to 22, and above every value of [1] from girth 10 on, by 0.003 to 0.010. From girth 14 on it is also above Sections 1 and 2. To our knowledge these are the highest values for a local algorithm on these graphs at these girths.

## The rules

The rule space is every deterministic rule that is equivariant under renaming the colours. A rule chooses, for each pair (count of neighbours with my colour, sorted counts of the other colours), whether to keep the colour or to move to the colour with a given count rank, splitting ties at random. The rules were optimized by exact coordinate ascent, on the tree value for the quantum algorithm and on random samples for the classical one.

All optimized rules share one shape. A vertex moves only to a least-used colour among its neighbours, and only if that colour is used by fewer neighbours than its own. For the quantum algorithm at k = 3 and d = 4, for example, the rule is: move to a colour that no neighbour has, if there is one and some neighbour shares my colour. Three rarely visited states in the classical rules for k = 4, d = 8 move to the second or third least-used colour instead. The exact rules and all angles are in `data/`.

## Status and checks

Numerical results. No part is formalized in Lean.

- **Quantum values** (Table 2): exact contraction of the tree tensor network [1, 3, 5] at the angles in `data/hybrid_params.json`, in double precision. The edge phase splits into one k × k matrix per index of the label string, so one level costs (2q + 1)·k^(2q+2).
- **Classical values** (Tables 1 and 3): `sim/lv_certify.py` and `sim/lv_baseline.py`, random sampling of the joint normal scores of the vertices within distance 2 of an edge (distance 3 for two rounds). The covariances are the exact tree overlaps of the vectors of [1, eq. 21, 23]. The lower bounds hold with probability at least 1 − 10⁻⁴ per row over the random samples.
- **Cross-checks:**
  - The contraction (`sim/chain.py`) reproduces the QAOA values of [1]: for k = 3 at d = 4, 6, 8 up to depth 5 or 6, and for k = 4 at d = 4, 8 up to depth 5. It also gives 0.6925 and 0.7559 for Max-Cut on 3-regular graphs.
  - The value after the round agrees with a full 14-qutrit state vector to 10⁻¹² (k = 3, d = 3, q = 1, random angles and rules).
  - With the rule "keep", the classical program returns the Local Vector value.
  - The tree evaluation of Section 5 (`sim/cdyn_tree.py`, single precision, one level of the tree per array) agrees with the graph dynamics of `sim/cdyn.py` run in double precision on an explicit radius-3 tree (`sim/cdyn_check.py`): 0.93463 ± 0.00025 from 10⁶ samples against 0.93461 from 2 · 10⁵ edges.
  - For k = 2, the reduced sampler of `sim/lv2.py` agrees with the full program of `sim/lv_plus_rule.py` within the statistical error: 0.7800 against 0.7798 at d = 4, m = 3, and 0.7530 against 0.7528 at d = 6, m = 5, with s.e. 0.0007.
  - For k = 2, the best linear factor of i.i.d. normal variables of the same radius with sign rounding, the class of [7], computed exactly as a generalized eigenvalue problem (`sim/linfactor.py`), is at least 0.0025 below every cell of Section 4. At every girth of [1, Table 3] not covered by Section 4, it is above QAOA by at least 0.0025 for d = 4, 6, 8, 10 and 40.
- **Not covered:**
  - for k = 3 and 4, degrees above 8, except the one row for d = 20;
  - the dynamics of Section 5 for other k and d. The tree has 2(d − 1)^p leaves, which limits sampling to small d;
  - the infinite-degree limit, where [1] reports its largest QAOA advantage;
  - more than two classical rounds;
  - randomized rules.

## Files

- `sim/treeqaoa.py`: tree contraction for depth-p local algorithms with diagonal edge phases and single-qudit gates.
- `sim/optimize.py`, `sim/chain.py`: QAOA angle optimization with warm starts.
- `sim/hybrid.py`, `sim/hybrid_opt.py`: joint distribution of the measured colours on an edge neighbourhood, and the joint optimization of angles and rule.
- `sim/check_hybrid.py`: re-evaluates every row of Table 2 from `data/hybrid_params.json`.
- `sim/check_hybrid_bruteforce.py`: the state-vector cross-check.
- `sim/lv_baseline.py`, `sim/lv_plus_rule.py`, `sim/lv_certify.py`: Algorithm 1 of [1], the rule search and the fresh-sample evaluation.
- `sim/lv_threshold.py`, `sim/lv_threshold_certify.py`: a threshold rule for large d, and its fresh-sample evaluation (`data/lvthr_cert_3_20.json`).
- `sim/lv2rounds.py`: Algorithm 1 of [1] with two rounds (`data/lv2rounds_cert.jsonl`).
- `sim/lv2.py`: the Max-Cut case of Section 4 (`data/lv2_k2.jsonl`); `sim/linfactor.py`: the linear-factor check.
- `sim/cdyn.py`, `sim/cdyn_train.py`, `sim/cdyn_tree.py`, `sim/cdyn_check.py`: the dynamics of Section 5, its training on a graph and on the tree, the tree value and the cross-check (`data/cdyn_params_3_4.jsonl`, `data/cdyn_cert_3_4.jsonl`).
- `sim/make_tables.py`: builds Tables 1 and 2 from `data/`.

Requirements: Python 3.12 with numpy, scipy and jax. Run the scripts from `sim/`, with the files from `data/` copied in.

## References

1. A. Apte, A. Khan, E. Farhi, K. Marwaha, S. Boulebnane, R. Shaydulin. Provable Classical and Quantum Local Algorithms for Max-k-Cut and Quantum Advantage at Moderate Girth. arXiv:2609.39042, 2026.
2. L. Caha, A. Kliesch, R. Koenig. Twisted hybrid algorithms for combinatorial optimization. arXiv:2203.00717, 2022.
3. E. Farhi, S. Gutmann, D. Ranard, B. Villalonga. Lower bounding the MaxCut of high girth 3-regular graphs using the QAOA. arXiv:2503.12789, 2025.
4. A. Maurer, M. Pontil. Empirical Bernstein Bounds and Sample Variance Penalization. COLT 2009, arXiv:0907.3740.
5. J. Basso, E. Farhi, K. Marwaha, B. Villalonga, L. Zhou. The Quantum Approximate Optimization Algorithm at High Depth for MaxCut on Large-Girth Regular Graphs and the Sherrington-Kirkpatrick Model. TQC 2022, arXiv:2110.14206.
6. F. Morone, S. Rawat, D. Sels. Whither quantum advantage? New classical lower bounds for Max-Cut on large-girth 3-regular graphs. arXiv:2610.17236, 2026.
7. J. Thompson, O. Parekh, K. Marwaha. An explicit vector algorithm for high-girth MaxCut. SOSA 2022, arXiv:2108.12477.
