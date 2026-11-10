# The QAOA fixed-angle conjecture on K_{d,d} at depth 2: counterexamples for 9 ≤ d ≤ 351, but not for every d

Written 7 Nov 2026.

## Problem

For MaxCut on d-regular graphs, the fixed-angle conjecture [1, Conjecture 2] says that the depth-p QAOA with the angles that are optimal on the regular tree (girth at least 2p + 2) cuts at least the tree-optimal fraction f^tree*_{p,d} of the edges on every d-regular graph. [1, Theorem 8] refutes it at p = 2 with the complete bipartite graph K_{9,9}, by a computer-assisted proof. For other degrees, [1] reports that preliminary numerics suggest K_{d,d} with d < 9 is not a counterexample, and leaves the case d > 9 open: whether the effect of the 4-cycles "always has to be destructive" is "a priori not clear", and [1] explicitly does not conjecture it for every d > 9. [1, Corollary 11] also shows that K_{9,9} with its own optimal angles is not a counterexample to the weaker large-loop conjecture [1, Conjecture 1].

## Results

All statements are for p = 2, from exact evaluations in double precision (method below). They are numerical, not certified with interval arithmetic as in [1, Theorem 8]. Write t(d) for the tree optimum f^tree*_{2,d} and k(d) for the cut fraction of K_{d,d} at the tree-optimal angles.

**1. Small degrees.** For 2 ≤ d ≤ 8, k(d) > t(d), so K_{d,d} is not a counterexample, as suggested in [1]. The same holds for the hypercubes Q_3, Q_4 and for K_{m,m} minus a perfect matching, 4 ≤ m ≤ 8 (degrees 3 to 7).

**2. Counterexamples for 9 ≤ d ≤ 351.** k(d) < t(d) for every 9 ≤ d ≤ 351, so K_{d,d} refutes the fixed-angle conjecture at p = 2 for all these degrees. The largest gap is t(d) − k(d) = 0.0846 at d = 22. At d = 9 the computed tree optimum 0.6391275409 equals the threshold b of [1, Theorem 8], and the gap is 0.0056 (at least c = 0.0029 by [1, Theorem 8]).

**3. Not for every d.** k(d) > t(d) for d in [352, 384], [586, 643] and [884, 966], and for no other d ≤ 1060; so 878 of the 1052 degrees 9 ≤ d ≤ 1060 give counterexamples. The smallest degree above 8 at which K_{d,d} is not a counterexample is d = 352, with k − t = +9.3 · 10^{−6}. At larger d the two cases keep alternating (table below).

**4. The large-loop conjecture holds on K_{d,d}.** For every 9 ≤ d ≤ 1060, K_{d,d} at the angles β = (−0.360743, −0.564711), γ = (−3.2955, −3.0938)/d cuts more than t(d), by at least 0.016. So K_{d,d} is not a counterexample to [1, Conjecture 1] at p = 2 in this range, which extends [1, Corollary 11] from d = 9.

| d | 9 | 22 | 351 | 352 | 368 | 384 | 385 | 600 | 1250 | 1500 | 1750 | 2000 | 2250 | 2500 | 2750 | 3000 | 4000 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 10⁴ (k − t) | −56.4 | −846.1 | −1.6 | +0.09 | +13.3 | +0.13 | −1.5 | +16.4 | +5.7 | −141.0 | +29.4 | −124.6 | +30.9 | −118.0 | +22.4 | −73.7 | −0.5 |

## Why the sign alternates

With the tree-optimal angles, γ_t = g_t/√d with g converging to about (0.7635, 1.3311) and β to about (0.4960, 0.2691). On the tree, √d(t(d) − 1/2) tends to 0.4076, the large-degree value of [2]. On K_{d,d} the cost is (d² − M_A M_B)/2 with M_A, M_B the sums of the Z operators on the two sides. The first phase layer rotates every qubit of one side by g_1 M/√d about the Z axis, where M is the sum on the other side, an O(1) angle. The first mixer then turns this into a magnetisation of order d sin(2β_1) on each side. So the second phase layer rotates the qubits by angles of order √d g_2 sin(2β_1), and the cut fraction oscillates in √d. Numerically this is what happens. At the fixed angles β = (0.4960, 0.2691), g = (0.7635, 1.3311), sampled at 101 values 1000 ≤ d ≤ 4000, √d(k − 1/2) fits a + b cos(ω√d + φ) with ω = 1.116 (against g_2 sin(2β_1) = 1.114), mean a = 0.19 and amplitude 0.37, with residual 0.023 (rms). Its peaks lie above 0.4076, so windows of both signs recur: 25 of the 101 sampled d are above the tree level. Below d = 1060 the windows have widths 0.83, 1.15 and 1.35 in √d and are about 5.6 apart, close to 2π/ω.

## Method

- **Tree.** The edge value of the depth-p double tree is a sum over histories h ∈ {±1}^{2p+1} of each qubit (forward bits, middle bit, backward bits). Each vertex contributes a weight f(h) from the mixers and each edge a phase exp(i Σ_t (γ_t/2)(z_t z′_t − w_t w′_t)). Summing out the leaves first gives a recursion on vectors of length 2^{2p+1} = 32, so t(d) costs O(d) to evaluate for any d; the large-degree iteration of [2] is the same idea.
- **K_{d,d}.** The state stays symmetric on each side, so it lives in the (d + 1)²-dimensional span of products of two symmetric states, each fixed by its number of ones. The phase layer is diagonal there and the mixer is a rotation of each collective spin. [1] uses the same symmetry.
- Both evaluators agree with a plain statevector to 10^{−10} (tree for d = 3, 4; K_{d,d} for d ≤ 5).
- **Tree-optimal angles.** Continuation in d from the d = 9 optimum, polished by second-order steps on central differences (gradient below 10^{−7} everywhere). The value is checked against 300 random starts over the box of [1] at d = 9, 30, 100, 352, 384, 600, 643, 900, 966 and 1060. No start found a larger value. At d = 352 the margin +9.3 · 10^{−6} is far above the effect of the remaining angle error.

## Files

- `sim/qaoa.py`: the three evaluators (tree, K_{d,d}, statevector) and their self-test.
- `sim/refine.py`: tree-optimal angles with second-order polishing and k(d), for a range of d. `sim/scan.txt` is its output for 9 ≤ d ≤ 1060, with the value of the 1/d family of result 4.
- `sim/big.py`, `sim/big.txt`: the large-d values in the table.
- `sim/fixedK.py`, `sim/dense.txt`: k at the fixed large-degree angles for 1000 ≤ d ≤ 4000 (step 30), used for the fit above.
- `sim/globalcheck.py`: the random-start check of the tree maximiser. `sim/kown.py`: the search over all angles on K_{d,d} that gave the angles of result 4 (at d = 30).
- `sim/others.py`, `sim/others.txt`: the hypercubes and the bipartite graphs minus a matching.
- `sim/check.py` (about 15 minutes): the evaluators against the statevector, the tree optimum from scratch and the sign of k − t at d = 2, …, 8, 9, 22 and at the window edges 351, 352, 384, 385, 585, 586, 643, 644, and result 4 at selected d. Output in `sim/out.txt`.

## References

1. L. Binkowski. Refuting the QAOA fixed-angle conjecture. arXiv:2609.27703 (2026).
2. J. Basso, E. Farhi, K. Marwaha, B. Villalonga, L. Zhou. The Quantum Approximate Optimization Algorithm at High Depth for MaxCut on Large-Girth Regular Graphs and the Sherrington-Kirkpatrick Model. TQC 2022, arXiv:2110.14206.
