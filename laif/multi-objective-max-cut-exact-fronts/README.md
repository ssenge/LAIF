# Exact Pareto sets of multi-objective weighted Max-Cut on heavy-hex graphs

_18 November 2026_

The quantum approximate multi-objective optimization benchmark of [1] asks for the Pareto set of m weighted Max-Cut objectives on one graph. Each objective is the total weight of the cut edges, f_j(x) = Σ_{(u,v) cut by x} w_j(u, v), with weights drawn from N(0, 1). The quality of a set of cuts is its hypervolume (HV) above a fixed reference point. The main instances of [1] are on a 42-node subgraph of a 156-qubit heavy-hex processor with 46 edges, with m = 3 and m = 4 objectives.

This folder gives the complete Pareto sets of the 42-node instances of [1] for their real-valued weights, with exact hypervolumes, computed in 0.1 s and 2.3 s on one CPU core. For m = 4 this shows that the front of 30 419 points found by quantum annealing in [2], believed optimal there, is the complete Pareto set. The folder also maps how far the exact computation reaches on heavy-hex and square lattices up to 156 qubits, and gives exact mean-variance and mean-CVaR fronts for a 100-asset portfolio instance in the setting of [8].

## Result

**The 42-node instances of [1], exact.**

| Objectives m | Exact Pareto points | Exact HV | Stated before | Time here, one CPU core |
|---|---|---|---|---|
| 3 | 2 067 | 43 471.7037 | HV_max = 43 471.704 and 2 067 points by DPA-a on weights scaled by 10⁴ and rounded, 3.6 min [1]; 2 067 points by annealing [2] | 0.1 s |
| 4 | 30 419 | 1 266 143.3494 | HV_max = 1 266 143.350 by DPA-a on weights scaled by 10³ and rounded, just under 20 000 s [1]; 30 419 points by annealing, believed optimal [2] | 2.3 s |

Pareto points are counted as distinct objective vectors, and the reference points are those of the instance files of [1]. So the front of 30 419 points of [2] is the complete Pareto set for m = 4, and the HV_max values of [1] are the exact optima to the stated precision. For m = 3, the exact Pareto set of the rounded weights computed by DPA-a in [1] already has the same 2 067 points.

The baselines of [1] are objective-space methods that call a MIP solver (DPA-a, DCM, a randomized ε-constraint method), weighted-sum methods and semidefinite rounding. QAOA samples are timed in [1] at an assumed rate of 10 000 shots per second, described there as an idealistic assumption that excludes circuit compilation. At this rate, hardware runs at depth 4 to 6 overtake the HV of the randomized ε-constraint method after 1230 s to 535 s for m = 3, and a fidelity-scaled estimate for m = 4 overtakes DCM and the ε-constraint method after about 5000 s. In [1] these results are read as a potential to outperform classical approaches.

The dynamic program here uses the graph structure: the 42-node graph has pathwidth at most 4, and the method processes it with at most 2⁴ frontier states. This hints at a possible gap in the hardness of the benchmark at this size, since an exact method that uses the sparse hardware graph reaches the full Pareto set within seconds.

**Scaling.** Patches of the 156-qubit heavy-hex lattice with the first k of its 8 rows of 16 qubits and the bridge qubits between them (n = 36, 56, ..., 156), and square lattices with k rows of 12 (n = 24, 48, ..., 120). Weights N(0, 1), three random instances per entry. Time and peak memory are the largest of the three runs, on one core.

| Graph | n | Frontier width | m = 2: points / time | m = 3: points / time / memory | m = 4: points / time / memory |
|---|---|---|---|---|---|
| heavy-hex | 36 | 3 | 50 to 79 / < 0.1 s | 737 to 1 934 / 0.1 s | 22 511 to 27 856 / 1.4 s / 0.1 GB |
| heavy-hex | 56 | 4 | 107 to 207 / 0.1 s | 3 448 to 4 464 / 0.6 s | 53 806 to 68 507 / 10 s / 0.2 GB |
| heavy-hex | 76 | 5 | 127 to 187 / 0.1 s | 6 397 to 15 378 / 6 s / 0.1 GB | 461 290 to 1 076 808 / 10 min / 2.9 GB |
| heavy-hex | 96 | 6 | 291 to 446 / 0.5 s | 14 243 to 20 129 / 18 s / 0.3 GB | 589 370 to 886 042 / 29 min / 4.7 GB |
| heavy-hex | 116 | 6 | 466 to 497 / 0.6 s | 48 961 to 61 466 / 54 s / 0.3 GB | |
| heavy-hex | 136 | 6 | 358 to 748 / 1.2 s | 71 495 to 134 721 / 2.6 min / 0.7 GB | |
| heavy-hex | 156 | 6 | 538 to 611 / 1.1 s | 98 275 to 189 160 / 4.0 min / 1.0 GB | |
| square | 24 | 2 | 13 to 46 / < 0.1 s | 401 to 703 / < 0.1 s | 1 896 to 5 453 / 0.2 s |
| square | 48 | 4 | 58 to 86 / 0.1 s | 963 to 2 546 / 0.4 s | 22 148 to 40 012 / 11 s / 0.2 GB |
| square | 72 | 6 | 182 to 214 / 0.4 s | 4 399 to 9 265 / 7 s / 0.1 GB | 68 253 to 337 176 / 7.4 min / 1.7 GB |
| square | 96 | 8 | 178 to 279 / 2.1 s | 11 123 to 24 357 / 89 s / 0.4 GB | 425 597 / 34 min / 2.5 GB (one instance) |
| square | 120 | 10 | 284 to 396 / 8.6 s | 32 893 to 46 172 / 11 min / 1.5 GB | |

With m = 5 on heavy-hex: 53 897 to 184 029 points at 36 qubits in at most 7 s, and 1.04 · 10⁶ to 1.44 · 10⁶ points at 56 qubits in at most 6.7 min and 3.7 GB.

Empty cells were not completed within one hour and 6 GB on one core; at 116 qubits with m = 4 the memory limit is reached first. Full logs: `data/scale_heavyhex.txt`, `data/scale_square.txt`.

So with two or three objectives the exact Pareto set is computed for every heavy-hex patch up to the full 156-qubit lattice, in at most four minutes, and for square lattices up to 10 × 12. The size of the Pareto set grows fast with m: on the 156-qubit lattice it has about 10² points for m = 2 and 10⁵ for m = 3. For m = 4 the set reaches about 10⁶ points at 76 to 96 qubits, and the method then needs tens of minutes and several GB.

## Where the exact method stops

The cost of the dynamic program is driven by two quantities: the frontier width w, which enters as 2^w states, and the number of non-dominated partial cut vectors kept per state, which grows with the size of the Pareto set. On heavy-hex patches w stays at most 6 up to 156 qubits, so the size of the Pareto set dominates. On square lattices w grows with the number of rows, and at m = 3 the time grows from 7 s at w = 6 to 11 min at w = 10.

So this exact reference covers the benchmark family of [1] at m ≤ 3 up to 156 qubits, at m = 4 up to about 100 qubits, and at m = 5 up to about 60 qubits. Instances with m = 4 objectives on more than about 100 qubits, with m = 5 on more than about 60 qubits, or on graphs of larger pathwidth such as denser or non-planar couplings, remain beyond it in one hour on one core. There, a hypervolume comparison has no exact reference from this method, and a quantum sampler would also face Pareto sets of 10⁶ points and more. The larger instances of the later work also lie there: random graphs with edge probability 0.5 and complete graphs on 100 to 200 nodes [3, 4] and dense multi-objective QUBOs with 100 to 1000 variables [5] have pathwidth close to the number of nodes.

## Portfolio fronts

In [8], binary portfolio selection under a Conditional Value-at-Risk (CVaR) constraint is reduced to the Pareto set of the two objectives max μᵀx and min xᵀΣx over x ∈ {0, 1}¹⁰⁰, since under Gaussian returns CVaR_α = −μᵀx + κ_α (xᵀΣx)^{1/2} is monotone in both. The covariance is sparsified to the 297 pairs of assets that meet on adjacent qubits during 4 alternating SWAP layers on a line of 100 qubits, so the same frontier dynamic program applies, with frontier width 5 along the line.

The instance of [8] is not public. The instance here is regenerated from the distribution stated in [8]: constant-correlation covariance with σ_i ~ U(0.1, 0.3) and ρ = 0.3, returns μ_i ~ U(0, 0.1), placement of the assets on the line by a quadratic assignment that maximizes the retained squared covariance, and a diagonal shift to positive semidefiniteness. With the NumPy generator at seed 0, the stated sum of returns 5.3097, their range [0.0006, 0.0995], the eigenvalue range [0.0071, 1.4715] of the dense covariance and the shift δ = 0.0606 are matched. The placement comes from a heuristic and is not recovered exactly: it retains 7.678 % of the squared off-diagonal covariance, against 7.683 % in [8]. So the numbers below belong to a closely matching instance, not to the instance of [8].

| Front | Exact Pareto points | Exact normalized HV | ε-constraint with 1000 values, same instance: points / HV |
|---|---|---|---|
| mean-variance | 2 042 | 0.8479 | 899 / 0.8477 |
| mean-CVaR, α = 90 % | 461 | 0.7770 | 255 / 0.7768 |
| mean-CVaR, α = 95 % | 731 | 0.7180 | 425 / 0.7178 |
| mean-CVaR, α = 99 % | 1 129 | 0.6896 | 660 / 0.6894 |

The exact mean-variance set takes about 1 s on one CPU core. The normalization and reference point (1.05, 1.05) are those of [8]. The mean-CVaR fronts are the non-dominated parts of the mean-variance set, which gives the exact optimum of the CVaR-constrained problem for every risk budget. The last column applies the ε-constraint reference of [8] (1000 equidistant bounds on the normalized return) to the exact set; on this instance it is within 0.03 % of the exact HV.

## Method

**Frontier dynamic program.** The vertices are processed in an order of small frontier width (breadth-first orders from every vertex and coordinate sweeps, the best one kept). A state is the side of each vertex in the current frontier. Each state carries the set of cut vectors of the processed edges that are not dominated by another vector of the same state. Adding a vertex extends each state by both sides and adds the weights of the cut edges to the already processed neighbours. A vertex leaves the frontier once all its neighbours are processed, and states that agree on the remaining frontier are merged and filtered. The first vertex is fixed to one side, since a cut and its complement have the same value. At the end the frontier is empty, and the single remaining set is the Pareto set. The time is O(n · 2^w · L · c(L)) for at most L labels per state and a non-dominance filter of cost c(L) per label.

Pareto-set dynamic programming over tree decompositions is known from [6], with algorithms for multicriteria s-t cut, minimum spanning tree and TSP parameterized by treewidth. The Max-Cut and portfolio programs here follow the same scheme.

**Checks.**

- `sim/test_pareto_dp.py`: the dynamic program against brute force on 60 random graphs with 4 to 12 vertices and 2 to 4 objectives, every third with integer weights in {−2, ..., 2} to create ties and zero weights. All Pareto sets agree.
- `sim/pareto_dp.py` runs a brute-force self-test on a 3 × 4 grid before each instance.
- `sim/qamoo_check.py` recomputes both 42-node instances and asserts the point counts and the HV values of the table. For m = 3 the HV is computed twice, with the library of [7] and with the exact slicing method of `sim/hv3.py`, which is itself checked against a Monte Carlo estimate.
- `sim/pareto_qubo.py`: the program for general multi-objective QUBOs, against brute force on 40 random instances with up to 10 variables and 2 or 3 objectives, and every Pareto point checked against a binary vector that attains it. `sim/portfolio.py` checks the SWAP pattern (198 SWAP gates, 297 pairs) and recomputes return and variance of sampled Pareto portfolios.

## Lean

`lean/ParetoDP/Basic.lean` proves, for values in any partially ordered additive commutative monoid (for example ℝ^m with the pointwise order) and any finite state space and transitions:

- `pruned_eq_nondom_exact`: if the non-dominated subset is taken after every step, the set of every state at every step equals the non-dominated part of the set of all values reachable in that state.
- `final_eq`: the same holds for the union over the final states.
- `nondom_eq_of_cover`: two finite sets X ⊆ Y, where every element of Y lies below an element of X, have the same non-dominated part.

These use only the standard axioms (`lean/axioms.txt`).

**Scope:** Lean covers the pruning theorem. The encoding of cuts and portfolios as runs of the program (frontier states, forgetting of vertices, the fixed first vertex) and the floating-point arithmetic are not formalized; they rest on the brute-force checks above.

## Files

- `sim/pareto_dp.py`: the dynamic program, with a self-test.
- `sim/test_pareto_dp.py`: comparison with brute force.
- `sim/hv3.py`: exact hypervolume in three dimensions.
- `sim/qamoo_check.py`: the 42-node instances of [1]. It reads the instance files of [1] (`data/problems/42q/problem_set_42q_0s_3o_0` and `..._4o_0` of the repository of [1]) and writes `data/front_42q_3o.npy` and `data/front_42q_4o.npy`, the exact Pareto sets as arrays of objective vectors.
- `sim/heavyhex.py`: the 156-qubit heavy-hex lattice and its row patches.
- `sim/probe.py`, `sim/run_scale.sh`: the scaling runs.
- `sim/pareto_qubo.py`: the program for multi-objective QUBOs, with a self-test.
- `sim/portfolio.py`: the portfolio instance and its exact mean-variance set (`data/portfolio_s0_k4.npz`: μ, Σ, the Pareto points and one portfolio for each).
- `sim/portfolio_hv.py`: the mean-CVaR fronts and the normalized hypervolumes.
- `lean/`: the Lean files. Build with `lake exe cache get` and then `lake build`; `lake env lean Axioms.lean` prints the axioms.

## References

1. A. Kotil, E. Pelofske, S. Riedmüller, D. J. Egger, S. Eidenbenz, T. Koch, S. Woerner. Quantum approximate multi-objective optimization. Nature Computational Science (2025). arXiv:2503.22797. Data: https://github.com/stefan-woerner/qamoo
2. A. D. King. Multi-objective optimization by quantum annealing. arXiv:2511.01762.
3. X.-Z. Tao, P. Mosharev, Z. Su, M.-H. Yung. Multi-objective optimization with quantum-annealing-inspired algorithms. arXiv:2604.26477.
4. J. Huang, C.-H. Huang, A. Velasquez, R. Wang, J. Liu, I. Alkhouri. Parallelizable gradient-based optimization for multi-objective MaxCut. arXiv:2608.25098.
5. S. Riedmüller, T. Koch. GPU parallel Pareto local search for multi-objective QUBO. arXiv:2610.21890.
6. J. Könen, H. Röglin, T. Stuck. Parameterized algorithms for computing Pareto sets. arXiv:2509.06124.
7. moocore: core algorithms for multi-objective optimization. https://github.com/multi-objective/moocore
8. A. Ruiz, S. Ghosh, S. Woerner. Binary optimization with complex constraints via quantum approximate multi-objective optimization. arXiv:2609.13790.
