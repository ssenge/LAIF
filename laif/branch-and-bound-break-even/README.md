# Quantum branch and bound on the QOBLIB library: break-even logical clock rates

_22 November 2026_

Quantum tree search speeds up classical branch and bound by close to a square root of the tree size [1, 2]. Whether this pays on real instances depends on how large the trees of a modern solver are, how long a node takes on each side, and how fast an error-corrected machine runs. This folder measures the branch-and-bound trees of SCIP on instances of the QOBLIB benchmark library [3] and computes the logical clock rate at which the quantum search would only match the faster of two classical solvers.

## Result

Break-even logical clock rates of 7.1 · 10⁷ to 1.6 · 10¹¹ layers of non-stabilizer gates per second on 17 instances from four QOBLIB classes, against a classical run on one laptop core. A surface-code machine with code distance 30 and a 1 µs cycle runs about one doubly controlled NOT (CCZ-type) gate, CCZ below, per 170 µs per factory, about 5.9 · 10³ per second [4, Eq. (6)], and parallel factories gain a factor of 10 to 100 [4]. The lowest break-even rate lies more than four orders of magnitude above one factory and more than a hundred times above a hundred factories.

| Class | Instance | Variables | SCIP nodes T | Depth d | Classical time, solver | LP iterations per node | Break-even rate (Hz) | Best hybrid rate (Hz) |
|---|---|---|---|---|---|---|---|---|
| marketsplit | ms_03_050_005 | 23 | 86 | 13 | 23 ms, CP-SAT | 3 | **3.1 · 10⁸** | no gain |
| marketsplit | ms_03_050_009 | 23 | 722 | 15 | 27 ms, CP-SAT | 2 | **5.0 · 10⁸** | no gain |
| marketsplit | ms_03_050_007 | 23 | 1 476 | 16 | 30 ms, CP-SAT | 2 | **7.3 · 10⁸** | 7.1 · 10⁸ (10 QPUs) |
| marketsplit | ms_03_050_002 | 23 | 3 297 | 16 | 29 ms, CP-SAT | 2 | **8.4 · 10⁸** | no gain |
| marketsplit | ms_03_100_001 | 23 | 3 429 | 16 | 56 ms, CP-SAT | 1 | **3.8 · 10⁸** | 1.1 · 10⁸ (47 QPUs) |
| marketsplit | ms_03_100_012 | 23 | 3 464 | 17 | 36 ms, CP-SAT | 2 | **7.2 · 10⁸** | 5.4 · 10⁸ (48 QPUs) |
| independentset | brock200-1 | 200 | 37+ | 20 | 8.3 s, CP-SAT | 1155 | **2.4 · 10⁸** | no gain |
| independentset | C125-9 | 125 | 1 099 | 28 | 3.7 s, SCIP | 43 | **1.2 · 10⁸** | 6.6 · 10⁷ (62 QPUs) |
| network | network05 | 101 | 171 | 10 | 28 ms, CP-SAT | 12 | **1.0 · 10⁹** | 1.0 · 10⁹ (4 QPUs) |
| network | network06 | 181 | 1 175 | 18 | 429 ms, CP-SAT | 16 | **3.5 · 10⁸** | 1.2 · 10⁸ (107 QPUs) |
| network | network07 | 295 | 11 430 | 27 | 11.9 s, SCIP | 24 | **7.1 · 10⁷** | 7.7 · 10⁶ (721 QPUs) |
| topology | topology_15_4 | 1576 | 14 | 6 | 478 ms, CP-SAT | 5596 | **6.8 · 10⁹** | no gain |
| topology | topology_20_4 | 7411 | 12+ | 6 | 566 ms, CP-SAT | 14260 | **1.3 · 10¹⁰** | no gain |
| topology | topology_20_3 | 11021 | 8+ | 5 | 696 ms, CP-SAT | 17363 | **1.0 · 10¹⁰** | no gain |
| topology | topology_25_6 | 7501 | 33+ | 17 | 800 ms, CP-SAT | 6184 | **1.1 · 10¹⁰** | no gain |
| topology | topology_15_3 | 3046 | 151 | 37 | 52 ms, CP-SAT | 1768 | **1.6 · 10¹¹** | no gain |
| topology | topology_20_5 | 3801 | 244+ | 33 | 163 ms, CP-SAT | 1936 | **6.8 · 10¹⁰** | no gain |

T+ marks a tree that SCIP had not finished within 60 s while CP-SAT solved the instance. The recorded nodes are then a part of the full tree, so the rate shown is a lower bound on the break-even rate for that tree. Rates are rounded down. "Best hybrid" is the lowest rate over the hybrid schemes below; "no gain" means that none of them is lower than the plain rate.

The rate falls with the tree size, roughly as 1/√T at a fixed time per node, because the classical time grows as T and the quantum depth as √T. On network07, the instance with the lowest rate, matching one factory at 5.9 · 10³ Hz with the same per-node costs would take a tree of about 10¹² nodes, which SCIP would need decades to search on one core.

## Cost model

- **Quantum speedup on the tree.** Detection of a marked node in a tree of T nodes and depth at most n by the quantum backtracking walk, with the phase-estimation constants of [2, Sec. 4.1]: b = 1/32 and at most 32√(Tn) sequential walk steps per run. The K = 79 repetitions of [2] are taken to run in parallel and are not counted, n is the measured maximum depth d of the SCIP tree, and the tree searched is the one SCIP explores. Finding an optimum takes at least one such detection, so this is a lower bound on the quantum depth. The incremental variant of [1] has the same leading √T dependence.
- **Gate cost per walk step.** Each step evaluates the node bound twice (compute and uncompute). One evaluation is costed at 10³ layers of non-stabilizer gates per simplex pivot, times the measured LP iterations per node of SCIP, and at least 10³. This is a floor of our own choice, about one 32-bit division and one comparison tree per pivot. It does not count loading the constraint matrix.
- **Gate speed and error correction.** The break-even rate is the rate of layers of non-stabilizer gates per second at which the quantum depth 2 · 32√(Td) · G equals the classical time. Error correction enters only through this rate: the reference point is one CCZ per 30 × 5.5 surface-code cycles of 1 µs at code distance 30 [4, Eq. (6)]. Physical qubit counts, routing and the time to prepare the input are not counted, which all favours the quantum side.
- **Classical side.** The faster of SCIP 10.0 (single thread, default settings) and CP-SAT of OR-Tools 9.15 (one worker), with wall-clock time on one core of an Apple M4 Pro laptop. The tree is that of SCIP in every row.
- **Hybrid schemes.** SCIP solves the top levels down to depth h ∈ {0, 2, ..., 12}, and the quantum walk is applied to each subtree below, either on one QPU in sequence or on one QPU per subtree in parallel.

## Scope

- **Classes measured.** Market split, maximum independent set, network design and topology design (Seidel linear model), with seven to nine instances per class picked by size (`sim/pick.py`). Of these, the instances in the table have a tree and were solved within 60 s by at least one of the two solvers.
- **Classes left out.** Steiner tree packing: all six instances picked were solved at the root node, so there is no tree to search. LABS, Birkhoff, sports timetabling, portfolio and routing were not measured. Larger instances of the measured classes that neither solver finished in 60 s are not in the table (`data/trees.jsonl` keeps their partial trees).
- **Not formalized.** The rates are numerical estimates under the cost model above.

## Files

- `sim/measure.py`: solves one instance with SCIP, records every solved node with its parent and depth, the subtrees below each depth h, and then runs CP-SAT on the same model (`python -I measure.py FILE 60 out.jsonl`).
- `sim/breakeven_bb.py`: the cost model and the table (`python -I breakeven_bb.py data/trees.jsonl data/instances.txt`; `python -I breakeven_bb.py test` checks the formula on a small case).
- `sim/pick.py`: the instance selection from the QOBLIB metrics files.
- `data/instances.txt`: class, variables, constraints and QOBLIB path of each instance; `data/trees.jsonl`: the solver runs; `data/breakeven_bb.jsonl`: the rates.

## References

1. S. Chakrabarti, P. Minssen, R. Yalovetzky, M. Pistoia. Universal quantum speedup for branch-and-bound, branch-and-cut, and tree-search algorithms. arXiv:2210.03210.
2. E. Campbell, A. Khurana, A. Montanaro. Applying quantum algorithms to constraint satisfaction problems. Quantum 3, 167 (2019). arXiv:1810.05582.
3. T. Koch et al. Quantum optimization benchmarking library: the intractable decathlon. Nature Computational Science 6, 653–671 (2026). arXiv:2504.03832.
4. R. Babbush, J. McClean, M. Newman, C. Gidney, S. Boixo, H. Neven. Focus beyond quadratic speedups for error-corrected quantum advantage. PRX Quantum 2, 010103 (2021). arXiv:2011.04149.
