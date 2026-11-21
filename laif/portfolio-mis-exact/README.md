# Exact maximum independent sets of portfolio market graphs

_21 November 2026_

In [1], portfolio diversification is posed as a maximum independent set (MIS) problem on asset correlation graphs: the assets of a market index are the vertices, and two assets are joined when the absolute correlation of their weekly returns exceeds a threshold λ. The data are the five index files of [2], as distributed in [3]. A hybrid algorithm reduces the graph classically by removing exposed corner (simplicial) vertices, and then calls QAOA on a 98-qubit trapped-ion system on the remaining kernel to fix frozen vertices, alternating the two until an MIS is found. On four indices, the optimal time to solution of the hybrid algorithm is 35.6 to 468.7 quantum shots [1, Table III].

## Result

The same graphs, solved exactly on one core: the same corner reduction, then a maximum clique of the complement of the kernel by branch and bound with a greedy-colouring bound. No sampling is involved.

| Index | λ | Assets | Edges | Kernel, here | Kernel [1, Table I] | MIS | Time (ms) | optTTS of [1] (shots) |
|---|---|---|---|---|---|---|---|---|
| DAX 100 | 0.24 | 85 | 1112 | 49, density 0.29 | 49, density 0.29 | **31** | 2.3 | 35.6 |
| FTSE 100 | 0.32 | 89 | 753 | 46, density 0.28 | 45, density 0.28 | **30** | 2.0 | 185.6 |
| S&P 100 | 0.24 | 98 | 903 | 76, density 0.19 | 68, density 0.20 | **30** | 12.0 | 468.7 |
| Nikkei 225 | 0.62 | 225 | 1849 | 58, density 0.15 | 78, density 0.17 | **102** | 14.4 | 88.6 |

The times are wall-clock times of the whole solve (graph, reduction and branch and bound) in plain Python on one core of an Apple M4 Pro laptop. The optimal time to solution of [1] counts quantum shots and does not convert to seconds, so the two columns are in different units.

Over all thresholds λ = 0.05, 0.06, ..., 0.95 and all five index files, including the 31-asset file not used in [1], the largest time is 1.6 s (Nikkei 225 at λ = 0.57, kernel of 163 vertices, MIS 69); for the three files with up to 98 assets it stays below 15 ms.

In [1], the problem is described as computationally challenging at scale, and every instance needs at least one quantum call inside the reduce-and-sample pipeline, since the corner reduction alone does not empty the kernel. An exact branch and bound on the kernel removes that need at these sizes. This hints at a possible gap in reading the four index graphs of [1] as hard instances: each is solved to proven optimality in milliseconds on one core.

## Scope

- **Graphs.** An edge joins i and j when |c_ij| > λ, with the correlations c_ij printed in the files of [3]. For DAX 100 the kernel after corner reduction agrees with [1, Table I] in size and density, and for FTSE 100 it differs by one vertex. For S&P 100 and Nikkei 225 it differs at the printed λ (76 and 58 vertices against 68 and 78). On a grid of λ with step 0.005, no λ gives 68 vertices for S&P 100, and the nearest kernels for Nikkei 225 have 77 vertices (λ = 0.575, density 0.18) and 79 vertices (λ = 0.59); with ≥ instead of >, or signed instead of absolute correlations, the kernels at the printed λ are the same. All of these graphs lie in the threshold scan below. The kernel of repeated corner removal does not depend on the order of removal (checked over 200 random orders). The MIS values for these two indices are exact for the graphs as rebuilt here.
- **Checks.** `python -I psp_mis.py test` compares the exact MIS with an independent maximum-clique search (networkx) on 60 random correlation graphs; the four MIS values above agree with the networkx maximum weight clique of the complement, and each returned set is checked to be independent in the full graph.
- **Not run.** The quantum part of [1] and the 73 emulator instances of [1], which are random subsets of the Nikkei 225 assets with unpublished selection.
- **Not formalized.** The search is a numerical computation.

## Files

- `sim/psp_mis.py`: graph, corner reduction and exact MIS. `python -I psp_mis.py FILE λ` prints one instance, with FILE one of `datasets/assets1.txt` to `assets5.txt` of [3]; `python -I psp_mis.py test` runs the checks.
- `data/hardware_instances.jsonl`: the four instances of the table, with one maximum independent set each.
- `data/lambda_scan.jsonl`: all five files at λ = 0.05 to 0.95.

## References

1. R. Yalovetzky, M. J. A. Schuetz, Z. He, J. Shen, Y. Sun, R. Raymond, S. Sahay, K. Perla, R. S. Andrist, G. Salton, H. G. Katzgraber, R. Bongiovanni, N. Kumar, R. Otter. Quantum-informed portfolio selection: an end-to-end pipeline validated on trapped-ion hardware with real market data. arXiv:2607.01037.
2. T.-J. Chang, N. Meade, J. E. Beasley, Y. M. Sharaiha. Heuristics for cardinality constrained portfolio optimisation. Computers & Operations Research 27, 1271–1293, 2000.
3. A. Knazakis. Portfolio Optimization. https://github.com/AchilleasKn/PortfolioOptimization (data files `datasets/assets1.txt` to `assets5.txt`).
