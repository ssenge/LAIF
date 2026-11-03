# Research results

Results on open problems in algorithms and complexity. Each folder holds one topic with its proofs, Lean files and scripts.

## Results

"Proved" means proved on paper. "Lean" means that the named steps are machine-checked in Lean 4 with Mathlib. No theorem in the table is checked in Lean as a whole, and each folder states exactly what is.

| Category | Problem | Before | After | Scope | Status | Details |
|---|---|---|---|---|---|---|
| Quantum query complexity | Exact minimum degree with quantum cut queries | O(√n) by quantum minimum finding [1]; no lower bound, Ω(√n) conjectured for simple graphs [1] | Ω(√n), so Θ(√n) | Integer weights of O(n² log n) bits. Simple graphs stay open | Proved. Lean: core steps | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Quantum query complexity | Global minimum cut value with quantum cut queries | No Ω(√n) lower bound known to us | Ω(√n) | Same weights | Proved (corollary) | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Quantum query complexity | Exact minimum degree, modular model | No lower bound known to us | Ω(√n) | Weights in Z_M, oracle returns the cut mod M, M = 2^k ≥ 4 | Proved | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Lattice lemma | Sparsity of near-solutions of the cut relations | Not available | At most 1 + (3/2)(R + 1) vertices with a visible degree shift, for R query terms | General tool for the bounds above | Proved. Lean: the exact 2-group case | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Classical query complexity | Exact minimum degree with randomized cut queries, large weights | O(n) by singleton queries; Ω(n/log n) from the simple-graph row below | At least n/5 − 2, so Θ(n) | Integer weights of O(n log n) bits | Proved. Lean: core steps | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Classical query complexity | Exact minimum degree with randomized cut queries, simple graphs | O(n) by singleton queries; no lower bound stated in the sources known to us | Ω(n/log n) | Simple graphs | Proved, using the cited disjointness bound | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Quantum-classical separation | Exact minimum degree with cut queries | O(√n) quantum and O(n) classical upper bounds, without matching lower bounds | Θ(√n) quantum against Θ(n) classical | Integer weights of O(n² log n) bits | Proved (from the results above) | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |

## References

1. S. Apers, Y. Efron, P. Gawrychowski, T. Lee, S. Mukhopadhyay, D. Nanongkai. Cut query algorithms with star contraction. FOCS 2022. arXiv:2201.05674.

## License

Copyright 2026 Sebastian Senge. Apache License 2.0; see [`LICENSE`](LICENSE).

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text. No person has reviewed the proofs.
