# Research results

Results on open problems in algorithms and complexity. Each folder holds one topic with its proofs, Lean files and scripts.

## Results

"Lean" means that the theorem is machine-checked in Lean 4 with Mathlib, using only the standard axioms. "Assuming" names a classical theorem that the Lean statement takes as an explicit hypothesis. Each folder states exactly what is checked and what is not.

| Category | Problem | Before | After | Scope | Status | Details |
|---|---|---|---|---|---|---|
| Quantum query complexity | Exact minimum degree with quantum cut queries | O(√n) by quantum minimum finding [1]; no lower bound, Ω(√n) conjectured for simple graphs [1] | Ω(√n), so Θ(√n) | Integer weights of O(n² log n) bits. Simple graphs stay open | Lower bound: Lean, assuming the approximate degree of AND. O(√n): cited | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Quantum query complexity | Global minimum cut value with quantum cut queries | No Ω(√n) lower bound known to us | Ω(√n) | Same weights | Lean, assuming the approximate degree of AND | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Quantum query complexity | Promise decision problem on degrees mod M, modular model | No lower bound known to us | Ω(√n) | Weights in Z_M, oracle returns the cut mod M, M = 2^k ≥ 4. Nothing follows for integer oracles | Lean, assuming the approximate degree of AND | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Lattice lemma | Sparsity of near-solutions of the cut relations | Not available | At most 2R + 3 vertices with a visible degree shift, for R query terms | General tool for the bounds above | Lean | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Classical query complexity | Exact minimum degree with randomized cut queries, large weights | O(n) by singleton queries; Ω(n/log n) from the simple-graph row below | At least n/7 − 2, so Θ(n) | Integer weights of O(n log n) bits and above | Lean | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Classical query complexity | Exact minimum degree with randomized cut queries, simple graphs | O(n) by singleton queries; no lower bound stated in the sources known to us | Ω(n/log n) | Simple graphs | Lean, assuming the communication complexity of disjointness | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Quantum-classical separation | Exact minimum degree with cut queries | O(√n) quantum and O(n) classical upper bounds, without matching lower bounds | Θ(√n) quantum against Θ(n) classical | Integer weights of O(n² log n) bits | Both lower bounds: Lean, as above. O(√n): cited | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |

## References

1. S. Apers, Y. Efron, P. Gawrychowski, T. Lee, S. Mukhopadhyay, D. Nanongkai. Cut query algorithms with star contraction. FOCS 2022. arXiv:2201.05674.

## License

Copyright 2026 Sebastian Senge. Apache License 2.0; see [`LICENSE`](LICENSE).

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
