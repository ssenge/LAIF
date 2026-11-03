# Research results

Results on open problems in algorithms and complexity. Each folder holds one topic with its proofs, Lean files and scripts.

## Results

"Proved" means proved on paper. "Lean" means that the named steps are machine-checked in Lean 4 with Mathlib. No theorem in the table is checked in Lean as a whole, and each folder states exactly what is.

| Category | Result | Scope | Status | Details |
|---|---|---|---|---|
| Quantum query complexity | Ω(√n) quantum cut queries for exact minimum degree, tight against quantum minimum finding | Integer weights of O(n² log n) bits. The simple-graph conjecture of [1] stays open | Proved. Lean: core steps | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Quantum query complexity | Ω(√n) quantum cut queries for the global minimum cut value | Same weights | Proved (corollary) | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Quantum query complexity | Ω(√n) quantum cut queries for exact minimum degree in the modular model | Weights in Z_M, oracle returns the cut mod M, M = 2^k ≥ 4 | Proved | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Lattice lemma | Sparsity lemma for near-solutions of the cut relations | General tool for the bounds above | Proved. Lean: the exact 2-group case | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Classical query complexity | At least n/5 − 2 randomized cut queries for exact minimum degree, tight up to a constant | Integer weights of O(n log n) bits | Proved. Lean: core steps | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Classical query complexity | Ω(n/log n) randomized cut queries for exact minimum degree, by reduction from set disjointness | Simple graphs | Proved, using the cited disjointness bound | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |
| Quantum-classical separation | Θ(√n) quantum against Θ(n) classical cut queries for exact minimum degree | Integer weights of O(n² log n) bits | Proved (from the results above) | [minimum-degree-cut-queries](minimum-degree-cut-queries/) |

## References

1. S. Apers, Y. Efron, P. Gawrychowski, T. Lee, S. Mukhopadhyay, D. Nanongkai. Cut query algorithms with star contraction. FOCS 2022. arXiv:2201.05674.

## License

Copyright 2026 Sebastian Senge. Apache License 2.0; see [`LICENSE`](LICENSE).

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text. No person has reviewed the proofs.
