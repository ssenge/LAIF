# Exact block heat bath for fixed-weight Boltzmann sampling on heavy-hex graphs

_18 November 2026_

In [1], quantum-enhanced Markov chain Monte Carlo samples the fixed-weight Boltzmann distribution

π_K(x) ∝ exp(−β E(x)),  E(x) = Σ_{ij ∈ E} Q_ij x_i x_j,  x ∈ {0, 1}^N,  Σ x_i = K = N/2,

with Q_ij ~ N(0, 1) on heavy-hex graphs with N = 144 and N = 1064 and β = 0.5. The graph is split into overlapping blocks of 49 vertices. At each step one block is chosen at random, and a new block configuration with the same block weight is proposed by a neural network trained on QAOA samples from an IBM Heron r2 processor. Mixing is measured by the decay rate τ of the autocorrelation of the normalized Hamming distance between replica pairs, fitted as exp(−τ ℓ) over the lag ℓ in steps. Per step, [1] reports τ about 5.2 and 12.3 times that of global and local Kawasaki dynamics at N = 1064, and 4.71 and 9.95 times at N = 144.

## Result

On the same graphs and blocks, an exact heat bath reaches the following per-step decay-rate ratios. It redraws the chosen block from π_K conditioned on the rest of the state and on the block weight.

| N | Steps | Exact block heat bath, τ ratio to global / local Kawasaki | Proposals of [1], τ ratio to global / local Kawasaki |
|---|---|---|---|
| 1064 | 27 000 | **14.9 / 33.8** (seeds: 13.7 to 17.5 / 25.9 to 38.1) | 5.2 / 12.3 |
| 144 | 3 000 | **18.2 / 40.7** (seeds: 16.3 to 20.6 / 29.0 to 50.4) | 4.71 / 9.95 |

Each entry is the mean over five draws of the couplings. The run uses the setting of [1]: β = 0.5, K = N/2, a uniformly random block per step, 16 replicas started from uniformly random states of weight K, and the mean autocorrelation over eight disjoint replica pairs. The two Kawasaki baselines reproduce the ratio between them in [1]: global over local is 2.2 here, and 2.37 (N = 1064) and 2.11 (N = 144) in [1].

The heat bath is exact because the blocks are thin. A transfer-matrix pass over a vertex order of the block, with a frontier of at most 4 vertices and the number of ones so far, gives the conditional weights of all block configurations of the required weight. A backward pass then draws one configuration from them. The move is accepted with probability 1, and it keeps π_K invariant as a Gibbs update of one block.

Lean (`lean/BlockHeatBath/Basic.lean`, standard axioms only, `lean/axioms.txt`) proves the exactness of the sampling step for any nonnegative weight f on {0, 1}^n with positive total Z. Let M(t, z) be the total weight of the configurations that agree with z on the first t coordinates, and draw the coordinates one after the other with probabilities M(t + 1, z)/M(t, z):

- `M_split`: the two continuations of a prefix sum to it, so every step is a probability distribution.
- `P_eq`: the configuration z is drawn with probability f(z)/Z.
- `sum_P`: these probabilities sum to 1.

The heat bath applies this with f the Boltzmann weight of the block configurations of the required weight, conditioned on the outside, and the coordinates in reverse order. The transfer-matrix pass computes the sums M from frontier states. That compression is not formalized; it is checked against enumeration by `sim/test_mcmc.py`.

To our knowledge, quantum-enhanced Markov chain Monte Carlo with block proposals has not been compared with an exact heat bath on the same blocks before.

## Scope

- **Instances.** The N = 144 graph is recovered exactly: the two-vertex blocks of [1, Table II] are its 164 edges, and it is the heavy-hex subdivision of a 3 × 7 hexagonal patch. Every block family of that table has the stated size, and each 49-vertex block has 54 internal edges. The N = 1064 graph is the 3 × 3 array of copies described in [1], the heavy-hex subdivision of a 9 × 21 patch with 1064 vertices and 1252 edges, with the four blocks repeated in each copy (36 blocks). The couplings of [1] come from a seed that is not given, so the couplings here are fresh N(0, 1) draws, and the comparison is between ratios to Kawasaki dynamics on the same instance.
- **Fit.** The fit window of [1] is not stated. Here exp(−τ ℓ) is fitted by least squares on the lags before the mean autocorrelation first falls below 0.1, with the same rule for every method. With the cut at 0.05 or 0.2, and with a burn-in of one full run length, the ratio to global Kawasaki stays between 15.7 and 18.2 (seed 0, both sizes).
- **Local Kawasaki** picks a uniformly random edge and proposes to swap its two bits if they differ.
- **Cost per step.** One heat-bath step takes about 130 µs on one laptop core at N = 1064, and a Kawasaki step about 0.2 to 0.3 µs. Per second of wall time, global Kawasaki therefore decorrelates faster than the block heat bath, by about 35 times at N = 1064. The cost per step of the proposals of [1] is not reported there.
- **Cluster moves** of the Swendsen-Wang, Wolff or Houdayer type flip sets of spins without keeping the number of ones fixed, so they do not apply to π_K directly and are not included.

## Files

- `sim/blocks.py`: the two graphs and their blocks from `data/table2_blocks.json` (the vertex sets of [1, Table II]), with asserts on the stated sizes and edge counts.
- `sim/mcmc.py`: global and local Kawasaki dynamics, a two-vertex heat bath, the exact block heat bath, the replica-pair autocorrelation and the fit.
- `sim/test_mcmc.py`: a chi-square test of the block heat bath against exact enumeration on a 12-vertex block (200 000 draws), and checks that the weight and the outside of the block are kept.
- `sim/robust.py`: the fit-window and burn-in check.
- `lean/`: the Lean files. Build with `lake exe cache get` and then `lake build`; `lake env lean Axioms.lean` prints the axioms.
- `data/`: the outputs (`n144.txt`, `n1064.txt`, `robust144.txt`, `robust1064.txt`).

## References

1. Y. Kawamata, K. Fujii. Hardware demonstration of neural-surrogated quantum-enhanced MCMC for large-scale constrained Boltzmann sampling. arXiv:2611.05883.
