# Quantum associative retrieval: cost from its own formulas and a classical baseline

2026-11-22

## Problem

Given p stored binary patterns of n bits and a query x, associative retrieval returns a stored pattern at the least bit distance d(x, p_k), the number of differing bits. In [1] a quantum algorithm is analysed that rotates a superposition of the stored patterns b times by angles depending on the distance and then applies amplitude amplification. The abstract of [1] states:

> "We show that efficient and high-precision quantum associative retrieval is possible with an exponential complexity advantage with respect to the classical brute force approach and with a polynomial capacity advantage with respect to classical neural network implementations for any number of patterns scaling polynomially in the number of qubits."

The resource measure of [1] is: "complexity refers to the number of sequential operations or repetitions required for one retrieval as a function of n, assuming that the pattern-dependent memory hardware has already been constructed. Thus a single traversal of a fixed photonic device is O(1) in this resource measure; its physical size and construction cost are outside the scope of the present analysis." The brute force baseline is O(pn) [1]. In the circuit model the memory state costs O(np) gates [1].

The cost formulas of [1] are:
- the good-subspace probability P_good = (1/p) Σ_k cos^{2b}(π d_k/(2n)) [1, eqs. (13), (14)];
- 1/√P_good repetitions of an oracle with O(b) steps on n qubits, so a typical cost C_ret = O(nb) 2^{b/2} [1, eq. (17)];
- the precision condition p 2^{−b} ≪ 1 for p = n^k [1, eq. (32)];
- for b = B log n, high precision together with an advantage over brute force for B/2 < k < B [1, eq. (34)].

| | cost of one retrieval, p = n^k patterns, success probability 1 − η |
|---|---|
| Brute force [1] | O(pn) |
| Stated in [1, abstract] | exponential advantage over O(pn) |
| Lemma 1, from the formulas of [1] | at least n b √((1 − η)p) sequential steps |
| Lemma 2, same resource measure | static classical circuit of size O(pn), depth O(log n · log p) |

## Results

**Lemma 1.** Suppose the query equals one stored pattern and the algorithm of [1] returns that pattern with probability at least 1 − η after the good outcome. Then 1/√P_good ≥ √((1 − η)p). So the sequential cost of [1, eqs. (14), (17)] is at least n b √((1 − η)p), and the gain over the brute force cost pn is at most √(p/(1 − η))/b. For p = n^k this is a polynomial factor, at most of order n^{k/2}.

**Lemma 2.** Under the same convention, where pattern-dependent hardware is built in advance and only sequential steps count, a static classical circuit of size O(pn) returns a stored pattern at the least bit distance, for every query and with certainty. It does so in depth O(log n · log p): p distance counters in parallel, then a tree of pairwise minima.

**Total gate count.** Each repetition of amplitude amplification contains a reflection about the memory state. In the circuit model that state costs O(np) gates [1], so the total gate count is at least √((1 − η)p) · np, above the brute force O(pn).

So, under the resource measure of [1], the gain over brute force is at most quadratic in p, and polynomial in n for p = n^k. A classical circuit with pattern-dependent hardware of the same order, O(pn), is faster still. This hints at a possible gap in the exponential advantage stated in the abstract of [1]. That statement would hold relative to the number 2^n of all possible strings, as the parenthesis "square root speed-up when measured with respect to the total number of possible states" in [1] suggests, but the abstract compares with brute force over the p stored patterns. The size of the photonic device of [1] is not quantified there. A comparison of hardware has to set it against the O(pn) of the classical circuit.

## Proof

**Lemma 1.** Let w_k = cos^{2b}(π d_k/(2n)), with w_target = 1 since d_target = 0. Then P_good = (1/p) Σ_k w_k, and the target is returned with probability w_target / Σ_k w_k = 1/(p P_good). This is at least 1 − η exactly when p P_good ≤ 1/(1 − η), that is, 1/√P_good ≥ √((1 − η)p). Each repetition calls the oracle, which has O(b) steps on n qubits [1, eq. (17)], so the sequential cost is at least of order n b √((1 − η)p).

**Lemma 2.** For every pattern k, compute the n bits x_j ⊕ p_{kj} in parallel and add them in a tree of depth ⌈log₂(n + 1)⌉. Then take the minimum of the p counts in a tree of ⌈log₂ p⌉ levels, each a comparison of ⌈log₂(n + 1)⌉-bit numbers. The comparison costs depth O(log n), and the number of gates is O(pn).

## Check

`sim/cost.py`, output in `sim/out_cost.txt`:

- **Lemma 1:** the identity p P_good · (success probability) = 1 and the bound, on 2000 random instances (n ≤ 40, p ≤ 300, b ≤ 60).
- **Typical case:** for p = n^k (k = 1, 2, 3; n = 16 to 1024) with i.i.d. uniform pattern bits, the least b with expected distractor mass at most η/(1 − η) = 1/9 (exact binomial sum), and then the cost n b/√P_good from the formulas of [1].
  - The gain over pn stays below √p, for example 42 against √p = 1024 at n = 1024, k = 2.
  - The total gate count with O(np) per reflection is above pn.
- **Lemma 2:** the classical circuit, run on 300 random instances, returns a pattern of least bit distance.

## Scope

- Lemma 1 uses the cost formulas of [1] as stated, with the benchmark case of [1] in which one stored pattern equals the query. It bounds the algorithm of [1], not every quantum algorithm.
- The capacity statements of [1] and the photonic implementation are not addressed here.
- The statements are Claims with the listed checks.

## References

1. C. A. Trugenberger. Complexity and precision in quantum associative retrieval. arXiv:2611.21941 (2026).

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
