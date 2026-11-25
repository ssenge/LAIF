# Quantum k-tuple sieving with nested search and product codes

Written 25 Nov 2026.

Heuristic sieving algorithms for the Shortest Vector Problem in dimension d keep a list of 2^{md} lattice vectors and combine k of them at a time into shorter ones. The time of one sieving step is 2^{td}, and larger k trades time for memory. For k = 3, a quantum algorithm of [1] reaches t = 0.2846 at the minimal 3-tuple memory m = 0.1887. It nests amplitude amplification in the form of two-oracle search and restricts each search to the bucket of a random product code. In [1, Section 1.3] it is asked whether these techniques improve 4-tuple sieving. Quantum 3- and 4-sieves with a tailored filtering step before the search, and their trade-offs between time and memory, are given in [3], with concrete circuits and re-optimized parameters in [4].

Here the method of [1] is carried to k − 1 nested levels, one random product code per level, with free inner products in the configuration of the k-tuple.

**Theorem 1 (heuristic).** In the model of [1] (classical memory readable in superposition, 2^{o(d)} qubits), under the heuristics of [1, Section 4]:

1. 4-tuple sieving runs in time 2^{0.304495d + o(d)} with the minimal 4-tuple memory 2^{0.172369d + o(d)}. This concerns k = 4; with larger k, less time is possible at this memory (part 2 and [2, Table 2]).
2. For every memory exponent m in [0.1625, 0.1887), k-tuple sieving with some k ∈ {4, 5, 6} runs in time 2^{t(m)d + o(d)}, where t(m) is the entry of the table of Section 3 at the largest listed memory not above m. In particular t(m) < 0.2989 on this range.

Status: Claim. The cost formula is evaluated and optimized by script, and the script reproduces the exponent 0.284551 of [1]; its derivation is the written argument of Sections 1 and 2.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| Quantum 4-tuple sieving at the minimal memory 0.1724 | time 0.3178 [2, Table 3] | time 0.3045 |
| Quantum sieving with memory 2^{md}, m ∈ [0.1625, 0.1875] | time 0.2989, from the k-sieve at memory 0.1395 [2, Table 2] | t(m) from 0.2982 (m = 0.1625) to 0.2873 (m = 0.1846) |

## 1. The algorithm

A k-tuple solution is built along a chain: x₁; then x₂ with ⟨x₁, x₂⟩ ≈ cos t₁; then, for i ≥ 2, x_{i+1} with ⟨s_i/‖s_i‖, x_{i+1}⟩ ≈ cos t_i, where s_{i+1} = s_i − x_{i+1}, up to ‖s_k‖ ≤ 1. With list size 2^{md}, the expected number of chains is 2^{(km + Σ_i log₂ sin t_i)d}, and the memory is the smallest m with at least 2^{md} solutions, m = −Σ_i log₂ sin t_i/(k − 1).

Each level i has its own random product code C_i, whose centres lie at angle a_i from the vectors they hold, and a table of the list sorted by centre in classical memory readable in superposition, as in [1, Section 3.3]. A chain is found in one repetition when consecutive elements share a centre at every level, which happens with probability Π_i W(a_i, a_i | t_i)/p(a_i) for independent codes, with p and W the cap and wedge volumes of [1, Lemmas 2.7, 2.8]. The search is nested two-oracle search [1, Section 2.3.3]: the outer level looks for pairs (x₁, x₂) that share a centre, its check looks for x₃ in the bucket of s₂/‖s₂‖, and so on, with Grover search over the last bucket.

## 2. Cost

All quantities below are log₂(·)/d. With ℓ = Σ_i (p(a_i) − W(a_i, a_i | t_i)) repetitions, S = m − ℓ ≥ 0 solutions per repetition, T₀ = 2m + p(a₁) pairs in shared buckets and T₁ = 2m + W(t₁, a₁ | a₁) of them at the right angle, the time is

max(ℓ + m, ℓ + S + max(T₀ − S, T₁ − S + 2c₂)/2),

where c_i is the cost of completing a prefix at level i: c_{k−1} = (m + p(a_{k−1}))/2 for the last bucket, and c_i = max(0, m + W(t_i, a_i | a_i))/2 + max(m + p(a_i), 2c_{i+1})/2 for the levels in between: an amplification over the bucket with the angle test, nested in an amplification over the vectors at the right angle with the next check. The formula is used when a prefix has at most one completion in expectation, which holds at every configuration reported here; the scripts reject other configurations. For k = 3 this is equation (4) of [1].

At the minimal 4-tuple memory, cos tᵢ = (1/4, 1/√6, √(3/8)) and the optimal cos aᵢ = (0.232941, 0.421080, 0.421080) give ℓ = 0.132126, S = 0.040243, buckets of 2^{0.1321d}, 2^{0.0316d} and 2^{0.0316d} vectors, and equal preprocessing and search costs of 0.304495.

## 3. Trade-off

| Memory m | Best k | Time t(m) |
|---|---|---|
| 0.1625 | 6 | 0.298236 |
| 0.1650 | 6 | 0.296795 |
| 0.1675 | 6 | 0.295680 |
| 0.1700 | 5 | 0.294306 |
| 0.1725 | 5 | 0.292926 |
| 0.1750 | 5 | 0.292104 |
| 0.1775 | 4 | 0.289559 |
| 0.1800 | 4 | 0.288084 |
| 0.1825 | 4 | 0.287445 |
| 0.1846 | 4 | 0.287305 |
| 0.1900 | 3 | 0.280649 |
| 0.1925 | 3 | 0.279693 |
| 0.1929 | 3 | 0.279680 |

Each entry is a configuration found by numerical optimization with three starting points, which agree to six decimals; its time is an upper bound for that memory. The entries for k = 3 are the algorithm of [1] with other inner products in the configuration, which [1, Lemma 3.16] covers; they are implied by [1] and listed for comparison.

## 4. Measurements

- [`sim/k3_reproduce.py`](sim/k3_reproduce.py): the cost formula with the angles of [1, proof of Theorem 3.1] gives 0.284551, and optimizing the angles returns the same point.
- [`sim/k4_chain.py`](sim/k4_chain.py): the cost for general k; for k = 4 at the minimal memory it checks the chain count m⁴ p(t₁)p(t₂)p(t₃) = m and finds 0.304495.
- [`sim/k4_explicit.py`](sim/k4_explicit.py): the closed form of Section 2 for k = 4, which agrees with the recursive one, with the count of chains per repetition equal to S.
- [`sim/k_general.py`](sim/k_general.py) and [`sim/curve.py`](sim/curve.py): free chain angles and the table of Section 3, written to `curve.csv`.
- [`sim/envelope.py`](sim/envelope.py): compares the table with the lower envelope of the quantum points of [2, Tables 2, 3 and Figure 1], [1] and [3, Tables 4, 5], [4, Table 2], and of the quantum 2-sieves at memory 0.2075, extended to larger memory, with the k = 3 entries counted as known; the entries for k ≥ 4 lie below it for every memory bound from 0.1625 to 0.1875.

Run each with `python <script>` in `sim/` (SciPy needed).

## 5. Limits

- The bounds are heuristic, under the assumptions of [1, Section 4] on the list vectors, and hold up to 2^{o(d)} factors.
- The argument of [1, Lemma 3.16] is carried to more levels, where the expected number of good vectors in a bucket per prefix is at most one; only upper bounds on these counts enter.
- Memory is classical memory readable in superposition, with unit cost per access, as for all the exponents compared here. With an access cost that grows with the list size, the exponents change, see [4, Section 3.4].
- The exponents of the table come from numerical optimization and are not claimed optimal.
- Not formalized in Lean.

## References

1. L. Engelberts, Y. Chen, A. S. Gilani, M.-I. van Hoof, S. Jeffery, R. de Wolf. An improved quantum algorithm for 3-tuple lattice sieving. arXiv:2510.08473.
2. E. Kirshanova, E. Mårtensson, E. W. Postlethwaite, S. Roy Moulik. Quantum algorithms for the approximate k-list problem and their application to lattice sieving. ASIACRYPT 2019, IACR ePrint 2019/1016.
3. A. Chailloux, J. Loyer. Classical and quantum 3 and 4-sieves to solve SVP with low memory. PQCrypto 2023, IACR ePrint 2023/200.
4. M. Khajeian. Concrete quantum circuit implementations and resource estimates for the quantum 3 and 4-sieves. IACR ePrint 2026/2895.

## Use of AI

The algorithm, the analysis, the scripts and this text were produced with the help of Claude Opus 5.5.
