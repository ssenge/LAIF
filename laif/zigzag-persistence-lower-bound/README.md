# Zigzag persistence statistics of temporal graphs: lower bounds for fixed power weights

Written 21 Nov 2026.

**Setting.** As in [1]: graphs G_1, …, G_m on the vertex set [n], given by the bit oracle that answers whether {u, v} is an edge of G_t. For the intersection zigzag G_1 ← G_1 ∩ G_2 → G_2 ← ⋯ → G_m, every bar b of its first homology has a snapshot lifetime ℓ_b ∈ {0, …, m}. For an integer r ≥ 2 the statistic is S_r = Σ_b (ℓ_b/m)^r, normalized degree-r total persistence, with 0 ≤ S_r ≤ B_n = C(n − 1, 2). The task is to output an estimate within εn of S_r with probability at least 2/3, under the promise S_r ≤ K.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Estimating S_r for a fixed r ≥ 2 under the promise S_r ≤ K, lower bound | Ω(K√m/(εn)) for every r ≥ 2, implied by [1]; Ω(√(mK)/ε) when λ·B_n ≤ εn/64 for the central split leakage λ ≤ 2(2/3)^r, so for r ≥ log_{3/2}(128 B_n/(εn)) [1]; upper bound Õ(√(m(K + n))/ε) for every weight [1] | Ω(√(K⌊m/s⌋)/ε) for every integer 1 ≤ s ≤ m with B_n (4/s)^{r−1} ≤ K/2; in particular Ω((√(mK)/ε) · (K/n²)^{1/(2(r−1))}) when m ≥ 10(2B_n/K)^{1/(r−1)} | Claim; checked by script |

Theorem 1 assumes n ≥ 6, 1/n ≤ ε ≤ 1/8 and 256n ≤ K ≤ B_n/8, the range of K and ε in [1, Thm. 6.2]. The bound implied by [1] comes from the construction in the proof of [1, Thm. 6.2] with only about K optional rows. For r = 2 Theorem 1 gives the same order K√m/(εn). For r ≥ 3 it is larger by the factor (n²/K)^{(r−2)/(2(r−1))}, and it is within (n²/K)^{1/(2(r−1))} of the upper bound of [1], up to polylogarithmic factors. So on sparse instances the gap between the two bounds shrinks as r grows, and it closes, up to a constant and polylogarithmic factors, once r reaches log(n²/K); [1] asks whether fixed power weights are easier on sparse instances.

## The instance

As in [1], every snapshot contains the star with centre 1 and leaves 2, …, n, and each of the B_n pairs of leaves is an optional chord. The chord pair e is present in a set of snapshots, its row. Each maximal run of consecutive snapshots in which e is present is one bar whose lifetime is the run length, so S_r is the sum over rows of Σ (u/m)^r over the runs u of the row.

Split [m] into s consecutive blocks whose lengths differ by at most one, and let L ≥ ⌊m/s⌋ be the smallest block length. A **full row** is present in every snapshot, a bar of lifetime m with contribution 1. A **decoy row** misses exactly one snapshot in each block. For s = 1 this is close to the rows with one central zero used in [1].

**Lemma 1.** A decoy row contributes at most λ_s = (4/s)^{r−1}.

*Proof.* Every run lies in two adjacent blocks, so u < 2⌈m/s⌉ ≤ 4m/s for s ≤ m. Hence Σ (u/m)^r ≤ (4/s)^{r−1} Σ u/m ≤ (4/s)^{r−1}. ∎

## Theorem 1, the proof

The argument is the one in the proof of [1, Thm. 6.2], with decoy rows in place of rows with one central zero. Every row of an input is full or a decoy. Let N = B_n, b = ⌊K/2⌋, d = ⌊4εn⌋ + 1 and a = b − d ≥ 0. Let X contain the inputs with exactly a full rows and Y those with exactly b full rows. Relate x ∈ X to y ∈ Y when y arises from x by filling every missing snapshot of exactly d decoy rows.

*Promise and separation.* By the condition on s and Lemma 1, every input has S_r at most b + Nλ_s ≤ K/2 + K/2 = K. A related pair differs only in the d filled rows, each of which gains at least 1 − λ_s ≥ 15/16, as λ_s ≤ K/(2N) ≤ 1/16. So S_r(y) − S_r(x) ≥ 15d/16 > 2εn, and the sets of correct outputs for x and y are disjoint.

*Degrees.* Every x has C(N − a, d) related inputs, and every y has C(b, d) P^d, where P is the product of the block lengths. For a position (e, i): if it is a missing snapshot of a decoy row of x, then C(N − a − 1, d − 1) related y differ there, and otherwise none. If row e of y is full and i lies in a block of length L_j, then C(b − 1, d − 1) P^d / L_j related x differ there, and otherwise none. The adversary bound for real-valued outputs with pairwise disjoint correct sets [1, Prop. C.1], a form of the relational adversary bound [2], gives

Q ≥ Ω(√((N − a) b L)/d).

*Arithmetic.* Here N − a ≥ N/2 ≥ n²/8 for n ≥ 6, b ≥ K/4 and d ≤ 4εn + 1 ≤ 5εn, so the bound is at least √(KL)/(29ε), which is Ω(√(K⌊m/s⌋)/ε).

For the second form put Y = (2N/K)^{1/(r−1)} ≥ 1 and s = ⌈4Y⌉. Then (4/s)^{r−1} ≤ K/(2N) and s ≤ 5Y, so m ≥ 10Y gives m ≥ 2s and ⌊m/s⌋ ≥ m/(10Y). With 2N ≤ n² the bound becomes Ω((√(mK)/ε)(K/n²)^{1/(2(r−1))}). ∎

## Scripts

`sim/check_decoys.py` checks four things.

* On 40 random instances with n ≤ 6, m ≤ 6 and r ∈ {2, 3}, it computes the statistic from the random-window identity of [1] (S_r is the mean of β_1 of the intersection graph over all r-tuples of times) and compares it with the run sum used above.
* For every m ≤ 60, every s ≤ m and r ∈ {2, 3, 4, 6}, random decoy rows satisfy Lemma 1.
* On four tiny instances, it computes the relation degrees of the proof by brute force.
* On 180 parameter cases with n up to 10^6, it checks the promise, the separation and the final constant, in exact arithmetic where it matters.

```
python sim/check_decoys.py
gadget statistic equals the run sum on 40 random instances
decoy run sum <= (4/s)^(r-1) on all tested decoys, largest ratio 0.4452
relation degrees of Theorem 1 checked
constants of Theorem 1 checked on 180 parameter cases
```

**Not formalized:** all of the folder.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. C. Xin. Quantum query complexity of persistence statistics in graph zigzags. arXiv:2609.05813, 2026.
2. A. Ambainis. Quantum lower bounds by quantum arguments. Journal of Computer and System Sciences 64, 2002. arXiv:quant-ph/0002066.
