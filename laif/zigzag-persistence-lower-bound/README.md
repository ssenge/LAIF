# Zigzag persistence statistics of temporal graphs: a lower bound for fixed power weights

Written 21 Nov 2026.

**Setting.** As in [1]: graphs G_1, …, G_m on the vertex set [n], given by the bit oracle that answers whether {u, v} is an edge of G_t. For the intersection zigzag G_1 ← G_1 ∩ G_2 → G_2 ← ⋯ → G_m, every bar b of its first homology has a snapshot lifetime ℓ_b ∈ {0, …, m}. For an integer r ≥ 2 the statistic is S_r = Σ_b (ℓ_b/m)^r, normalized degree-r total persistence, with 0 ≤ S_r ≤ B_n = C(n − 1, 2). The task is to output an estimate within εn of S_r with probability at least 2/3, under the promise S_r ≤ K.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Estimating S_r for a fixed r ≥ 2 under the promise S_r ≤ K, lower bound | Õ(√(m(K + n))/ε) for every weight [1]; a matching Ω(√(mK)/ε) when λ·B_n ≤ εn/64 for the central split leakage λ ≤ 2(2/3)^r, so for r ≥ log_{3/2}(128 B_n/(εn)) [1] | Ω(√(K⌊m/s⌋)/ε) for every r ≥ 2 and every integer 1 ≤ s ≤ m with B_n (4/s)^{r−1} ≤ εn/4; in particular Ω((√(mK)/ε) · (ε/(2n))^{1/(2(r−1))}) when m ≥ 10(2n/ε)^{1/(r−1)} | Claim; checked by script |

The ranges are those of [1]: n ≥ 6, 1/n ≤ ε ≤ 1/8 and 256n ≤ K ≤ B_n/8. For fixed r the leakage condition of [1] fails, and [1] asks whether fixed power weights are easier on sparse instances. Theorem 1 shows that the factor √m survives for every fixed r ≥ 2, up to the factor (n/ε)^{1/(2(r−1))}: for r = 2 the bound is Ω(√(mK/n)/√ε) and the gap to the upper bound of [1] is O(√(n/ε)) up to polylogarithmic factors, and the gap shrinks as r grows.

## The instance

As in [1], every snapshot contains the star with centre 1 and leaves 2, …, n, and each of the B_n pairs of leaves is an optional chord. The chord pair e is present in a set of snapshots, its row. Each maximal run of consecutive snapshots in which e is present is one bar whose lifetime is the run length, so S_r is the sum over rows of Σ (u/m)^r over the runs u of the row.

Split [m] into s consecutive blocks whose lengths differ by at most one. A **full row** is present in every snapshot, a bar of lifetime m with contribution 1. A **decoy row** misses exactly one snapshot in each block.

**Lemma 1.** A decoy row contributes at most (4/s)^{r−1}.

*Proof.* Every run lies in two adjacent blocks, so u < 2⌈m/s⌉ ≤ 4m/s for s ≤ m. Hence Σ (u/m)^r ≤ (4/s)^{r−1} Σ u/m ≤ (4/s)^{r−1}. ∎

**Lemma 2.** Let g map the full row to 1 and every decoy row to 0. Then Adv±(g) ≥ √L, where L ≥ ⌊m/s⌋ is the smallest block length.

*Proof.* Relate the full row to every decoy row. The full row has Π_j L_j related rows, and those that differ from it in a position i of block j number Π_{j′≠j} L_{j′}. Every decoy row is related to the full row only. The weighted adversary bound [4] gives √(L_j) ≥ √L, and the general adversary bound is at least this bound [5]. ∎

## Theorem 1, the proof

Take t = ⌊K/2⌋ and Δ = ⌈3εn⌉. All rows are full or decoy, and the number of full rows is exactly t or exactly t + Δ. By Lemma 1 and the condition on s, S_r lies between the number of full rows and that number plus εn/4. Then S_r ≤ t + Δ + εn/4 ≤ K, so the promise holds, and an estimate within εn tells the two cases apart, since Δ > 9εn/4. A query reveals one bit of one row. So estimating S_r computes F = EW_{B_n,t,Δ} ∘ g^{B_n}, where EW_{N,t,Δ} maps inputs of Hamming weight t to 0 and weight t + Δ to 1, and the quantum query complexity is Ω(Adv±(F)) [3, Thm. 1.1].

The composition lemma for partial functions [2, Lemma 6] gives Adv±(F) ≥ Adv±(EW_{B_n,t,Δ}) · Adv±(g). For the exact-weight function, relating every input of weight t to every input of weight t + Δ containing it gives Adv±(EW_{N,t,Δ}) ≥ √((N − t)(t + Δ))/Δ [4, 5]. Here N − t ≥ N/2 and t + Δ ≥ K/2, since K ≤ N/8, and N = B_n ≥ n²/4 for n ≥ 6, so this is at least n√K/(4Δ) ≥ √K/(16ε), using Δ ≤ 4εn for εn ≥ 1. With Lemma 2 the bound is Ω(√(K⌊m/s⌋)/ε).

For the second form take s = ⌈4(2n/ε)^{1/(r−1)}⌉. Then (4/s)^{r−1} ≤ ε/(2n) and B_n ≤ n²/2 give B_n (4/s)^{r−1} ≤ εn/4. With X = (2n/ε)^{1/(r−1)} ≥ 1 we have s ≤ 4X + 1 ≤ 5X, so m ≥ 10X gives m ≥ 2s and ⌊m/s⌋ ≥ m/(2s) ≥ m/(10X). ∎

## Scripts

`sim/check_decoys.py` checks three things. First, on 40 random instances with n ≤ 6, m ≤ 6 and r ∈ {2, 3}, the statistic computed from the random-window identity of [1] (S_r is the mean of β_1 of the intersection graph over all r-tuples of times) equals the run sum used above. Second, for every m ≤ 60, every s ≤ m and r ∈ {2, 3, 4, 6}, random decoy rows satisfy Lemma 1. Third, the semidefinite programme of the general adversary bound confirms Lemma 2 for six small cases.

```
python sim/check_decoys.py
gadget statistic equals the run sum on 40 random instances
decoy run sum <= (4/s)^(r-1) on all tested decoys, largest ratio 0.4452
m=4 s=2: Adv(g)=1.4142 sqrt(min block)=1.4142
m=6 s=2: Adv(g)=1.7321 sqrt(min block)=1.7321
m=6 s=3: Adv(g)=1.4142 sqrt(min block)=1.4142
m=7 s=2: Adv(g)=1.7321 sqrt(min block)=1.7321
m=8 s=2: Adv(g)=2.0000 sqrt(min block)=2.0000
m=8 s=4: Adv(g)=1.4142 sqrt(min block)=1.4142
inner adversary bound checked
```

**Not formalized:** all of the folder.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. C. Xin. Quantum query complexity of persistence statistics in graph zigzags. arXiv:2609.05813, 2026.
2. S. Kimmel. Quantum adversary (upper) bound. Chicago Journal of Theoretical Computer Science, 2013. arXiv:1101.0797.
3. T. Lee, R. Mittal, B. W. Reichardt, R. Špalek, M. Szegedy. Quantum query complexity of state conversion. FOCS 2011. arXiv:1011.3020.
4. A. Ambainis. Quantum lower bounds by quantum arguments. Journal of Computer and System Sciences 64, 2002. arXiv:quant-ph/0002066.
5. P. Høyer, T. Lee, R. Špalek. Negative weights make adversaries stronger. STOC 2007. arXiv:quant-ph/0611054.
