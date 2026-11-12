# Quantum queries for the largest rectangle in a histogram

Written 12 Nov 2026.

**Setting.** A histogram is given by heights h_0, …, h_{n−1} ≥ 0, and a query returns one height. The task is the largest area of a rectangle under the histogram,

OPT = max over intervals [l, r] of (r − l + 1) · min{h_l, …, h_r},

together with an interval that attains it. Classically this takes Θ(n) queries and O(n) time with a stack. Write H for the number of distinct heights. The algorithms below need no knowledge of H or of the heights.

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | OPT exactly, H distinct heights | O(n) queries | O(√(nH) log n) queries | Claim; Lean for the combinatorial lemmas |
| Cor 2 | OPT exactly, heights in a known set of H values | O(n) queries | O(√(nH)) queries | Claim |
| Thm 3 | OPT exactly, V valleys | O(n) queries | O(√(nV) log n + √n log² n) queries | Claim; Lean for the weak records |
| Thm 4 | OPT within a factor 1 + ε | O(n) queries | O(√(n log n / ε)) queries | Claim; Lean for the threshold grid |
| | Lower bound, any factor, H = 2 | | Ω(√n) queries | Claim |

So a constant number of distinct heights, a constant number of valleys (for example sorted heights), or a constant approximation factor gives Θ̃(√n). A *valley* is a maximal run of equal heights whose two neighbours are both higher, where a missing neighbour counts as higher.

## 1. Records

Fix a position p. A *left record* of p is a position j ≤ p whose height is below all heights in (j, p], and a *right record* is defined in the same way to the right; p itself is a record on both sides. Moving outward from p, the records are the positions where the running minimum drops, so their heights strictly decrease and they number at most H on each side, p included.

**Lemma 1.**
(a) Every interval [l, r] through p has a lowest position that is a left or a right record of p.
(b) For a height v ≤ h_p, the first position left of p with height below v is a left record, and in the same way on the right.

*Proof.* (a) Among the lowest positions of [l, p], the one closest to p is a left record, and among those of [p, r] the one closest to p is a right record. The lower of the two is lowest on [l, r]. (b) All heights strictly between that position and p are at least v, which is larger than its height. ∎

So the best rectangle through p within a window [lo, hi] ∋ p follows from the records of p in the window. For each record height v, the run of heights at least v through p ends, on each side, just before the first record below v or at the end of the window, and its area is v times its length. The largest of these areas is the best rectangle through p in the window: by (a) the height of every interval through p is a record height v, and the interval lies in the run of v.

## 2. The exact algorithm

**Lemma 2.** Let w ≥ 1. Every interval of length in [w, 2w) contains a multiple p of w and lies in the window [p − 2w + 1, p + 2w − 1].

*Proof.* Any w consecutive positions contain a multiple of w, and the interval reaches less than 2w − 1 positions beyond p on each side. ∎

**Theorem 1.** OPT, and an interval that attains it, can be computed with O(√(nH) log n) quantum queries and bounded error.

*Proof.* For each scale w = 2^a ≤ n and each multiple p of w, let f(p, w) be the best rectangle through p within the window of Lemma 2, clipped to [0, n − 1]. By Lemma 2, OPT is the largest f(p, w) over all scales and multiples.

The records of p in the window are found one after the other, each as the first position beyond the last record whose height is below it. A search for the first such position at distance g costs O(√g) queries [2, Theorem 6], and the composition theorem for algorithms with input-dependent query complexity [2, Theorem 3] bounds the whole sequence by O(Σ √g_i) with bounded error. With R searches on a side whose distances sum to at most 2w, the Cauchy-Schwarz inequality gives Σ √g_i ≤ √(2Rw). Then f(p, w) follows from the records without further queries (Section 1).

Since H is unknown, it is guessed as H' = 1, 2, 4, …. With guess H', each staircase stops after H' + 1 records, p included, and raises a flag if it got that far, so f(p, w) costs O(√(H'w)). For each scale, maximum finding over the n/w multiples with a bounded-error evaluation [4] costs O(√(n/w) · √(H'w)) = O(√(nH')), and a search for a raised flag with a bounded-error oracle [6] costs the same. If a flag is raised at some scale, the guess doubles and all scales run again. Every side has at most H records, so no flag is raised once H' ≥ H, and the guesses stop below 2H. Over the log n scales and the geometric sum of the guesses this is O(√(nH) log n). The maximum findings and flag searches run one after the other, and each depends only on the outputs of the earlier ones. Each computes a function of the histogram with bounded error, so it has a solution of the filtered γ₂ program of the same cost, and these solutions add up by the sequential composition of [2, Theorems 4 and 5] (used in the same way in Theorem 5 of [1]), with no loss for error reduction. ∎

**Corollary 2.** If the heights lie in a known set of H values, OPT can be computed with O(√(nH)) quantum queries.

*Proof.* OPT = max over the H values t of t · L(t), where L(t) is the longest run of heights at least t. This is the longest empty segment of the bit string [h_i < t], which takes O(√n) queries [1]. Maximum finding over the H values with a bounded-error evaluation [4] gives the bound. ∎

## 3. Few valleys

A *weak left record* of p is a position j ≤ p with h_j ≤ h_i for all i in (j, p], and weak right records are defined in the same way. Every left record is a weak left record. Write V for the number of valleys.

**Lemma 3.** In a window [lo, p], the weak left records of p form at most V′ + 2 maximal runs of consecutive positions, where V′ is the number of valleys of the histogram restricted to the window. On each run the heights do not increase going away from p.

*Proof.* If j and j − 1 are both weak left records, then h_{j−1} ≤ h_j, which is the second claim. Let x > lo be the outer end of a run, so that x − 1 is not a weak left record and h_{x−1} > h_x, and let [x, e] be the maximal run of heights equal to h_x. If e < p, then h_{e+1} ≥ h_x because x is a weak left record, so h_{e+1} > h_x, and [x, e] is a valley of the window. Distinct runs have distinct outer ends, so at most V′ runs end in this way, one run may end at lo, and one may end with e = p. ∎

**Theorem 3.** OPT, and an interval that attains it, can be computed with O(√(nV) log n + √n log² n) quantum queries and bounded error.

*Proof.* As in Theorem 1, it suffices to compute f(p, w) for every scale w and multiple p of w, within the window of Lemma 2. On each side of p, the runs of Lemma 3 are found one after the other: the first position of a run is the first position beyond the previous run whose height is at most the last height seen, and its end is the first position j beyond it, going outward, where the height goes up. Each search costs O(√g) queries for its distance g [2, Theorem 6], and with R ≤ V + 2 runs on a side the distances sum to at most twice the window side, so the Cauchy-Schwarz inequality bounds the cost by O(√(Vw)). The runs give an index of all weak records on each side, in order.

By Lemma 1(a), the height of every interval through p is the height of a weak record. For a candidate height v, the run of heights at least v through p ends, on each side, just before the first weak record with height below v, since that position is a record by Lemma 1(b) and all weak records closer to p have height at least v. By Lemma 3 the heights of the weak records do not increase going outward, so a binary search finds that position with O(log w) queries. Maximum finding over the at most 4w weak records [4] then gives f(p, w) with O(√w log w) queries. Every valley of a window is a valley of the histogram, or it touches an end of the window and leads, going down outward, to a distinct valley of the histogram, so V′ ≤ V for every window. Since V is unknown, guess G = 1, 2, 4, …, and for each guess search, at every scale, for a multiple p whose staircase on some side has more than G + 2 runs, stopping each staircase after G + 3 runs. This costs O(√(nG)) per scale, and no such p exists once G ≥ V, so the guesses stop below 2V at a total cost of O(√(nV) log n). With the final guess, f(p, w) costs O(√(Gw) + √w log w), and maximum finding over the n/w multiples costs O(√(nV) + √n log w) per scale, so O(√(nV) log n + √n log² n) over the scales. The steps run one after the other, and their solutions add up by the sequential composition as in Theorem 1. ∎

## 4. Approximation

**Theorem 4.** For 0 < ε ≤ 1, a value in [OPT/(1 + ε), OPT] can be computed with O(√(n log n / ε)) quantum queries and bounded error.

*Proof.* Find the largest height m with O(√n) queries [3]. If m = 0, then OPT = 0. Otherwise let t_b = m/(1 + ε)^b for b = 0, …, B, with B = ⌈log_{1+ε} n⌉, and output the largest t_b · L(t_b), with L as in Corollary 2.

Each t_b · L(t_b) is the area of a rectangle, so it is at most OPT. Conversely, let OPT = v · W for a rectangle of height v and width W. Since OPT ≥ m and W ≤ n, v ≥ m/n ≥ t_B, and v ≤ m = t_0. For the smallest b with t_b ≤ v, either b = 0 and t_b = v, or t_{b−1} > v and t_b > v/(1 + ε). The rectangle has all heights at least t_b, so L(t_b) ≥ W and t_b · L(t_b) ≥ OPT/(1 + ε).

There are B + 1 = O(log n / ε) values, and maximum finding over them with a bounded-error evaluation [4], each L(t_b) from [1], gives the bound. The search for m and this maximum finding each run with error at most 1/6. ∎

**Lower bound.** With heights in {0, 1}, OPT = 0 iff all heights are 0. Every approximation within any factor decides this OR of n bits, which needs Ω(√n) quantum queries [5].

## Lean

The library `Histogram` in `lean/` (Lean 4, Mathlib at the revision pinned in `lean/lakefile.toml`) proves, with only the standard axioms (`lean/axioms.txt`), for heights h : ℤ → ℝ:

- `min_is_record`, with `exists_recL` and `exists_recR`: Lemma 1(a).
- `first_below_isRecL`: Lemma 1(b) on the left; the right side is its mirror image.
- `recL_strict`, `card_recL_le`: the heights of the left records strictly increase towards p, so in every finite set of positions the left records number at most the distinct heights; the right side is the mirror image.
- `isRecL_weak`, `weakL_mono`, `first_below_weak`: every left record is a weak left record, the heights of weak left records do not increase going away from p, and the first position left of p below v ≤ h_p is a weak left record with all weak left records between it and p at height at least v. These are the facts behind the binary search of Theorem 3.
- `cover`: Lemma 2.
- `sum_sqrt_le`: R searches with distances of sum S cost Σ √g_i ≤ √(RS).
- `grid`, `approx`: the threshold step of Theorem 4. For m/(1 + ε)^B ≤ v ≤ m, some b ≤ B has m/(1 + ε)^b ≤ v ≤ (1 + ε) · m/(1 + ε)^b, and then a rectangle of height v and width W ≤ L(t_b) has area at most (1 + ε) t_b L(t_b).

Not formalized: the quantum subroutines and their error reduction, the computation of the best rectangle in a window from the records, the count of runs in Lemma 3, and the counting of queries in Theorems 1, 3 and 4 and Corollary 2.

## Scripts

`sim/check_valleys.py` checks Lemma 3 and Theorem 3 against brute force: the number of runs of weak records on each side is at most the number of valleys of the window plus 2, the searches cost at most √(2R · 2s) for R runs and a window of s positions, the best rectangle through p from the weak records and the binary searches equals the brute-force value, and the largest value over all scales and multiples equals OPT. It passes on 2500 random histograms of up to 50 bars, including sorted ones and ones with few monotone pieces and plateaus.

`sim/check_histogram.py` computes OPT with a stack and compares it with the exact algorithm of Theorem 1, run classically: the records of every multiple of every scale, the rectangle through p from the records, and the largest value over all windows. It also checks that each side has at most min(H, 2w) records and that the searches cost at most √(2Rw), and it checks the algorithm of Theorem 4 and its factor 1 + ε for ε ∈ {1, 0.5, 0.25, 0.1, 0.01}. It passes on 3000 random histograms of up to 60 bars: few distinct heights, random heights, sorted staircases and noisy pyramids.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the Lean files and the check script, and to draft the text.

## References

1. Longest empty segment in O(√n) queries: Theorem 5 in [largest-empty-rectangle-queries](../largest-empty-rectangle-queries/) of this repository; earlier O(√n log n log log n) in K. Khadiev et al., Quantum algorithm for searching for the longest segment and the largest empty rectangle, arXiv:2512.03788, 2025.
2. R. Kothari. An optimal quantum algorithm for the oracle identification problem. STACS 2014. arXiv:1311.7685.
3. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014, 1996.
4. Q. Wang, M. Ying. Quantum algorithm for lexicographically minimal string rotation. arXiv:2012.09376.
5. C. H. Bennett, E. Bernstein, G. Brassard, U. Vazirani. Strengths and weaknesses of quantum computing. SIAM J. Comput. 26(5), 1997. arXiv:quant-ph/9701001.
6. P. Høyer, M. Mosca, R. de Wolf. Quantum search on bounded-error inputs. ICALP 2003. arXiv:quant-ph/0304052.
