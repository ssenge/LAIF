# Stock trading with at most t transactions: quantum queries

Written 21 Nov 2026.

**Setting.** The input is a sequence of n integer prices x_1, …, x_n in [0, W], and a query returns one price. A transaction buys at a day i and sells at a later day j > i, with profit x_j − x_i. For t ≥ 0, f(t) is the largest total profit of at most t transactions whose intervals are disjoint, i_1 < j_1 < i_2 < j_2 < ⋯, so f(0) = 0 (allowing j_ℓ = i_{ℓ+1} gives the same value, since a sale and a purchase on the same day merge into one transaction). The task is to compute f(t).

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | f(t), upper bound | O(√(n log^{2t−1} n)) for every constant t [1]; √n · exp(O(log² t + log t · log log n)) [2]; both independent of W | O(√(nt) · log(W+2) · log^{3/2}(n+1) · log(n log(W+2))) | Claim; checked by script |
| Thm 2 | f(t), lower bound | Ω(√n) | Ω(√(nt)) for 1 ≤ t ≤ n/4, already for W = 1, implied by [4] | Claim; encoding checked by script |

So for prices of polynomial size, log W = O(log n), and 1 ≤ t ≤ n/4, the quantum query complexity of f(t) is Θ̃(√(nt)), polynomial in the number of transactions. The bounds of [1] and [2] are stated for exactly t transactions. They apply to f(t) as well: f(t) is the largest of the values for exactly 0, …, t transactions, which for [2] are entries of one matrix product and for [1] come from t + 1 runs.

**Scope.** For log W = O(log n), the bound of Theorem 1 is O(√(nt) log^{7/2} n). It is smaller than the bound of [1] for every constant t ≥ 5, and smaller than the bound of [2] for every t above a constant that depends on the constant in the exponent of [2]; for t = n^δ with δ > 0 the bound of [2] exceeds n, while Theorem 1 gives n^{(1+δ)/2} polylog n. The factor log(W+2) is not present in [1] and [2], so for prices with very many bits their bounds are smaller. The bound counts queries only.

## The fee problem and its zigzag

For a fee λ ≥ 0, let F(λ) be the largest value of Σ (x_j − x_i − λ) over any number of disjoint transactions.

**Zigzag.** Start in the down state with lo = x_1 and process x_2, …, x_n. In the down state, a price p with p − lo ≥ λ switches to the up state with hi = p; otherwise lo becomes min(lo, p). In the up state, a price p with hi − p ≥ λ completes a leg of value hi − lo − λ and switches to the down state with lo = p; otherwise hi becomes max(hi, p). At the end, an open up state adds hi − lo − λ. Write Z(λ) for the total and m(λ) for the number of legs, counting an open leg at the end.

**Lemma 1.** For every λ ≥ 0, Z(λ) = F(λ).

*Proof.* F(λ) is computed by the dynamic programme that updates both values at once, cash ← max(cash, hold + p − λ) and hold ← max(hold, cash − p), starting after x_1 with cash = 0 and hold = −x_1, and ends with F(λ) = cash. Let C be the total of the legs completed so far. By induction over the prices: in the down state, cash = C and hold = C − lo; in the up state, cash = C + hi − lo − λ and hold = C − lo. This holds after x_1, where C = 0 and lo = x_1. The four transitions keep it:

* down state, p − lo < λ: cash stays C, and hold becomes C − min(lo, p);
* down state, p − lo ≥ λ: cash becomes C + p − lo − λ, and hold stays C − lo since p ≥ lo;
* up state, hi − p < λ: cash becomes C + max(hi, p) − lo − λ, and hold stays C − lo since cash − p < C − lo;
* up state, hi − p ≥ λ: cash stays C + hi − lo − λ since p ≤ hi, and hold becomes C + hi − lo − λ − p ≥ C − lo, the new C minus the new lo.

At the end, cash equals Z(λ). ∎

**Lemma 2.** F(λ) = max_k (f(k) − kλ), and the legs of the zigzag have total profit Z(λ) + λ m(λ) = f(m(λ)). So m(λ) maximizes f(k) − kλ.

*Proof.* The first claim holds since λ ≥ 0 and f(k) is the best value with at most k transactions. The m = m(λ) legs are disjoint transactions, so their profit P is at most f(m), and P − mλ = Z(λ) = F(λ) ≥ f(m) − mλ by Lemma 1. ∎

**Lemma 3.** f is nondecreasing and concave, with integer values, and f(k) = f(⌊n/2⌋) for k ≥ ⌊n/2⌋.

*Proof.* Only the concavity needs an argument. Let h_d ∈ {0, 1} say whether the stock is held from day d to day d + 1, for d = 1, …, n − 1, and s_d ≥ h_d − h_{d−1} count the purchases (with h_0 = 0). Then f(k) is the largest value of Σ h_d (x_{d+1} − x_d) subject to 0 ≤ h_d ≤ 1, s_d ≥ 0, s_d − h_d + h_{d−1} ≥ 0 and Σ s_d ≤ k: a 0/1 vector h has one run of ones per transaction, consecutive runs are separated by a zero, and the number of runs is Σ max(0, h_d − h_{d−1}) ≤ Σ s_d. After negating the last row, every column of the constraint matrix has at most one +1 and at most one −1, so it is the incidence matrix of a directed graph with some arcs cut, and it stays totally unimodular with the bound rows added. The polyhedron is pointed and integral for integer k, so the optimum is attained at an integral vertex, and the value of the linear programme is concave in the right-hand side k. ∎

**Lemma 4.** Let 0 < ε with nε < 1 (the script uses ε = 1/(2n+1)), t ≤ n, and a ≥ 0 an integer. If K = m(a + ε) ≤ t, and either a = 0 or m(a − 1 + ε) > t, then f(t) = f(K) + (t − K) a.

*Proof.* By Lemma 2, K maximizes f(k) − k(a + ε), so f(t) − f(K) ≤ (t − K)(a + ε) < (t − K) a + 1, and f(t) − f(K) ≤ (t − K) a since both sides are integers. If a = 0, f(t) ≥ f(K) since f is nondecreasing. Otherwise K′ = m(a − 1 + ε) > t maximizes f(k) − k(a − 1 + ε), so f(K′) − f(t) ≥ (K′ − t)(a − 1 + ε). By concavity the slope d = f(t + 1) − f(t) satisfies f(K′) − f(t) ≤ (K′ − t) d, so d > a − 1, hence d ≥ a, and again by concavity f(t) − f(K) ≥ (t − K) d ≥ (t − K) a. ∎

The technique behind Lemma 4, a Lagrangian fee with a binary search over it for a concave value function, is classical [3]. The quantum query bound below is the contribution of this folder.

## Theorem 1, the algorithm

Assume t ≤ ⌊n/2⌋, since f(t) = f(⌊n/2⌋) beyond that, and t ≥ 1. Since prices are integers, a rise or drop is at least a + ε exactly when it is at least a + 1. One run of the zigzag at threshold c = a + 1, stopped when the (t + 1)-th leg starts, consists of at most 2t + 2 phases, and it decides whether m(a + ε) ≤ t. A phase that starts at day r in the down state ends at the first day j > r for which the window x_r, …, x_j has a rise x_v − x_u ≥ c with u < v, and lo is the minimum of x_r, …, x_{j−1}. A phase in the up state ends at the first day with a drop of at least c from an earlier day of the window, and hi is the maximum of the window before it. The last phase of a run may reach day n without an end.

The predicate "the window of length L from r has a rise of at least c" is monotone in L and is decided with O(√(L log L)) queries by the single-transaction algorithm of [1]. Galloping over L = 1, 2, 4, … and then a binary search finds the end of a phase whose window has length ℓ with O(√ℓ · log^{3/2}(n+1)) queries, and one minimum or maximum finding gives lo or hi. Consecutive windows share one day, so the window lengths ℓ_1, ℓ_2, … sum to at most n + 2t + 2 ≤ 3n, and a run costs O(Σ √ℓ_i · log^{3/2}(n+1)) = O(√(tn) · log^{3/2}(n+1)) by the Cauchy-Schwarz inequality.

Let D = max x − min x, found with O(√n) queries; no rise exceeds D, so m(D + ε) = 0. If m(ε) ≤ t, take a* = 0. Otherwise a binary search over {0, …, D} with the invariant m(lo + ε) > t ≥ m(hi + ε) ends with an integer a* such that m(a* + ε) ≤ t < m(a* − 1 + ε), after O(log(W+2)) runs; this needs no monotonicity of m. The final run gives K = m(a* + ε) and the profit of its legs, which is f(K) by Lemma 2, and Lemma 4 gives f(t). There are O(t log n log(W+2)) decisions in total, so amplifying each to error below 1/(10 times their number) costs a factor O(log(n log(W+2))). ∎

## Theorem 2, the lower bound

For bits b_1, …, b_N, the prices 0, b_1, 0, b_2, …, 0, b_N (with a 0 appended for odd n) have f(t) = min(t, |b|). The pairs (0, b_i) with b_i = 1 give min(t, |b|). Conversely, every transaction gains at most 1, and the total profit of disjoint transactions is at most the sum of the positive steps x_{d+1} − x_d, which is |b|. Deciding whether |b| ≥ t takes Ω(√(t(N − t + 1))) queries [4], which is Ω(√(nt)) for n = 2N and t ≤ n/4. ∎

## Scripts

`sim/check_zigzag.py` checks Lemmas 1, 2 and 4 against a dynamic programme on 3000 random price sequences of length at most 14 with W ∈ {1, 2, 5, 30}: the zigzag equals the fee programme for six fees, f is concave, and the formula of Lemma 4 returns f(t) for every t. It also runs the phase decomposition of the algorithm at every threshold, checks that it agrees with the zigzag, that a run stopped after t + 1 legs has at most 2t + 3 phases with Σ √ℓ_i ≤ √((2t+3)n), where ℓ_i counts the days of a phase without its last day, and that it decides m(a + ε) ≤ t correctly. Finally it checks f(t) = min(t, |b|) for the encoding of Theorem 2.

```
python sim/check_zigzag.py
3000 price sequences checked
lower bound encoding checked
```

**Not formalized:** all of the folder.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. J. Allcock, J. Bao, A. Belovs, T. Lee, M. Santha. On the quantum time complexity of divide and conquer. ICALP 2025. arXiv:2311.16401.
2. T. Lee, M. Santha. The quantum query complexity of the semigroup product problem. arXiv:2609.39974, 2026.
3. A. Aggarwal, B. Schieber, T. Tokuyama. Finding a minimum-weight k-link path in graphs with the concave Monge property and applications. Discrete and Computational Geometry 12, 1994.
4. R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf. Quantum lower bounds by polynomials. Journal of the ACM 48, 2001.
