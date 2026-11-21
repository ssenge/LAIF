# Stock trading with at most t transactions: quantum queries

Written 21 Nov 2026.

**Setting.** The input is a sequence of n integer prices x_1, …, x_n in [0, W], and a query returns one price. A transaction buys at a day i and sells at a later day j > i, with profit x_j − x_i. For t ≥ 1, f(t) is the largest total profit of at most t transactions whose intervals are disjoint, i_1 < j_1 < i_2 < j_2 < ⋯ (allowing j_ℓ = i_{ℓ+1} gives the same value, since a sale and a purchase on the same day merge into one transaction). The task is to compute f(t).

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | f(t), upper bound | O(√n log^{2t−1} n) for every constant t [1]; √n · exp(O(log² t + log t · log log n)) [2]; both independent of W | O(√(nt) · log(W+2) · log^{3/2}(n+1) · log(n log(W+2))) | Claim; checked by script |
| Thm 2 | f(t), lower bound | Ω(√n) | Ω(√(nt)) for 1 ≤ t ≤ n/4, already for W = 1, implied by [4] | Claim; encoding checked by script |

So for prices of polynomial size, log W = O(log n), the quantum query complexity of f(t) is Θ̃(√(nt)), polynomial in the number of transactions. The bounds of [1] and [2] are stated for exactly t transactions; f(t) is the largest of the entries for exactly 0, …, t transactions of the same product in [2], so the bound of [2] applies to f(t) as well.

**Scope.** The bound of Theorem 1 has a factor log(W+2) that the bounds of [1] and [2] do not have. It is the smaller bound whenever log(W+2) is below t^{C log t} (log n)^{C log t} for a suitable constant C, for example when log W is polylogarithmic in n and t grows, or t is a large enough constant. For prices with very many bits the bound of [2] is smaller. The bound counts queries only.

## The fee problem and its zigzag

For a fee λ ≥ 0, let F(λ) be the largest value of Σ (x_j − x_i − λ) over any number of disjoint transactions.

**Zigzag.** Start in the down state with lo = x_1. In the down state, a price p with p − lo ≥ λ switches to the up state with hi = p; otherwise lo becomes min(lo, p). In the up state, a price p with hi − p ≥ λ completes a leg of value hi − lo − λ and switches to the down state with lo = p; otherwise hi becomes max(hi, p). At the end, an open up state adds hi − lo − λ. Write Z(λ) for the total and m(λ) for the number of legs.

**Lemma 1.** For every λ ≥ 0, Z(λ) = F(λ).

*Proof.* F(λ) is computed by the dynamic programme cash ← max(cash, hold + p − λ), hold ← max(hold, cash − p), with cash = 0 and hold = −∞ before the first price and F(λ) = cash at the end. Let C be the total of the legs completed so far. By induction over the prices: in the down state, cash = C and hold = C − lo; in the up state, cash = C + hi − lo − λ and hold = C − lo. Each of the four transitions keeps this. For example, in the up state a price p with hi − p < λ gives cash − p = C + hi − lo − λ − p < C − lo, so hold does not change, and a price p with hi − p ≥ λ gives hold = C + hi − lo − λ − p ≥ C − lo, which is the new C minus the new lo. At the end, cash equals Z(λ). ∎

**Lemma 2.** F(λ) = max_k (f(k) − kλ), and the legs of the zigzag have total profit Z(λ) + λ m(λ) = f(m(λ)).

*Proof.* The first claim holds since λ ≥ 0 and f(k) is the best value with at most k transactions. The m = m(λ) legs are disjoint transactions, so their profit P is at most f(m), and P − mλ = F(λ) ≥ f(m) − mλ. ∎

**Lemma 3.** f is concave on 0, 1, …, n with integer values.

*Proof.* Let h_d ∈ {0, 1} say whether the stock is held from day d to day d + 1, and s_d ≥ h_d − h_{d−1} count the purchases (with h_0 = 0). Then f(k) is the largest value of Σ h_d (x_{d+1} − x_d) subject to 0 ≤ h_d ≤ 1, s_d ≥ 0, s_d − h_d + h_{d−1} ≥ 0 and Σ s_d ≤ k. After negating the last row, every column of the constraint matrix has one +1 and one −1, so the matrix is a network matrix and totally unimodular. The linear programme has an integral optimum for integer k, and its value is concave in the right-hand side k. ∎

**Lemma 4.** Let ε = 1/(2n+1), and for an integer a ≥ 0 let K(a) = m(a + ε). Then K is nonincreasing, and if a* is the smallest a ≥ 0 with K(a) ≤ t, then f(t) = f(K(a*)) + (t − K(a*)) a*.

*Proof.* Two values f(k) − k(a + ε) and f(k′) − k′(a + ε) with k ≠ k′ in 0, …, n differ by an integer minus (k − k′)ε, which is not an integer, so f(k) − k(a + ε) has a unique maximizer. By Lemma 2 it is K(a). With the slopes d_k = f(k) − f(k − 1), which are integers, nonincreasing by Lemma 3 and at least 0, the unique maximizer is K(a) = #{k : d_k > a}. So K is nonincreasing, K(a) ≤ t if and only if d_{t+1} ≤ a, and a* = d_{t+1} (with d_{t+1} = 0 if t ≥ n). For K(a*) < k ≤ t, d_k ≤ a* by the choice of K and d_k ≥ d_{t+1} = a* by concavity, so every such slope equals a*. ∎

The technique behind Lemma 4, a Lagrangian fee with a binary search over it for a concave value function, is classical [3]. The quantum query bound below is the contribution of this folder.

## Theorem 1, the algorithm

Since prices are integers, a rise or drop is at least a + ε exactly when it is at least a + 1. One run of the zigzag at threshold c = a + 1, stopped after t + 1 legs, consists of at most 2t + 3 phases. A phase that starts at day r in the down state ends at the first day j > r for which the window x_r, …, x_j has a rise x_v − x_u ≥ c with u < v, and lo is the minimum of x_r, …, x_{j−1}. A phase in the up state ends at the first day with a drop of at least c from an earlier day of the window, and hi is the maximum of the window before it.

The predicate "the window of length L from r has a rise of at least c" is monotone in L and is decided with O(√(L log L)) queries by the single-transaction algorithm of [1]. Galloping over L = 1, 2, 4, … and then a binary search finds the end of a phase of length ℓ with O(√ℓ · log^{3/2}(n+1)) queries, and one minimum or maximum finding gives lo or hi. The phase lengths ℓ_1, ℓ_2, … sum to at most n, so a run costs O(Σ √ℓ_i · log^{3/2}(n+1)) = O(√((2t+3)n) · log^{3/2}(n+1)) by the Cauchy-Schwarz inequality.

A binary search over a ∈ {0, …, W} with O(log(W+2)) runs finds a*, since K is nonincreasing and K(W) = 0. The final run gives K(a*) and the profit of its legs, which is f(K(a*)) by Lemma 2, and Lemma 4 gives f(t). There are O(t log n log(W+2)) decisions in total, so amplifying each to error below 1/(10 times their number) costs a factor O(log(n log(W+2))). ∎

## Theorem 2, the lower bound

For bits b_1, …, b_N, the prices 0, b_1, 0, b_2, …, 0, b_N have f(t) = min(t, |b|), since a transaction gains at most 1 and the pairs (0, b_i) are disjoint. Deciding whether |b| ≥ t takes Ω(√(t(N − t + 1))) queries [4], which is Ω(√(nt)) for n = 2N and t ≤ n/4. ∎

## Scripts

`sim/check_zigzag.py` checks Lemmas 1, 2 and 4 against a dynamic programme on 3000 random price sequences of length at most 14 with W ∈ {1, 2, 5, 30}: the zigzag equals the fee programme for six fees, f is concave, and the formula of Lemma 4 returns f(t) for every t. It also runs the phase decomposition of the algorithm at every threshold, checks that it agrees with the zigzag, that K is nonincreasing, that a run stopped after t + 1 legs has at most 2t + 3 phases with Σ √ℓ_i ≤ √((2t+3)n), and that it decides K(a) ≤ t correctly. Finally it checks f(t) = min(t, |b|) for the encoding of Theorem 2.

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
