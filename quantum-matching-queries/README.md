# Quantum query complexity of maximum matching on general graphs

Minor results on maximum matching with adjacency-matrix quantum queries on general graphs. The best known general bound is O(n^{7/4}) [1], against the lower bound Ω(n^{3/2}). Results 1 and 2 have written proofs, and result 3 is a calculation. None is formalized in Lean, and no human has checked them. They are short enough to be folklore, so none is claimed as new.

| # | Result | Status |
|---|---|---|
| 1 | A decision tree with at most I wrong "no edge" guesses gives a deterministic edge-partition protocol with O(I log T) bits | proved below |
| 2 | Õ(n^{3/2}√(1+κ)) queries from a half-integral warm start, hence Õ(n^{3/2}√(1+n/g)) at odd girth g, with the corresponding communication bound | proved below |
| 3 | In a guessing tree with T = Θ(n²), a (1−ε)-approximation with n/ε^c edge reveals and c < 1 gives n^{7/4−Ω(1)} queries | calculation |

Setting: an n-vertex graph, adjacency-matrix queries. The guessing tree theorem ([2]; Theorem 1 in [1]) turns a decision tree of depth T with at most I wrong guesses per path into O(√(T·I)) quantum queries. The tree of [1] has T ≤ n² and I = O(n^{3/2}), which is where n^{7/4} comes from.

## 1. From guessing trees to communication protocols

**Proposition.** Take a decision tree computing a function of the edge set, with depth T and at most I wrong guesses per path.

- (a) If the tree always guesses "no edge", the usual edge-partition two-party problem has a deterministic protocol with O(I log T) bits. In that problem each edge is held by one player, and a player does not know the other player's edges.
- (b) With arbitrary guesses, the same bound holds in a weaker model: every vertex pair is assigned in advance to a player who knows whether it is an edge.

*Proof.* The players keep a common position in the tree. From there, each follows the guessed path and finds the first node where its own data contradicts the guess: in (a) a queried pair that it holds as an edge, in (b) a pair assigned to it whose status differs from the guess. It sends that depth, which takes log T bits. The earlier of the two depths is the true first wrong guess. If neither player reports one, the guessed path runs to a leaf. Both players move to the node just after the wrong guess, using the true answer. Each exchange uses up one wrong guess, so there are at most I+1 exchanges. ∎

**Consequence.** The matrix-model tree of [1] guesses "no edge" throughout. A tree of that kind with T = Θ(n²) and n^{7/4−Ω(1)} queries has I = n^{3/2−Ω(1)}, so by (a) it gives a deterministic o(n^{3/2}) edge-partition protocol for general matching. The best known protocol has Õ(n^{3/2}) bits [3], and improving it is stated as open in [3] and in [4].

**Why (a) needs "no edge" guesses.** To refute a guess "edge", both players must confirm they do not hold the pair. A player cannot find the first such node alone, and finding it looks like a set-intersection problem over T elements.

**Scope.** This is not a lower bound on queries. It does not cover trees with T = n^{2−Ω(1)}, where I can stay at n^{3/2} or above, or trees that guess "edge" somewhere, where only (b) applies.

## 2. Warm start and odd girth

**Theorem.** A maximum matching can be found with Õ(n^{3/2}√(1+κ)) bounded-error queries, where κ is the number of odd cycles in the half-integral solution of step 1. If G has odd girth g, then κ ≤ n/g, so no promise is needed and the bound is Õ(n^{3/2}√(1+n/g)). This is polynomially below n^{7/4} for g ≥ n^{1/2+Ω(1)}.

*Proof.*

1. **Half-integral solution.** The bipartite double cover has 2n vertices, and one query to it is one query to G. A maximum matching M' of the cover costs O(n^{3/2} log² n) queries [4]. Setting x_uv = (1[u₁v₂ ∈ M'] + 1[v₁u₂ ∈ M'])/2 gives a maximum fractional matching of G. It is half-integral, and its half-weight edges form disjoint paths and cycles.
2. **Rounding, no queries.** Replace each path and even cycle by an alternating matching, which does not lose value. Remove one vertex from each of the κ odd cycles and match the rest. The result M₀ satisfies |M₀| ≥ ν_f − κ/2 ≥ ν − κ/2. The cycles are disjoint with length at least g, so κ ≤ n/g.
3. **Finishing, by a tree that guesses "no edge".** Run the textbook Edmonds search from all free vertices of the current matching. Skip a pair (x, y) with x outer unless y is unlabelled, or y is outer in another blossom. Read an eligible pair from a query record if it was read before, otherwise query it. A wrong guess reveals an edge and forces one of: a grow step (at most n/2 per search, as each adds two vertices), a blossom shrink (at most n/2 per search), or an augmenting path, which ends the search. So each search has at most n+1 wrong guesses. A search that ends with no eligible pair left certifies maximality by the usual Hungarian-forest argument. There are at most κ/2 + 1 searches, and κ is known after step 1. With T ≤ n² from the query record, the tree theorem gives O(√(n²·n(1+κ))) queries. ∎

Step 3 does not depend on the analysis of [1]. That analysis also allows an arbitrary starting matching: each iteration of its Listing 2.1 rebuilds its weights and duals from the current M alone, and its Lemmas 1 and 2 do not use how M arose.

**Corollary (communication).** The deterministic edge-partition complexity of maximum matching is O(n log² n + n(1+κ) log n), so O(n log² n + (n²/g) log n) at odd girth g. This is below n^{3/2} once g ≫ √n log n. *Proof.* Theorem 1.1 of [4] finds a matching of the double cover with O(n log² n) bits. Each edge of G becomes two cover edges at the same player. Then apply Proposition 1(a) to step 3.

**Scope.** This is a parameterized statement and does not touch the general case. Graphs with many disjoint short odd cycles get no gain.

## 3. From an approximation to an exact matching

Let R be the number of edge reveals, so that the query bound is O(n√R) when T = Θ(n²). From deficiency d, at most d+1 further searches of at most n reveals each finish the job, so R ≤ R_approx(d) + n(d+1).

Reaching R = n^{3/2−Ω(1)} takes d = n^{1/2−Ω(1)}, that is ε = n^{−1/2−Ω(1)}. If R_approx = n·ε^{−c} with **c < 1**, a small enough polynomial choice of ε gives this, and the query bound is n^{7/4−Ω(1)}.

We know of no such approximation. The first phase of [3] reveals n² ln n / k edges for deficiency k, which is c = 1, where the balance sits exactly at n^{3/2}.

## References

1. S. Kimmel, R. T. Witter. A Query-Efficient Quantum Algorithm for Maximum Matching on General Graphs. arXiv:2010.02324.
2. S. Beigi, L. Taghavi. Quantum speedup based on classical decision trees. Quantum 4, 241, 2020.
3. Cheng, Jiang, Sawettamalya, Yu. arXiv:2607.05751.
4. J. Blikstad, J. van den Brand, Y. Efron, S. Mukhopadhyay, D. Nanongkai. Nearly Optimal Communication and Query Complexity of Bipartite Matching. FOCS 2022, arXiv:2208.02526.
