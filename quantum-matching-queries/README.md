# Quantum query complexity of maximum matching on general graphs

Minor results from an attempt to improve the O(n^{7/4}) bound of [1] on adjacency-matrix quantum queries for maximum matching on general graphs, against the lower bound Ω(n^{3/2}). No bound was improved. Results 1 to 3 have proofs below; none is formalized in Lean, and no human has checked them. Result 4 is measurement only. No dedicated search for earlier statements of these results was made, so none is claimed as new; results 1 and 2 are short enough to be folklore.

| # | Result | Status | Importance |
|---|---|---|---|
| 1 | Guessing trees give communication protocols, so a large class of trees cannot beat n^{7/4} without new communication bounds | proved below | minor |
| 2 | Õ(n^{3/2}√(1+κ)) queries from a half-integral warm start, hence Õ(n^{3/2}√(1+n/g)) at odd girth g | proved below | minor |
| 3 | Approximate-then-finish needs a (1−ε)-approximation with n/ε^c reveals and c < 1 | calculation | minor |
| 4 | LP rounds with a small odd-set family do not give hybrid cost o(√n) | measured | minor |

Setting: an n-vertex graph, adjacency-matrix queries. The guessing tree theorem ([2]; Theorem 1 in [1]) turns a decision tree of depth T with at most I wrong guesses per path into O(√(T·I)) quantum queries. The tree of [1] has T ≤ n² and I = O(n^{3/2}), which is where n^{7/4} comes from.

## 1. Barrier for the guessing tree route

**Proposition.** Take a decision tree computing a function of the edge set, with depth T and at most I wrong guesses per path.

- (a) If the tree always guesses "no edge", the usual edge-partition two-party problem has a deterministic protocol with O(I log T) bits. In that problem each edge is held by one player, and a player does not know the other player's edges.
- (b) With arbitrary guesses, the same bound holds in a weaker model: every vertex pair is assigned in advance to a player who knows whether it is an edge.

*Proof.* The players keep a common position in the tree. From there, each follows the guessed path and finds the first node where its own data contradicts the guess: in (a) a queried pair that it holds as an edge, in (b) a pair assigned to it whose status differs from the guess. It sends that depth, which takes log T bits. The earlier of the two depths is the true first wrong guess. If neither player reports one, the guessed path runs to a leaf. Both players move to the node just after the wrong guess, using the true answer. Each exchange uses up one wrong guess, so there are at most I+1 exchanges. ∎

**Consequence.** The matrix-model tree of [1] guesses "no edge" throughout. A tree of that kind with T = Θ(n²) that beats n^{7/4} polynomially has I = n^{3/2−Ω(1)}, so by (a) it gives a deterministic o(n^{3/2}) edge-partition protocol for general matching. The best known is Õ(n^{3/2}) [3]. Improving it is stated as open in [3] and in [4].

**Why (a) needs "no edge" guesses.** To refute a guess "edge", both players must confirm they do not hold the pair. A player cannot find the first such node alone, and finding it looks like a set-intersection problem over T elements. An argument that ignores this distinction is wrong.

**What this does not say.** It is not a lower bound on queries, and n^{7/4} may still be far from optimal. Two loopholes remain:
1. Smaller T. With T = n^{2−Ω(1)}, I can stay at n^{3/2} or above.
2. Trees that guess "edge" somewhere. Then only (b) applies, and improving matching in the assigned-pair model may be easier than in the usual model.

## 2. Warm start and odd girth

**Theorem.** A maximum matching can be found with Õ(n^{3/2}√(1+κ)) bounded-error queries, where κ is the number of odd cycles in the half-integral solution of step 1. If G has odd girth g, then κ ≤ n/g, so no promise is needed and the bound is Õ(n^{3/2}√(1+n/g)). This is polynomially below n^{7/4} for g ≥ n^{1/2+Ω(1)}.

*Proof.*

1. **Half-integral solution.** The bipartite double cover has 2n vertices, and one query to it is one query to G. A maximum matching M' of the cover costs O(n^{3/2} log² n) queries [4]. Setting x_uv = (1[u₁v₂ ∈ M'] + 1[v₁u₂ ∈ M'])/2 gives a maximum fractional matching of G. It is half-integral, and its half-weight edges form disjoint paths and cycles.
2. **Rounding, no queries.** Replace each path and even cycle by an alternating matching, which does not lose value. Remove one vertex from each of the κ odd cycles and match the rest. The result M₀ satisfies |M₀| ≥ ν_f − κ/2 ≥ ν − κ/2. The cycles are disjoint with length at least g, so κ ≤ n/g.
3. **Finishing, by a tree that guesses "no edge".** Run the textbook Edmonds search from all free vertices of the current matching. Skip a pair (x, y) with x outer unless y is unlabelled, or y is outer in another blossom. Read an eligible pair from a query record if it was read before, otherwise query it. A wrong guess reveals an edge and forces one of: a grow step (at most n/2 per search, as each adds two vertices), a blossom shrink (at most n/2 per search), or an augmenting path, which ends the search. So each search has at most n+1 wrong guesses. A search that ends with no eligible pair left certifies maximality by the usual Hungarian-forest argument. There are at most κ/2 + 1 searches, and κ is known after step 1. With T ≤ n² from the query record, the tree theorem gives O(√(n²·n(1+κ))) queries. ∎

Step 3 does not depend on the analysis of [1]. That analysis also allows an arbitrary starting matching: each iteration of its Listing 2.1 rebuilds its weights and duals from the current M alone, and its Lemmas 1 and 2 do not use how M arose.

**Corollary (communication).** The deterministic edge-partition complexity of maximum matching is O(n log² n + n(1+κ) log n), so O(n log² n + (n²/g) log n) at odd girth g. This is below n^{3/2} once g ≫ √n log n. *Proof.* Theorem 1.1 of [4] finds a matching of the double cover with O(n log² n) bits. Each edge of G becomes two cover edges at the same player. Then apply Proposition 1(a) to step 3.

**Limits.** This is a parameterized statement and does not touch the general case. Graphs with many disjoint short odd cycles get no gain, and such graphs are the hard ones.

## 3. Approximate-then-finish needs c < 1

Let R be the number of edge reveals, so that the query bound is O(n√R) when T = Θ(n²). From deficiency d, at most d+1 further searches of at most n reveals each finish the job, so R ≤ R_approx(d) + n(d+1).

Beating R = n^{3/2} needs d = o(√n), that is ε = o(n^{−1/2}). If R_approx = n·ε^{−c}, this needs n^{1+c/2} = o(n^{3/2}), so **c < 1**.

The first phase of [3] reveals n² ln n / k edges for deficiency k. That is c = 1, and the balance sits exactly at n^{3/2}. Semi-streaming reductions, judged from their abstracts only, have c far above 1. So a (1−ε)-approximation with n/ε^c reveals and c < 1 would be enough, and we know of none.

## 4. LP rounds with a small odd-set family fail as stated

**The route.** Solve the blossom LP on a family F of O(n) odd sets, growing F over r rounds. If one LP solve cost Õ(n) reveals (never proved), then Q = Õ(n^{3/2}√cost), where cost = min_r[(r+1) + d_r] and d_r is the deficiency of the best matching on the edges revealed by round r. The route needs worst-case cost o(√n).

**Measurements** (scripts in `sim/`, each with self-checks; Python with scipy and networkx):

*Hidden bridges* (`flat.py`, `flat.log`). Two odd sets joined by one edge that a perfect matching needs, adversarial objective, worst of 3 seeds. The run was stopped during k = 7, s = 21; rows shown are for 2 chords per vertex unless noted.

| k, s | n | cut odd support components: rounds | also cut Gallai-Edmonds D-components: rounds |
|---|---|---|---|
| 1, 41 | 82 | 300 (cap) | 4 |
| 1, 81 | 162 | 300 (cap) | 4 |
| 3, 21 (noise 0.3) | 126 | 300 (cap) | 5 |
| 3, 41 | 246 | 300 (cap) | 4 |

*Nested ears* (`ear_chain.py`, `ear_chain.log`) defeat the better rule. r_primal is the first round whose accumulated support contains a maximum matching.

| n | 14 | 22 | 38 | 70 | 134 | 262 | 518 |
|---|---|---|---|---|---|---|---|
| worst of 10 random objectives | 2 | 4 | 6 | 12 | 24 | 46 | 93 |
| depth-penalty objective | 2 | 3 | 4 | 7 | 12 | 23 | 44 |

Both rows grow linearly in n, so random perturbation chosen by the algorithm does not help.

*Copies of nested ears* (`ear_copies.py`, `ear_copies.log`, random objective, no noise edges). The last planned row, k = 32, m = 16, noise 2.0, hit the time limit.

| k, m | n | √n | cost_d | cost_pass | passes without LP |
|---|---|---|---|---|---|
| 8, 16 | 560 | 23.7 | 9 | 3 | 5 |
| 16, 16 | 1120 | 33.5 | 17 | 3 | 5 |
| 32, 16 | 2240 | 47.3 | 30 | 3 | 5 |

cost_d tracks k. So the LP does not remove the deficiency on this family, and cost = o(√n) fails if each unit of deficiency costs one search.

**What this does not show.**
- It is not a proof. It covers two specific cut rules and finite sizes, with no lower bound over all cut rules.
- cost_pass stays small on these disjoint copies, because one pass of disjoint augmentations fixes them all. With noise edges pure passes reach 17 at n = 1216, and cost_pass reaches 11 at n = 1120. That is too few points to fit an exponent. Passes have no known worst-case bound, and any remaining hope sits there, not in the LP.
- Low costs on the earlier gadget families (`hybrid.py`, `copies.py`) say nothing in favour of the LP, since passes with no LP finish those instances in at most 5.
- `adversary2.py` stayed at score 2 up to s = 70. The objective is nearly flat, so that result is uninformative.

## What to try first if this is reopened

Result 1(a) means a guess-no-edge tree at T = Θ(n²) must also improve general-matching communication. So the matching communication question comes first, or else a tree with small T on the paths that have many reveals.

## References

1. S. Kimmel, R. T. Witter. A Query-Efficient Quantum Algorithm for Maximum Matching on General Graphs. arXiv:2010.02324.
2. S. Beigi, L. Taghavi. Quantum speedup based on classical decision trees. Quantum 4, 241, 2020.
3. Cheng, Jiang, Sawettamalya, Yu. arXiv:2607.05751.
4. J. Blikstad, J. van den Brand, Y. Efron, S. Mukhopadhyay, D. Nanongkai. Nearly Optimal Communication and Query Complexity of Bipartite Matching. FOCS 2022, arXiv:2208.02526.
