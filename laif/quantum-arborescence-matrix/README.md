# Quantum minimum-weight arborescence in the adjacency matrix model

26 November 2026

## Result

**Theorem 1.** Let G be a digraph on n vertices, given by its weighted adjacency matrix (entry W[u][v] is the weight of the arc u→v, or ∞ if there is no arc), and fix a root r. A quantum algorithm computes a minimum-weight spanning arborescence rooted at r, or reports that none exists, with Õ(n^{3/2}) queries and success probability at least 2/3. Precisely, O(n^{3/2} log^{5/2} n) queries suffice.

Theorem 1 is tight up to the polylogarithmic factor. On a symmetric matrix, every spanning tree oriented away from r is an arborescence, so the minimum arborescence has the weight of a minimum spanning tree, and the bound Ω(n^{3/2}) for minimum spanning trees in the matrix model [1] applies.

### Before and after

| Problem, adjacency matrix model | Previous best bound | This folder |
|---|---|---|
| Minimum spanning tree, undirected | Θ(n^{3/2}) [1] | |
| Minimum-weight arborescence (directed minimum spanning tree) | O(n²) by reading the matrix and running the algorithm of [2, 3]; Ω(n^{3/2}), implied by [1] | Õ(n^{3/2}), Theorem 1 |

For comparison, a directed minimum spanning tree in the Quantum CONGEST-CLIQUE model is given in [6]; that is a different model with a different cost measure.

## The algorithm

The base is the path-growing form of the contraction algorithm of [2, 3], as described in [4, 5].

- Vertices are grouped into supernodes, which start as singletons. Every vertex v carries an offset off[v], and the reduced weight of an arc u→v is W[u][v] − off[v].
- A path of supernodes is grown from an unfinished vertex. The head X of the path picks the arc of least reduced weight entering X from outside, u→v with v ∈ X and u ∉ X, and every member of X gets its offset raised by that reduced weight c.
- If u lies in a finished supernode, the whole path is finished. If u lies on the path, the cycle closes and its supernodes are merged into one new head. Otherwise the supernode of u becomes the new head.
- Every supernode picks at most once, and there are at most 2n − 1 supernodes, so there are at most 2n − 1 picks.
- The weight of the arborescence is the sum of the picked reduced weights. The arcs are recovered from the picks by the standard expansion of the cycles, with no further queries.

With plain minimum finding, one pick of X costs Θ(√(|X| n)) queries. On a chain, where the supernode grows by one vertex per step, the picks then cost Θ(n²) in total. The new ingredient is to keep the minima of the columns of X in a sorted form that the picks never have to recompute.

**Order invariance (Lemma 1).** Let C be a set of columns inside a supernode X, and set key_C(u) = min over v ∈ C, v ≠ u, of W[u][v] − off[v], with the offsets taken at one time t. After t, offsets change only when a supernode that contains C picks, and that change is the same for all of C. So at every later time, the current minimum of row u over C equals key_C(u) − Δ, where Δ does not depend on u. The order of the rows by key_C never changes, and rows only ever leave the candidate set, by joining X.

**Groups.** The columns of each supernode are split into groups. The class of a group of size s is ⌊log₂ s⌋. When a supernode A absorbs a supernode B with |A| ≥ |B|:

1. the groups of B, together with the groups of A of size at most |B|, are merged into one new group;
2. then two groups of the same class are merged, again and again, until the classes are distinct.

A cycle of several supernodes is merged by absorbing them one by one into the largest. Every supernode has at most ⌊log₂ n⌋ + 1 groups.

**Batches.** A group g with column set C, of size s, hands out rows in increasing order of key_C, skipping the rows inside its supernode X, in batches of sizes 1, 2, 4, and so on. A batch of b rows is the b rows of least key_C among the rows outside X that g has not handed out yet.

- It is found with the k-minimum finding of [1] over the n rows. Each key is evaluated by minimum finding over s columns.
- The cost is O(√(n b s)) queries per batch, up to a logarithmic factor that reduces the error of the inner calls.
- Rows of the current batch that have joined X are dropped. The head of g is the first row that remains, and a new batch is fetched only when the current one is empty.
- The pick of X compares the heads of its groups by key_C(u) − Δ_g, which is classical work. It then finds the column of the chosen row by minimum finding over C, at a cost of O(√n), and reads one entry.

**Correctness.** Each batch is a prefix of the order by key_C among the rows outside X, and that order is fixed (Lemma 1). So the head of g is the row of least key_C outside X, and the least head over the groups gives the arc picked by [2, 3].

## The count

**Lemma 2 (each vertex lies in few groups).** Over the whole run, every vertex lies in at most 2⌊log₂ n⌋ + 2 groups, so the sizes of all groups ever formed sum to at most n(2 log₂ n + 2).

*Proof.* Follow the group of a vertex v. A new group containing v arises in one of three ways:

- (a) v's supernode is the smaller side B of an absorption. The new group has at least |B| elements, which is at least the size of v's old group. The supernode of v at least doubles, so this happens at most log₂ n times.
- (b) v's group lies in A and has size s ≤ |B|. The new group has at least |B| + s ≥ 2s elements.
- (c) v's group is merged with a group of the same class k. The result has at least 2^{k+1} elements.

The class of v's group never decreases, and it rises strictly in (b) and (c). Classes lie in 0, …, ⌊log₂ n⌋. ∎

**Lemma 3 (few deletions).** A row u is dropped from batches at most (⌊log₂ n⌋ + 1)·log₂ n times over the run.

*Proof.* A row u in a batch of g is dropped only after u has joined the supernode X of g. That happens when the supernode B of u is absorbed into a supernode A that contains g. Here B is the smaller side, which happens at most log₂ n times for u. The group g already existed, since it had handed out u, and A had at most ⌊log₂ n⌋ + 1 groups at that moment. ∎

**Lemma 4 (doubling).** If g drops d_g rows over its life, it hands out h_g ≤ 2d_g + 1 rows, and its batches cost O(√(n s_g h_g)) in total.

*Proof.* A new batch is fetched only when every row of the previous batches has been dropped. If the batches have sizes 1, 2, …, 2^t, the first t of them hold 2^t − 1 ≤ d_g rows. The cost is a geometric sum dominated by its last term. ∎

The consumed row of a pick stays in its batch. Its supernode is either finished, or it is merged into the next supernode of the group, and then the row is dropped as in Lemma 3.

*Proof of Theorem 1.* By the Cauchy-Schwarz inequality, Lemmas 2 to 4 give Σ_g √(n s_g h_g) ≤ √(n · Σ_g s_g · Σ_g h_g). Here

- Σ_g s_g = O(n log n), by Lemma 2;
- Σ_g h_g ≤ 2 Σ_g d_g + #groups = O(n log² n), by Lemmas 2 and 3.

So the batches cost O(n^{3/2} log^{3/2} n). The 2n − 1 picks add O(n^{3/2}). There are polynomially many inner calls, and reducing each to error 1/n³ adds a factor O(log n), so the failure probability stays below 1/3. If some head finds no finite arc into X, no arborescence exists. ∎

## Scripts

All scripts are in `sim/` and run with Python 3 and networkx, using fixed seeds. Each asserts that the weight of the computed arborescence equals the optimum from networkx, for n ≤ 129.

- `contraction_cost.py`: path-growing contraction with plain minimum finding per pick. On random digraphs the cost is about n^{3/2}. On the chain family it is about 0.5 n².
- `lsm_cost.py`: the algorithm of Theorem 1, on six families: random, chain, a hierarchical family, symmetric random, and chains of blocks of size 2 and 8. It asserts the following.
  - At most 2 log₂ n + 2 groups per vertex (Lemma 2).
  - At most (log₂ n + 1) log₂ n drops per row (Lemma 3).
  - h_g ≤ 2d_g + 1 plus the final batch (Lemma 4).
  - At most 2n − 1 picks.

  Up to n = 257, the cost divided by n^{3/2}(log₂ n + 1)² stays below 1.21 on every family.
- `grouped_cost.py`, `hard_families.py`, `big_n.py`, `hill_adv.py`: a variant with plain binomial merging, block chains up to n = 513, and a hill-climbing search for weight matrices of high cost (n ≤ 96). On these, the cost stays near n^{3/2} log² n.

## Not formalized

Theorems and lemmas above are a written proof (Claim). The k-minimum finding of [1], its composition with inner minimum finding, and the correctness of the contraction algorithm [2, 3, 4] are used as known results.

## References

1. C. Dürr, M. Heiligman, P. Høyer, M. Mhalla. Quantum query complexity of some graph problems. SIAM J. Comput. 35(6), 2006. arXiv:quant-ph/0401091.
2. J. Edmonds. Optimum branchings. J. Res. Nat. Bur. Standards 71B, 1967.
3. Y. J. Chu, T. H. Liu. On the shortest arborescence of a directed graph. Scientia Sinica 14, 1965.
4. R. E. Tarjan. Finding optimum branchings. Networks 7, 1977.
5. H. N. Gabow, Z. Galil, T. Spencer, R. E. Tarjan. Efficient algorithms for finding minimum spanning trees in undirected and directed graphs. Combinatorica 6, 1986.
6. P. A. Kerger, D. E. Bernal Neira, Z. Gonzalez Izquierdo, E. G. Rieffel. Mind the Õ: asymptotically better, but still impractical, quantum distributed algorithms. arXiv:2304.02825.

## Use of AI

The algorithm, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
