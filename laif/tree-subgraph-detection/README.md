# Detecting trees with three branching path vertices in linear quantum queries

Written 11 Nov 2026.

**Setting.** G is a graph on n vertices, given by its adjacency matrix: a query (u, v) returns whether uv is an edge. For a fixed graph T, the subgraph detection problem asks whether G contains T as a subgraph (not necessarily induced). Every T with an edge needs Ω(n) quantum queries, by search on n² cells [1, Prop. 4].

| | Trees T | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | A path p_1, …, p_k with any numbers of leaves attached to three consecutive path vertices p_i, p_{i+1}, p_{i+2} | O(n) if T has at most one vertex of degree 3 or more [1, Thm 14], Õ(n) if T has diameter at most 4 (implied by [2, Thm 4.5]); otherwise Õ(n^{3/2 − 1/(vc(H′)+1)}) with H′ = T minus its leaves [2, Thm 4.5], for example n^{7/6} | Θ(n), with \|T\|^{O(\|T\|)} · n queries | Window lemma and copy construction in Lean; witness sizes and the span program bound of [3] are a claim |

The new cases are the trees of this class with at least two vertices of degree 3 or more and diameter at least 5. The smallest is the path on six vertices with one extra leaf at each of its two middle vertices (8 vertices). The class also contains paths with leaves at p_i and p_{i+2} only. To our knowledge, the only trees with linear quantum query complexity known before are paths, subdivided claws and stars with two subdivided legs [1], and trees of diameter at most 4, up to a logarithmic factor [2]. Every tree has an O(n) algorithm under the promise that G either contains T or does not contain T as a minor [4]; Thm 1 needs no promise.

## 1. The reduction

Fix k ≥ 3, 1 ≤ i ≤ k − 2 and leaf numbers d_i, d_{i+1}, d_{i+2}, and let D be their sum, so |T| = k + D. Colour the vertices of G independently and uniformly by the vertices of T. A copy φ of T is *correctly coloured* if every vertex φ(t) has colour t. Each copy is correctly coloured with probability |T|^{−|T|}.

**The graph G′.** Its nodes are s, t, one node for every vertex of G with a path colour, and private chain nodes. Free edges join s to the vertices of colour p_1, and the vertices of colour p_k to t. For every pair (x, y) of vertices with colours p_j and p_{j+1} there is a private chain of edges in series from x to y:

    x → B(x, ℓ) for each leaf ℓ at p_j → [edge labelled xy] → B(y, ℓ′) for each leaf ℓ′ at p_{j+1} → y.

A bundle B(z, ℓ) is a set of parallel edges, one for each vertex u of colour ℓ, labelled zu. An edge labelled ab is present in G′(G) iff ab is an edge of G. So the chain from x to y is connected iff xy is an edge, x has a neighbour of every leaf colour at its position, and so does y. Chain nodes have no other edges.

**Lemma 1 (walks).** A simple path from s to t in G′(G) passes through whole chains. It gives vertices x_1, …, x_r of G, pairwise distinct, with consecutive ones adjacent, whose colour positions c_1, …, c_r satisfy c_1 = 1, c_r = k and |c_{p+1} − c_p| = 1, and every x_p has a neighbour of each leaf colour at position c_p.

Such a path may go back and forth between neighbouring colours. The next lemma finds a stretch of it that behaves like a path through the colours in order.

**Lemma 2 (first arrival).** Let c_1 = 1, c_r = k, |c_{p+1} − c_p| = 1, and 3 ≤ q ≤ k. Let τ be the first index with c_τ = q. Then c_{τ−1} = q − 1, c_{τ−2} = q − 2, τ ≥ q and r − τ ≥ k − q.

*Proof.* All colours before τ are below q, since the sequence starts at 1 and moves by one. So c_{τ−1} = q − 1, and c_{τ−2} is q − 2 or q, where q is excluded. The two inequalities hold because each step moves by one. ∎

**Lemma 3 (copies).** If s and t are connected in G′(G), then G contains T.

*Proof.* Take the walk of Lemma 1, q = i + 2, and y_j = x_{τ−q+j} for j = 1, …, k. The indices lie in 1, …, r by Lemma 2. The y_j form a path in G, and y_i, y_{i+1}, y_{i+2} have colours p_i, p_{i+1}, p_{i+2}. By Lemma 1 each of these three has a neighbour of every leaf colour at its position. All leaf colours differ from each other and from the path colours, so these neighbours are distinct and lie off the path. Together they form a copy of T. ∎

Conversely, a correctly coloured copy of T gives a path from s to t through k vertex nodes and k − 1 chains, of length k + 1 + 2D at most, since each leaf bundle lies in two chains.

## 2. Query bound

**Theorem 1.** For every tree T in the class above, detecting T as a subgraph takes Θ(n) quantum queries.

*Proof.* The st-connectivity span program of [1] on a multigraph whose edges carry input labels, several edges possibly with the same label and some edges free, decides connectivity with O(√(W₊ W₋)) queries, where W₊ is the largest effective resistance R_st over the positive inputs and W₋ the largest cut value C_st = min over cuts κ of Σ_e |κ(u) − κ(v)| over the negative inputs [3, Thm 10 and eq. (8)]. A label shared by several edges and a free edge are allowed by the general span program setting of [1, Section 2], where one input variable may label a set of input vectors and the bound holds for partial functions.

Run it on G′ for one colouring, as a promise problem: positive inputs have a correctly coloured copy, negative inputs contain no copy of T. On a positive input the copy's path gives R_st ≤ k + 1 + 2D.

On a negative input, G has at most (|T| − 2) n edges: a graph without T has a vertex of degree at most |T| − 2 in every subgraph, since minimum degree |T| − 1 embeds every tree on |T| vertices greedily. Let κ be 1 on the vertex nodes reachable from s and 0 on the others; κ(t) = 0 by Lemma 3. A chain whose ends have the same value gets that value throughout. A chain whose ends differ is not connected. Cut it at its edge labelled xy if xy is not an edge of G, at cost 1, and otherwise at a bundle with no present edge, at cost at most n. This cut separates no present edge, so C_st ≤ n² + n · |E(G)| ≤ (|T| − 1) n².

So one run costs O(√((k + 1 + 2D)(|T| − 1)) · n) = O(|T| n) queries. Repeat for O(|T|^{|T|}) independent colourings, with the error of each run reduced to O(|T|^{−|T|}) at a factor O(|T| log |T|), and accept if some run accepts. The total is |T|^{O(|T|)} · n, which is O(n) for fixed T. If G contains T, some colouring is correctly coloured with constant probability, and every run on an input outside the promise answers about a graph that contains T, so acceptance is correct. If G has no copy, every run is on a negative input. The lower bound is [1, Prop. 4]. ∎

## Lean

`lean/TreeDetect/Window.lean`, built against Mathlib, standard axioms only (`lean/axioms.txt`):

- `exists_hit`, `first_arrival`: Lemma 2 for colour sequences with steps of exactly one.
- `window`: the start index a with a + k − 1 ≤ r and exact colours at a + i, a + i + 1, a + i + 2.
- `tree_copy`: Lemmas 1 to 3 at the level of G. An injective walk with these colours and leaf neighbours gives an injective homomorphism of the tree `tree k i d` into G.

**Not formalized:** the span program bound of [3] and its witness sizes (resistance and cut value of G′), the degeneracy bound for T-free graphs, and colour coding. The span program bound is taken from [1, 3].

## Scripts

`sim/check_caterpillar.py` builds G′ explicitly. On random graphs with up to 11 vertices and six shapes of T it checks that s and t are connected only if G contains T, that a correctly coloured copy connects them with R_st within the bound, and that the minimum cut stays within the cut bound above. It also builds random back-and-forth walks with shared leaves for three-position shapes, including leaves at p_i and p_{i+2} only, and checks that each contains T.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the Lean files and the check script, and to draft the text.

## References

1. A. Belovs, B. W. Reichardt. Span programs and quantum algorithms for st-connectivity and claw detection. ESA 2012. arXiv:1203.2603.
2. A. M. Childs, R. Kothari. Quantum query complexity of minor-closed graph properties. SIAM J. Comput. 41(6), 2012. arXiv:1011.1443.
3. S. Jeffery, S. Kimmel. Quantum algorithms for graph connectivity and formula evaluation. Quantum 1, 26 (2017). arXiv:1704.00765.
4. G. Wang. Span-program-based quantum algorithm for tree detection. arXiv:1309.7713.
