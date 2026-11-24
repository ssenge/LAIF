# Bandwidth and Distortion in polynomial space with a quantum algorithm

Written 22 Nov 2026.

Input: a graph G on n vertices. Question: the bandwidth of G, the minimum over all orderings π: V → {1, …, n} of the maximum of |π(u) − π(v)| over the edges uv.

**Theorem 1.** Bandwidth has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, in time O(3.1623^n). For every δ > 0 the same algorithm with a larger constant depth runs in time O((√10 + δ)^n), and √10 = 3.16227….

Status: Claim. Assuming the bucket-assignment method of [1] as restated in [2, Section 4.1], and using quantum search [3] and reversible simulation [4] as stated. The reduction is checked against brute force and the exponent by an exact script.

Input of Distortion: a connected graph G on n vertices. Question: the minimum distortion of a non-contracting embedding of the shortest-path metric of G into the line, the minimum over all maps π: V → ℤ with |π(u) − π(v)| ≥ d_G(u, v) of the maximum of |π(u) − π(v)| / d_G(u, v).

**Theorem 2.** Distortion has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, in time O(3.1623^n), and in time O((√10 + δ)^n) for every δ > 0.

Status: Claim. Assuming the state graph of the polynomial-space algorithm of [5, Section 4] (Lemmas 4.3 and 4.8 to 4.10, and the split into instances with few segments in the proof of Theorem 4.11) and the count of [5, Lemma 2.5], and using quantum search [3] and reversible simulation [4] as stated. The state graph and the search with halving are checked against brute force on small graphs, and the count of Lemma 2.5 by brute force.

## Before and after

| Model | Previous best bound | After |
|---|---|---|
| Classical, polynomial space | O(9.363^n) [5] | |
| Classical, any space | O*(4.383^n), with exponential space [6]; O(4.83^n) with space O*(4^n) [7] | |
| Quantum, polynomial space, no quantum random access memory | | **O(3.1623^n)** |
| Quantum, exponential space with quantum random access memory | O*(2.945^n) [2, Theorem 6] | |

Theorem 1 is below every classical bound above, including those with exponential space. For large bandwidth the classical bound is smaller: the restricted algorithm of [1] decides b ≥ n/2 in time O*(2.83^n), so the gain of Theorem 1 is for b < n/2.

For Distortion:

| Model | Previous best bound | After |
|---|---|---|
| Classical, polynomial space | O(9.363^n) [5] | |
| Classical, any space | O(4.383^n), with exponential space [5]; O*(5^{n+o(n)}) with space O*(2^n) [9] | |
| Classical, parameterized by the distortion d | O(n d^4 (2d + 1)^{2d}) [10] | |
| Quantum, polynomial space, no quantum random access memory | | **O(3.1623^n)** |

Theorem 2 is below both exponential bounds. For small distortion the parameterized algorithm of [10] is faster: it wins whenever (2d + 1)^{2d} is below 3.1623^n, for example for d ≤ n/(2 log₂ n) and n large, so the gain of Theorem 2 is for larger distortion.

Related work: the quantum halving step over middle sets is the polynomial-space end of the time-space trade-offs of [8]. Theorem 1 combines it with a search over the valid pairs of [1, 2].

## 1. The algorithm

**Bucket assignments** [1], as restated in [2, Section 4.1]. A graph that is not connected is handled one component at a time, so let G be connected. Fix b and split the positions 1, …, n into k = ⌈n/(b + 1)⌉ buckets of b + 1 consecutive positions, the last one smaller if b + 1 does not divide n. An ordering of bandwidth at most b puts the endpoints of every edge into the same or adjacent buckets. Fix a spanning tree with root r. A bucket assignment σ is given by the bucket of r and an offset in {−1, 0, +1} between each other vertex and its parent, so there are at most k · 3^{n−1} of them. For a fixed σ with the right bucket sizes and no edge across two or more buckets, the positions are filled in rounds, one position per bucket in each round, and an ordering of bandwidth at most b exists if and only if there is a sequence of balanced sets ∅ = S₀ ⊂ S₁ ⊂ … ⊂ S_n = V, each adding a vertex v of the bucket of the next position such that v has no neighbour in S in the previous bucket and all its neighbours in the next bucket are in S. A set S on such a sequence is valid for σ: if the parent p of v is in S and v lies one bucket above p, then v ∈ S, and if p ∉ S and v lies one bucket below p, then v ∉ S. Given whether its parent is in S, each vertex has 5 of the 6 combinations of offset and membership, so there are exactly 2k · 5^{n−1} index tuples for pairs (σ, S) with S valid for σ [2, Section 4.1], some of which place vertices outside the buckets and are discarded by the search.

**Halving recursion.** A sequence from A to B exists if and only if there is a balanced set C with A ⊆ C ⊆ B and |C \ A| = ⌊|B \ A|/2⌋ such that sequences from A to C and from C to B exist.

**Nested search.** The top level searches the pairs (σ, S), with S valid for σ, by quantum search [3]. Their index is a choice of the root bucket, root membership and one of 5 combinations per vertex in the order of the tree, so it is computed in polynomial time. The search marks a pair if σ has the right bucket sizes and no edge across two or more buckets, S is balanced with |S| = ⌊n/2⌋, and sequences from ∅ to S and from S to V exist. The levels l = 1, …, D − 1 search the middle sets C of their interval among all subsets of B \ A of the right size, at most 2^{n/2^l} of them. At depth D the call decides the sequence classically by the same halving recursion, in time 4^m · m^{O(log m)} for an interval of m = n/2^D vertices and polynomial space, run reversibly [4] in time (4^m · m^{O(log m)})^{1+ε} and polynomial space. Each subcall is repeated in L = c · n parallel copies with a majority vote, with a constant c large enough that the error 2^{−Ω(L)} of a vote stays below the inverse of the total number of subcalls, at most 4^n, and its work is uncomputed, so the workspace of a call is at most 2L times that of a subcall plus poly(n), which is poly(n) over the constant depth D.

## 2. Analysis

The square roots of the search spaces multiply along a path of calls, and the two subcalls at each level and the copies contribute a factor (2L · O(n))^D = poly(n). The time is therefore

√(2k · 5^{n−1}) · ∏_{l=1}^{D−1} 2^{n/2^{l+1}} · 4^{(1+ε) n/2^D} · 2^{O(log² n)} = 10^{n/2} · 2^{(1+2ε) n/2^D} · 2^{O(log² n)},

since the exponents of the middle levels sum to n(1/2 − 1/2^D). With D = 17 and ε = 1/10, √10 · 2^{(1+2ε)/2^D} < 3.1623, so the time is O(3.1623^n), where the strict inequality absorbs the subexponential factors. As D grows the bound tends to 10^{n/2}. The binary search over b adds a factor O(log n). The space is polynomial.

## 3. Distortion: Theorem 2

**The state graph** [5, Section 4]. A non-contracting embedding of minimum distortion may be taken pushing: in the order of the positions, consecutive vertices u, v satisfy π(v) − π(u) = d_G(u, v), and then the distortion is the longest edge [5, Lemma 4.2]. Fix d, so the positions are 1, …, n(d + 1), split into segments of d + 1 consecutive positions. The colour of a position is its offset in its segment, and the colour order sorts positions by colour, then by segment. A pushing embedding has distortion at most d if and only if the endpoints of every edge lie in the same or adjacent segments and, across adjacent segments, the endpoint in the later segment comes earlier in the colour order [5, Lemma 4.3]. A state (p, (A, f), (H, h)) records that the first p positions of the colour order are processed: A is the set of placed vertices, f its segments (a partial bucket function as in Section 1), and h the position of the last placed vertex of each segment. A step processes position p + 1, leaves it empty or places one vertex there, and checks the pushing condition inside its segment. The guessed first vertex and position of every segment close the chain across segments in the final state. For r segments, an embedding of distortion at most d exists if and only if some guess has a path of states from the empty state to a final state [5, Lemmas 4.8, 4.9].

**Few segments.** For r ≥ n/log³ n segments, the proof of [5, Theorem 4.11] guesses two adjacent segments with at most 4 log³ n vertices in total and their positions, n^{O(log³ n)} guesses, and splits the instance into two independent instances on the two sides, with the guessed vertices fixed on the boundary. Repeated to depth O(log n), this leaves instances with r < n/log³ n segments. The guesses are enumerated classically around the quantum algorithm below, which costs a factor n^{O(log⁴ n)} in total; the run times of the two independent instances of a guess add, and their vertex counts sum to at most n. Each quantum run is repeated O(log⁵ n) times with a majority vote, so all answers are correct with probability at least 2/3.

**Nested search.** For an instance on n̂ vertices with r < n/log³ n segments, the top level searches, by quantum search [3], the triples of a middle state with |A| = ⌊n̂/2⌋ and a final state whose segment function is a bucket extension of that of the middle state, together with the guesses of the first vertices, the index p and the maps h of both states. By [5, Lemma 2.5] there are at most 2r · 5^{n̂−1} such pairs of segment functions for a connected graph. On an instance with fixed boundary vertices, each component of the remaining graph has a vertex next to the boundary, whose segment is then 1 or r, so the root of each component has at most 4 choices of segment and membership instead of 2r, and the bound is at most 5^{n̂}. The guesses, p and the maps h add a factor n^{O(r)} = 2^{O(n/log² n)}. The levels below search the middle states of the halving recursion of [5, Lemma 4.10]: at most 2^m subsets of the vertices of the interval, O(n²) values of p and n^{O(r)} maps h for an interval of m vertices. At constant depth D the classical halving recursion of [5, Lemma 4.10] decides the path in time 4^m · n^{O(r log m)} and polynomial space, run reversibly [4]. The copies, majority votes and uncomputation are as in Section 1.

**Analysis.** The factors n^{O(r)} of the D levels and n^{O(r log m)} of the leaves give at most 2^{O(D n / log n)}, which is subexponential. The rest is the product of Section 2 with 5^{n̂} at the top, so an instance takes time 10^{n̂/2} · 2^{(1+2ε) n̂/2^D} · 2^{o(n)}, which is O(3.1623^{n̂}) for D = 17 and ε = 1/10 by the inequality checked in Section 4. The searches over d (at most 2n − 1, as recalled in [5]) and r add a factor poly(n), and the space is polynomial.

## 4. Measurements

`sim/bandwidth.py`:
- implements the bucket-assignment reduction of Section 1 with the halving recursion, checks that every top-level middle set it uses is valid for σ in the sense of Section 1, and compares the bandwidth it finds with brute force over all orderings on 137 random connected graphs with 2 to 7 vertices;
- counts the locally valid combinations per vertex, 5 of 6;
- checks √10 · 2^{(1+2ε)/2^D} < 3.1623 for D = 17 and ε = 1/10 in exact rational arithmetic, with ln 2 < 0.6932 and 2^x ≤ 1/(1 − x ln 2).

`sim/distortion.py`:
- implements the state graph of Section 3 with the guesses of the first vertices and compares the answer for every d up to the optimum plus one with brute force over all vertex orders on 60 random connected graphs with 2 to 5 vertices;
- runs the top-level search over pairs of a middle state and a final state with the halving recursion and compares it with the state graph on 113 pairs of a graph with at most 4 vertices and a value of d;
- counts the triples of [5, Lemma 2.5] by brute force on 40 random connected graphs with at most 5 vertices and at most 4 segments, and checks the bound 2N · 5^{n−1}.

Run them with `python bandwidth.py` and `python distortion.py` in `sim/`. Each exits nonzero on a failed check.

## 5. Limits

- The reduction of [1] is used as restated in [2], where b + 1 divides n; the smaller last bucket is our extension, and the script checks it and the reduction on small graphs only.
- The bound counts all 2k · 5^{n−1} valid pairs at the top level and all subsets of the right size below it, with no gate count.
- The polynomial factors and the constant 2^{O(D)} are not evaluated.
- For b ≥ n/2 the classical algorithm of [1] in time O*(2.83^n) is faster.
- For Distortion, the split into instances with few segments, the state graph and the count are used as stated in [5]; the scripts check the state graph and the search with halving on graphs with at most 5 and 4 vertices, and not the split, which only acts for r ≥ n/log³ n.
- For distortion d with (2d + 1)^{2d} < 3.1623^n, the classical algorithm of [10] is faster.

## References

1. M. Cygan, M. Pilipczuk. Faster exact bandwidth. WG 2008.
2. A. Ambainis, K. Balodis, J. Iraids, M. Kokainis, K. Prūsis, J. Vihrovs. Quantum speedups for exponential-time dynamic programming algorithms. arXiv:1807.05209.
3. L. K. Grover. A fast quantum mechanical algorithm for database search. STOC 1996.
4. C. H. Bennett. Time/space trade-offs for reversible computation. SIAM Journal on Computing 18(4), 1989.
5. M. Cygan, M. Pilipczuk. Bandwidth and distortion revisited. Discrete Applied Mathematics 160, 2012. arXiv:1004.5012.
6. M. Cygan, M. Pilipczuk. Exact and approximate bandwidth. Theoretical Computer Science 411(40), 2010.
7. M. Cygan, M. Pilipczuk. Even faster exact bandwidth. ACM Transactions on Algorithms 8(1), 2012. arXiv:0902.1661.
8. S. Caroppo, J. Vihrovs, D. Zajakina, A. Zajakins. Quantum time-space tradeoffs for exponential dynamic programming. arXiv:2604.02233.
9. F. V. Fomin, D. Lokshtanov, S. Saurabh. An exact algorithm for minimum distortion embedding. Theoretical Computer Science, 2011.
10. M. R. Fellows, F. V. Fomin, D. Lokshtanov, E. Losievskaja, F. A. Rosamond, S. Saurabh. Distortion is fixed parameter tractable. ICALP 2009.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check the analysis, to write the simulation scripts, and to draft the text.
