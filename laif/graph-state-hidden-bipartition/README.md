# Learning graph states with a hidden bipartition: O(d log n) copies in three adaptive rounds for almost every graph of the hard distribution

2026-11-24

## Problem

The setting is the one of [1]. A learner receives N copies of an unknown n-qubit graph state |G⟩ and measures every qubit of every copy in the X, Y or Z basis. An adaptive learner may choose the setting of each copy from the outcomes of earlier copies. B_{n,d} is the class of connected bipartite d-regular graphs on [n] of diameter at most D_n = ⌈16 ln n / ln ln n⌉, in the range ⌈ln n⌉ ≤ d and d³ ln n ≤ n. The bipartition of the target is not given.

In [1, Section 5] a distribution π_B on B_{n,d} is used for the nonadaptive lower bound: n = 2m, a uniformly random balanced partition L ⊔ R, d independent uniform bijections L → R, conditioned on the event E that their edges are pairwise disjoint and that two expansion properties hold [1, Lemma 19]. Then P(E) ≥ e^{−d²}/2.

| learner | copies to identify G |
|---|---|
| nonadaptive X/Y/Z, on B_{n,d} and on π_B [1, Theorem 2] | Θ(d² log n) |
| adaptive X/Z, breadth-first, on B_{n,d} [1, Theorem 14] | O(d log² n / log log n), with D_n + 1 adaptive rounds |
| any adaptive Pauli learner, bipartition revealed [1, Proposition 15] | Ω(d log n) |
| Theorem 1: adaptive X/Z, almost every graph of π_B | O(d log n), with three adaptive rounds |

## Result

**Theorem 1.** There are absolute constants k and n₀ such that for n ≥ n₀ in the range above the following holds. There is an adaptive X/Z learner with three adaptive rounds and (k + 2) b copies, where

b = ⌈log₂((k + 2) n Q / δ)⌉,  Q = Σ_{j ≤ d} C(n − 1, j) ≤ (en/d)^d,

so O(d log n + log(1/δ)) copies, and a set 𝒢 of graphs with π_B(𝒢) = 1 − o(1), such that for every G ∈ 𝒢 the learner outputs G with probability at least 1 − δ − o(1).

**Corollary 2.** On π_B the adaptive cost is Θ(d log n), in the following sense: Theorem 1 gives O(d log n) copies on a set of graphs of measure 1 − o(1), and every adaptive Pauli learner that is correct with probability at least 2/3 on a set of measure 1 − o(1) needs Ω(d log n) copies. The lower bound is that of [1, Proposition 15], which applies to π_B since every graph in its support is connected and so determines its bipartition. On the same distribution every nonadaptive learner needs Ω(d² log n) copies [1, Theorem 2], so adaptivity gains the full factor d there.

For the worst case over B_{n,d}, the adaptive rate remains open, as stated in [1, Section 7]. Theorem 1 does not address it.

## Learner

- **Round 1.** For j = 1, …, k, draw R_j, with every qubit in it independently with probability p = 1/(4d). On b copies, measure X on R_j and Z elsewhere. For every v ∈ R_j, keep the sets Γ ⊆ [n] \ R_j with |Γ| ≤ d that satisfy s_v = Σ_{u ∈ Γ} t_u on all b copies, where s and t are the X and Z outcome bits. If exactly one remains, it is taken as N(v). These k settings do not depend on any outcome, so they form one round.
- **Round 2.** Take the largest component C of the graph of learned edges with its 2-colouring. Measure X on the unlearned vertices of a colour class of C that has some, and Z elsewhere, on b copies. Recover their neighbourhoods.
- **Round 3.** Recompute C, which now contains a whole side, and do the same for the unlearned vertices of that side. Every edge has an endpoint on that side.

## Proof

Write N2(U) = N(N(U)), and call v ∈ W clean if no neighbour of v lies in W.

**Lemma 1 (one setting).** Fix the set W measured in X, with Z elsewhere. If v ∈ W is clean, N(v) passes every copy, and a wrong Γ passes each copy with probability 1/2. If v is not clean, every Γ passes each copy with probability 1/2. By [1, Lemma 4] the outcome is uniform on an affine space whose constant linear functionals are a·s + (Bᵀa)·t with a ∈ ker A[W, W] and B = A[W, U]. The functional s_v + 1_Γ·t is of this form only for a = e_v, which lies in the kernel exactly when v is clean, and then 1_Γ = 1_{N(v)}. A nonconstant affine functional on a uniform affine space over F₂ is a fair coin. With b copies, all decisions of a round are correct except with probability at most nQ2^{−b}. So each round learns exactly its clean vertices.

**Lemma 2 (sampling).** Let S be the set of vertices learned in round 1 and S_A = S ∩ A for a side A, with B the other side. For disjoint T, X ⊆ A with |T| = s,

P(T ⊆ S_A and S_A ∩ X = ∅) ≤ (kp)^s 2^k exp(−3k|X|/(32d)).

Condition on the sets R_j ∩ B. Then a vertex v ∈ A lies in S_A independently of the other vertices of A, with probability 1 − (1 − p)^{w(v)} ≤ kp, where w(v) counts the rounds j with N(v) ∩ R_j = ∅. The number Y_j of x ∈ X with N(x) ∩ R_j = ∅ is at least |X| − K_j, where K_j = Σ_b 1[b ∈ R_j] |N(b) ∩ X| has mean |X|/4 and weights at most d. The inequality of [2] gives P(K_j ≥ |X|/2) ≤ exp(−3|X|/(32d)), so E(1 − p)^{Y_j} ≤ 2 exp(−3|X|/(32d)).

**Graph properties.** Let k = 2048, γ = k/(256 ln(kd)), s₁ = ⌊γm/d⌋, μ = (64/(3k)) d (ln(ekd) + 2) and L = ln(m/(2d²)). With probability 1 − o(1) under π_B, on both sides:

- (P1) |N2(x)| ≥ d²/2 for every vertex x;
- (P2) |N2(U)| ≥ μ|U| for every U on one side with 3d/L ≤ |U| ≤ s₁;
- (P3) N(U) ∩ N(Z) ≠ ∅ for all disjoint U, Z on one side with |U| = |Z| = s₁.

Each failure probability is bounded in the model of independent bijections and is o(e^{−d²}), so it survives the conditioning on E. Fix U ⊆ L. Given the images π_i(U), each π_i maps L \ U uniformly onto R \ π_i(U), independently over i. So N2(U) is U together with d independent uniformly random subsets of L \ U of size |N(U)| − |U|. Also P(|N(U)| < y) ≤ C(m, y)(y/m)^{d|U|}. For (P2) take y = d|U|/10, and for (P3) take y = γm/4. For (P3), given the images of U, each π_i(Z) is a uniform s₁-subset of R \ π_i(U), and avoiding N(U) has probability at most (1 − (|N(U)| − s₁)/m)^{s₁}. The resulting bounds are

- (P1) exp(−(d²/2 − d) ln(2m/d²) + d²/2) per vertex;
- (P2) exp(−d|U|(0.9 ln(10m/(d|U|)) − 0.1)) + C(m, μ|U|)(μ|U|/m)^{d²|U|/20}, against the count C(m, |U|);
- (P3) 2 C(m, s₁)² max{exp(−γm((3/4) ln(4/γ) − 1/4)), exp(−γ²m/5)}.

`sim/exponents.py` evaluates every bound of the proof, with the conditioning factor and the union counts, in log space over the range of n and d, and checks that each is negative.

**Lemma 3 (connectivity).** With probability 1 − o(1), the graph on S_A in which two vertices are adjacent when they share a neighbour is connected.

- A component T of size s is connected in the graph Γ₂ on A with these adjacencies, whose degree is below d². It satisfies T ⊆ S_A and S_A ∩ (N2(T) \ T) = ∅.
- There are at most m(ed²)^{s−1} such sets T. By Lemma 2 the expected number of components of size s ≤ s₁ is at most m 2^k (ekd/4)^s exp(−3k f(s)/(32d)), where f(s) is the least value of |N2(T) \ T|.
- By (P1), f(s) ≥ d²/2 − s, and by (P2), f(s) ≥ (μ − 1)s for s ≥ 3d/L. In each range of s this makes the term at most e^{−s−k} n^{−2}, so components of size at most s₁ have probability o(1).
- Conditionally on the sets R_j ∩ B, |S_A| ≥ km/(32d) ≥ 2s₁ except with probability o(1).
- A component T with s₁ < |T| ≤ |S_A|/2 would leave Z = S_A \ T with |Z| ≥ s₁ and N(T) ∩ N(Z) = ∅, against (P3).

**Lemma 4 (coverage).** With probability 1 − o(1), every vertex a has a vertex of S in N2(a). By Lemma 2 with T = ∅, X = N2(a) and (P1), this fails at a given a with probability at most 2^k e^{−3kd/64}.

**Proof of Theorem 1.**

- *Components after the k rounds.* Every edge of the learned graph has an endpoint in S. By Lemma 3 for both sides, its nontrivial components are the component of S_A, which contains S_A ∪ N(S_A), and the component of S_B. They may coincide.
- *Round 2.* If the two components are distinct and C is the component of S_A, its A-class is S_A, which is learned, and its B-class is N(S_A), so round 2 measures X on N(S_A) \ S. The case of S_B is symmetric. If they coincide, round 2 measures one class, say the B-class, which contains N(S_A). In each case, after round 2 every vertex of N(S_A) is learned (say), and every a ∈ A has a neighbour in N(S_A) by Lemma 4, so all of A lies in the new C.
- *Round 3.* The A-class of the new C is all of A. Its B-class contains only learned vertices: the vertices of B learned so far are S_B and those learned in round 2, and every unlearned vertex of the B-class would be a neighbour of a learned A-vertex, that is, of S_A, all of whose neighbours were learned in round 2. So the only class with unlearned vertices is A, and round 3 learns all of A. If no class has unlearned vertices, every vertex is learned and the learner stops.
- *End.* After round 3 a whole side is learned, so every edge is known.
- *Independence.* Each set measured in X in rounds 2 and 3 lies in one colour class of a component, hence in one side, so Lemma 1 applies to all its vertices.
- *Failure probability.* The k + 2 settings fail with probability at most δ, and the events of Lemmas 3 and 4 fail with probability o(1).

## Check

`sim/lemma1.py` checks Lemma 1 on state vectors: for n = 10 and six random sets W, the true neighbourhood of every clean vertex passes all shots, and every other candidate, at clean and non-clean vertices, passes a fraction of the shots between 0.4 and 0.6.

`sim/learner.py`, output in `sim/out_learner.txt`, runs the learner at the level of Lemma 1: clean vertices are learned and the others are not. Graphs are unions of d random bijections, with collisions removed by random swaps; this approximates π_B and is not the conditioned law.

- With p = 1/(4d) and k = 8, it succeeds on 10 out of 10 graphs for each of (n, d) = (2000, 8), (8000, 9), (20000, 10).
- The events of Lemmas 3 and 4 hold in all these runs.

`sim/exponents.py`, output in `sim/out_exponents.txt`, evaluates the failure bounds of (P1) to (P3) and Lemmas 3 and 4 with the constants of the proof, for ln n ∈ {520, 600, 700} and d from ⌈ln n⌉ to the top of the range. All are negative in log space.

## Scope

- Theorem 1 is about the distribution π_B of [1], for all but a vanishing fraction of its graphs. The worst case over B_{n,d} is not covered.
- The constants are far from optimal: the argument uses k = 2048 and d ≥ 512, so n₀ is very large. In the simulations, k = 8 random settings suffice for the sizes checked.
- The learner uses exhaustive search over candidate neighbourhoods, as in [1], and takes time n^{O(d)}.
- The statements are Claims with the listed checks.

## References

1. M. De Francesco. Learning sparse graph states with local Pauli measurements: tight nonadaptive bounds and an adaptive separation. arXiv:2611.16456 (2026).
2. S. Bernstein, inequality for sums of bounded independent random variables; see S. Boucheron, G. Lugosi, P. Massart, Concentration Inequalities, Oxford University Press, 2013, Theorem 2.10.

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
