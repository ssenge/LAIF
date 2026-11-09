# Graph colouring in polynomial space with a quantum algorithm

Written 7 Nov 2026, corrected 9 Nov 2026.

**Paper:** [`paper/main.pdf`](paper/main.pdf), with its source in [`paper/`](paper/). It also covers [domination problems](../quantum-dominating-set/) and [monotone local search](../quantum-monotone-local-search/), including its [approximate form](../quantum-approximate-monotone-local-search/).

Input: a graph G on n vertices and a number k. Output: whether G has a proper colouring with k colours.

**Theorem 1.** 4-Colouring has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time O*(1.6981^{n/2}) ⊂ O(1.3032^n). With the branching algorithm of [8] alone, the time is O*(1.7159^{n/2}) ⊂ O(1.3100^n).

**Theorem 2.** For the values of k in the table below, k-Colouring has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in the time of the table.

Status: Claim. The arithmetic of the rows k = 4 and 5 is in Lean. The rows k = 6 to 18 are an upper-bound computation in floating point, with a margin far above its rounding error. The weights of Theorem 1 are checked in exact decimal arithmetic, its tree is run on small graphs, and the recursion behind the table is checked against brute force on small graphs.

## Before and after

All rows are for bounded error, polynomial space and no quantum random access memory. Each value is rounded up.

| k | Before [1] | With [8] alone | After, with [8] and [9] |
|---|---|---|---|
| 4 | 1.3231^n | 1.3100^n | 1.3032^n |
| 5 | 1.4695^n | 1.4578^n | 1.4518^n |
| 7 | 1.6511^n | 1.6418^n | 1.6369^n |
| 8 | 1.6585^n | 1.6481^n | 1.6427^n |
| 9 | 1.7460^n | 1.7383^n | 1.7343^n |
| 10 | 1.7775^n | 1.7679^n | 1.7629^n |
| 11 | 1.7775^n | 1.7726^n | 1.7726^n |
| 13 | 1.8499^n | 1.8442^n | 1.8413^n |
| 14 | 1.8580^n | 1.8531^n | 1.8503^n |
| 15 | 1.9303^n | 1.9225^n | 1.9183^n |
| 16 | 1.9303^n | 1.9226^n | 1.9201^n |
| 17 | 1.9303^n | 1.9242^n | 1.9217^n |
| 18 | 1.9366^n | 1.9279^n | 1.9233^n |

For k = 3, 6, 12, 19 and 20 the bounds of [1] stand. These are best known upper bounds in this model, to our knowledge, and not tight ones. Algorithms with quantum random access memory are outside this model; with it, [7] solves graph colouring for every k in O(1.7956^n).

**Prior work.** The classical 3-colouring algorithm in O*(1.3289^n) is from [3]. The classical 4-colouring algorithm in O(1.7159^n) and polynomial space is from [8]. The terminal algorithms used below, and the weights of the analysis in this form, are from [9], whose running times O*(1.3204^n) and O*(1.6975^n) use dynamic programming over decompositions and so exponential space. The square root of the time of [3] by quantum search is from [4], with the details in Lemma 6 of [1]. The reductions from k-colouring to smaller k are from [6], and their quantum form with size limits, Theorem 9 of [1], is the tool used here. To our knowledge, what is new is the quantum form of [8], its combination with the polynomial-space terminal algorithms of [9], and the bounds for larger k that follow.

## 1. Theorem 1

An instance is P = (G, I, S), where I is an independent set with colour 4, S ⊇ N(I) is disjoint from I with colours 1, 2, 3, and U = V − I − S is free. It is terminal if every component of G[U] is a K₃ or a K₄, with n₃ and n₄ such components. The measure of [8] is

    μ(P) = ω_c |S| + ω′₃ n₃ + ω′₄ n₄ + Σ_C Σ_{v ∈ C} ω_{deg_C(v)},

over the other components C of G[U], with ω₀ = 0, ω_i = 1 for i ≥ 3, and μ(G, ∅, ∅) ≤ n.

**Branching.** A nonterminal instance is replaced by the rules of Section 3.2 of [8]. P has a colouring if and only if a child has one, |U| decreases in each child, and there is a constant number of children except on a cycle, where there is one child per maximal independent set. The tree chooses that set one vertex at a time. The constraints of [8] give Σ_j r^{μ(P_j)} ≤ r^{μ(P)} (Lemma 5.7 of [9]).

**Terminal instances.** Two maximal families of disjoint copies of K_{1,3} are computed in polynomial time, one inside G[S] with vertex set S₁, and one with centres in U and leaves in S − S₁. Then G[S − S₁] has maximum degree at most two. The terminal algorithms are:

1. Choose the vertex of colour 4 in each clique and 3-colour the rest with [3] (Lemma 5.2 of [9]).
2. Choose the colours of the centres, restrict the cliques to lists of two colours, and solve the (3,2)-constraint satisfaction instance of [3] (Lemmas 5.3 and 5.4 of [9]).
3. Enumerate the colours of S₁ and of the cliques, and solve list colouring on the paths and cycles of G[S − S₁] (Lemma 5.5 of [9]).
4. Alone, for the bound with [8]: the terminal algorithm of Section 3.1 of [8].

All of these are OR trees with polynomial work per node, in polynomial space, and the tree takes the one with the smallest stated size. With r = 1.69804, ω₁ = 0.9342533916, ω₂ = 1, ω_c = 0.5593776725, ω′₃ = 2.9704494860, ω′₄ = 3.5579545637 and multipliers η = (0.0822508347, 0.8778792406, 0.0398699247), all constraints of Lemma 5.8 of [9] hold, so the smallest terminal size is at most r^{μ(P)} up to a factor e^{o(n)}. So there are constants C and a with at most T_n = C n^a 1.6981^n nodes.

The quantum walk on backtracking trees [5], given T_n, detects a marked leaf in time √T_n poly(n), with bounded error and in polynomial space, and its running time depends only on n. Finally √1.6981 ≤ 1.3032 and √1.7159 ≤ 1.3100. A colouring follows by self-reduction: add a K₄ on four new vertices, merge one vertex at a time with one of them, and keep the first merge that leaves a 4-colourable graph. ∎

**3-colouring with the forests of [2].** The stated bound O*(1.3217^n) of [2] is not used. The linear program printed in [2] has optimum 1.32702 (Appendix F of [9]), which does not bound the running time from below. If the constraints of that program hold for the forests of [2], the same computation gives 1.1520^n for k = 3, 1.5255^n for k = 6, 1.8242^n for k = 12, 1.9574^n for k = 19 and 1.7722^n for k = 11, with the other rows unchanged. If 1.3217 itself holds, k = 3 becomes 1.1497^n.

## 2. Theorem 2

Theorem 9 of [1] turns a polynomial-space quantum 3-colouring algorithm in time O*(2^{f₃n}) into one for k-colouring in time O*(2^{d_k(1)n}), for the exponents d_k(μ) below, with d₃ = f₃ and d₁ = d₂ = 0. Here μ = u/n, where u bounds the size of each colour class. Write h for the binary entropy, logarithms to base 2.

    d_k(μ) = min( max_{1 ≤ s ≤ k} log(s)/(2s) + (1 − 1/s) d_{k−1}(1),
                  min_{2 ≤ k′ ≤ k/2} max_{δ ∈ [k′/k, min(1, μk′)]} h(δ)/2
                       + max( δ d_{k′}(min(1, μ/δ)), (1 − δ) d_{k−k′}(min(1, δ/(k′(1 − δ)))) ) ).

The first line enumerates maximal independent sets of size at least n/k, by [6] with quantum search, and colours the rest with k − 1 colours. The second guesses the union S of the k′ largest colour classes, of size δn, by quantum search, and solves G[S] and G − S, whose classes are at most |S|/k′.

An algorithm that decides 4-colourability is a correct call for k = 4 under any size limit. So the bound f₄ of Theorem 1 may replace d₄(μ) when it is smaller. Take f₃ = log(1.3289)/2 from [3], and f₄ = log(1.6981)/2, or log(1.7159)/2 for the column with [8] alone.

- **k = 5.** The first line suffices. Its term for s is at most y if s · x^{2(s−1)} ≤ y^{2s}, with x a bound on 2^{f₄}. With x = √1.6981 and y = 1.4518, and with x = √1.7159 and y = 1.4578, these are polynomial inequalities for s = 1, …, 5.
- **k = 6 to 20.** The values come from evaluating the recursion as an upper bound. The range of δ is cut into 4000 pieces [a, b]. On a piece, h(δ) is at most its maximum on [a, b], δ d_{k′}(μ/δ) is at most b d_{k′}(μ/a), and the second term is at most (1 − a) d_{k−k′}(b/(k′(1 − b))), with the limit 1 when b = 1. Every μ is rounded up to a grid of step 1/4000. The algorithm may pass these larger size limits on to its calls, since a larger limit only weakens the promise of the call, so the values bound the running time of that algorithm and are not only approximations of the recursion. A margin of 10⁻⁹ in the exponent covers the floating point error. Without f₄, the same computation gives the values of [1] to within 0.0008 in the base.

## 3. Measurements

[`fourcol_bound.py`](fourcol_bound.py) checks the weights of Theorem 1 with 60 digits and a margin of 10⁻⁹, and the parameters of Table 2 of [8] at 1.7159 ([`fourcol_bound.log`](fourcol_bound.log)).

[`fourcol_check.py`](fourcol_check.py) runs the tree ([`fourcol_check.log`](fourcol_check.log)):

| Test | Instances | Result |
|---|---|---|
| One branching step on graphs of maximum degree 4 | 27463 states, all reached cases of [8] | Σ r^{−drop} ≤ 1 in the real measure, and P is colourable if and only if a child is |
| Terminal algorithms 1, 2 and 3, with nine local lists per triangle in place of the blocks | 400 random terminal instances | all agree with brute force |
| Blocks of Lemma 5.3 of [9] | one and two triangles | every colouring is covered, within the stated bound |
| Whole tree | 300 graphs with at most 16 vertices | equal to brute force, terminal sizes add up to at most r^{μ(root)} |

The tree for 3-colouring of [3], the elimination of two-valued variables and the factor e^{o(n)} are not run.

[`bounds.py`](bounds.py) computes the table, with its output in [`bounds.log`](bounds.log). The columns there are the values of [1], the same computation with no 4-colouring step, with [8], with [8] and [9], and with the conditional base of Section 1.

[`check_reduction.py`](check_reduction.py) runs the recursion of Section 2 classically, with OR in place of quantum search, on random graphs with 5 to 9 vertices and k from 3 to 8. Its base case for k ≤ 3 respects the size limits strictly, at k = 4 it may ignore the limit as the algorithm does, and the limits passed on are kept tight or enlarged at random. With either reduction chosen at random, and with Reduction 2 only, it agrees with brute force on 300 graphs each. As a control, lowering the limit for G − S by one makes 80 of 300 answers wrong, so the test depends on the limits ([`check_reduction.log`](check_reduction.log)).

## 4. Limits

- The last column of the table uses terminal algorithms of [9], an arXiv paper. The column with [8] alone does not depend on it.
- The rules of [8] and the lemmas of [9] are used as stated there, and checked on small instances as above.
- Rows k = 6 to 18 are a floating point computation, not an interval arithmetic certificate.
- The quantum walk of [5] is used as stated.

## 5. Formal verification

The Lean library [`lean/`](lean/) is built on Mathlib and uses only the standard axioms ([`lean/axioms.log`](lean/axioms.log)).

| Theorem | Statement |
|---|---|
| `term_le` | If s · x^{2(s−1)} ≤ y^{2s}, then s^{1/(2s)} · x′^{(s−1)/s} ≤ y for every 0 ≤ x′ ≤ x |
| `row3` | √1.3289 ≤ 1.1528 |
| `row3_cond` | √1.32703 ≤ 1.1520 |
| `row4` | √1.6981 ≤ 1.3032 |
| `row4_base8` | √1.7159 ≤ 1.3100 |
| `row5` | Every term s = 1, …, 5 of the first line for k = 5 is at most 1.4518, with 2^{f₄} = √1.6981 |
| `row5_base8` | The same, at most 1.4578, with 2^{f₄} = √1.7159 |

Not formalized: the rules of [8], the terminal algorithms, the backtracking structure, the quantum walk, Theorem 9 of [1], and the rows k = 6 to 18.

## References

1. K. Shimizu and R. Mori. Exponential-time quantum algorithms for graph coloring problems. Algorithmica 84, 2022. arXiv:1907.00529. Theorem and lemma numbers refer to the arXiv version.
2. L. Meijer. 3-Coloring in time O(1.3217^n). arXiv:2302.13644, 2023.
3. R. Beigel and D. Eppstein. 3-coloring in time O(1.3289^n). J. Algorithms 54(2), 2005.
4. M. Fürer. Solving NP-complete problems with quantum search. LATIN 2008.
5. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14(15), 2018.
6. J. M. Byskov. Enumerating maximal independent sets with applications to graph colouring. Oper. Res. Lett. 32(6), 2004.
7. S. Gaspers and J. Z. Li. Quantum algorithms for graph coloring and other partitioning, covering, and packing problems. ICALP 2024. arXiv:2311.08042.
8. P. Wu, H. Gu, H. Jiang, Z. Shao and J. Xu. A faster algorithm for the 4-coloring problem. ESA 2024, LIPIcs 308, 103:1-103:18.
9. R. Yamano and T. Shibuya. Faster exact algorithms for 3- and 4-coloring: deterministic improvements and further randomized speedups. arXiv:2611.03115, 2026.
