# Graph colouring in polynomial space with a quantum algorithm

Written 7 Nov 2026.

Input: a graph G on n vertices and a number k. Output: whether G has a proper colouring with k colours.

**Theorem 1.** 3-Colouring has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in time O*(1.3217^{n/2}) ⊂ O(1.1497^n).

**Theorem 2.** For 4 ≤ k ≤ 20, k-Colouring has a quantum algorithm with bounded error, polynomial space and no quantum random access memory, running in the time of the table below.

Status: Claim. The arithmetic of the rows k = 3, 4 and 5 is in Lean. The rows k = 6 to 20 are an upper-bound computation in floating point, with a margin far above its rounding error. The recursion behind the table is checked against brute force on small graphs.

## Before and after

All rows are for bounded error, polynomial space and no quantum random access memory. Each value is rounded up.

| k | Before [1] | After |
|---|---|---|
| 3 | 1.1528^n | 1.1497^n |
| 4 | 1.3231^n | 1.3204^n |
| 5 | 1.4695^n | 1.4671^n |
| 6 | 1.5261^n | 1.5238^n |
| 7 | 1.6511^n | 1.6492^n |
| 8 | 1.6585^n | 1.6564^n |
| 9 | 1.7460^n | 1.7445^n |
| 10 | 1.7775^n | 1.7756^n |
| 11 | 1.7775^n | 1.7756^n |
| 12 | 1.8246^n | 1.8227^n |
| 13 | 1.8499^n | 1.8487^n |
| 14 | 1.8580^n | 1.8573^n |
| 15 | 1.9303^n | 1.9288^n |
| 16 | 1.9303^n | 1.9288^n |
| 17 | 1.9303^n | 1.9288^n |
| 18 | 1.9366^n | 1.9350^n |
| 19 | 1.9575^n | 1.9568^n |
| 20 | 1.9575^n | 1.9574^n |

These are best known upper bounds in this model, to our knowledge, and not tight ones. Algorithms with quantum random access memory are outside this model; with it, [7] solves graph colouring for every k in O(1.7956^n).

**Prior work.** The classical 3-colouring algorithm in O*(1.3289^n) is from [3], and the improvement to O*(1.3217^n) from [2], building on it. The square root of the time of [3] by quantum search is from [4], with the details in Lemma 6 of [1]. The reductions from k-colouring to 3-colouring are from [6], and their quantum form with size limits, Theorem 9 of [1], is the tool used here. To our knowledge, what is new is the quantum 3-colouring bound from [2], and the bounds for k ≥ 4 that follow from it.

## 1. Theorem 1

The algorithm of [2] has three kinds of steps. Reductions and branching rules on the graph, such as the rules on vertices of degree three, replace an instance by polynomially many smaller instances. Then it fixes a set S of vertices, through its forests, and tries the colourings of S that its analysis counts. Each colouring leaves a (3,2)-constraint satisfaction instance, which the algorithm of [3] solves by branching. Every step answers as the OR of its children, computes them in polynomial time, and keeps only the current instance. So the algorithm is a backtracking tree of polynomial depth, and its number of nodes is at most its running time, O*(1.3217^n). The vertices of S are coloured one at a time, in the order of [2], in which each vertex of a tree of the forest comes after its parent. Each node offers the colours that differ from those of its coloured neighbours, so a vertex after its parent has at most two, and where [2] colours two vertices together the node lists the pairs in the same way. A node stores S, the order and the partial colouring, fixed when S is chosen, so the forests are not recomputed on a partly coloured graph.

By [2] there is a fixed polynomial p with at most T_n = p(n) · 1.3217^n nodes on every graph with n vertices. The quantum walk on backtracking trees [5], given the bound T_n, detects a marked leaf in time √T_n poly(n), with bounded error and in polynomial space. Its running time depends only on n, so it can be used inside the quantum search of Section 2. This is an analogue of Lemma 6 of [1] for the algorithm of [3], with the walk in place of search over leaf indices. A colouring follows by self-reduction: fix the colour of one vertex at a time, by merging it with one of three fixed new vertices of a triangle, and keep the change if the answer stays yes. ∎

## 2. Theorem 2

Theorem 9 of [1] turns a polynomial-space quantum 3-colouring algorithm in time O*(2^{f₃n}) into one for k-colouring in time O*(2^{d_k(1)n}), for the exponents d_k(μ) below, with d₃ = f₃ and d₁ = d₂ = 0. Here μ = u/n, where u bounds the size of each colour class. Write h for the binary entropy, logarithms to base 2.

    d_k(μ) = min( max_{1 ≤ s ≤ k} log(s)/(2s) + (1 − 1/s) d_{k−1}(1),
                  min_{2 ≤ k′ ≤ k/2} max_{δ ∈ [k′/k, min(1, μk′)]} h(δ)/2
                       + max( δ d_{k′}(min(1, μ/δ)), (1 − δ) d_{k−k′}(min(1, δ/(k′(1 − δ)))) ) ).

The first line enumerates maximal independent sets of size at least n/k, by [6] with quantum search, and colours the rest with k − 1 colours. The second guesses the union S of the k′ largest colour classes, of size δn, by quantum search, and solves G[S] and G − S, whose classes are at most |S|/k′.

Take f₃ = log(1.3217)/2 from Theorem 1.

- **k = 3, 4, 5.** For k ≤ 5 the first line suffices. Its term for s is at most y if s · x^{2(s−1)} ≤ y^{2s}, with x a bound on 2^{d_{k−1}(1)}. With x = √1.3217 and y = 1.32034, and then x = 1.32034 and y = 1.4671, these are polynomial inequalities for s = 1, …, 5.
- **k = 6 to 20.** The values come from evaluating the recursion as an upper bound. The range of δ is cut into 4000 pieces [a, b]. On a piece, h(δ) is at most its maximum on [a, b], δ d_{k′}(μ/δ) is at most b d_{k′}(μ/a), and the second term is at most (1 − a) d_{k−k′}(b/(k′(1 − b))), with the limit 1 when b = 1. Every μ is rounded up to a grid of step 1/4000. The algorithm may pass these larger size limits on to its calls, since a larger limit only weakens the promise of the call, so the values bound the running time of that algorithm and are not only approximations of the recursion. A margin of 10⁻⁹ in the exponent covers the floating point error. With f₃ from [3], the same computation gives the values of [1] to within 0.0008 in the base.

## 3. Measurements

[`bounds.py`](bounds.py) computes the table, with its output in [`bounds.log`](bounds.log). The second column there is the same computation with f₃ from [3], next to the values of [1].

[`check_reduction.py`](check_reduction.py) runs the recursion of Section 2 classically, with OR in place of quantum search, on random graphs with 5 to 9 vertices and k from 3 to 8. Its base case respects the size limits strictly, and the limits passed on are kept tight or enlarged at random. With either reduction chosen at random, and with Reduction 2 only, it agrees with brute force on 300 graphs each. As a control, lowering the limit for G − S by one makes 143 of 300 answers wrong, so the test depends on the limits ([`check_reduction.log`](check_reduction.log)).

## 4. Limits

- Theorem 1 uses the running time of the algorithm of [2] as stated there. Its analysis is a linear program over the structure of the forests, which is not reproduced here. The paper [2] is an arXiv paper, unrefereed. With the algorithm of [3] in its place, every row returns to the values of [1].
- Rows k = 6 to 20 are a floating point computation, not an interval arithmetic certificate.
- The quantum walk of [5] is used as stated.

## 5. Formal verification

The Lean library [`lean/`](lean/) is built on Mathlib and uses only the standard axioms ([`lean/axioms.log`](lean/axioms.log)).

| Theorem | Statement |
|---|---|
| `term_le` | If s · x^{2(s−1)} ≤ y^{2s}, then s^{1/(2s)} · x′^{(s−1)/s} ≤ y for every 0 ≤ x′ ≤ x |
| `row3` | √1.3217 ≤ 1.1497 |
| `row4` | Every term s = 1, …, 4 of the first line for k = 4 is at most 1.32034 |
| `row5` | Every term s = 1, …, 5 of the first line for k = 5 is at most 1.4671, given 2^{d₄(1)} ≤ 1.32034 |

Not formalized: the backtracking structure of the algorithm of [2], the quantum walk, Theorem 9 of [1], and the rows k = 6 to 20.

## References

1. K. Shimizu and R. Mori. Exponential-time quantum algorithms for graph coloring problems. Algorithmica 84, 2022. arXiv:1907.00529. Theorem and lemma numbers refer to the arXiv version.
2. L. Meijer. 3-Coloring in time O(1.3217^n). arXiv:2302.13644, 2023.
3. R. Beigel and D. Eppstein. 3-coloring in time O(1.3289^n). J. Algorithms 54(2), 2005.
4. M. Fürer. Solving NP-complete problems with quantum search. LATIN 2008.
5. A. Montanaro. Quantum-walk speedup of backtracking algorithms. Theory of Computing 14(15), 2018.
6. J. M. Byskov. Enumerating maximal independent sets with applications to graph colouring. Oper. Res. Lett. 32(6), 2004.
7. S. Gaspers and J. Z. Li. Quantum algorithms for graph coloring and other partitioning, covering, and packing problems. ICALP 2024. arXiv:2311.08042.
