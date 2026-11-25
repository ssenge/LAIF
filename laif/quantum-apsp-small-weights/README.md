# Quantum all-pairs shortest paths in directed graphs with small integer weights

Written 25 Nov 2026.

All-pairs shortest paths (APSP) in a directed graph with n vertices and integer edge weights in {−M, …, M}, M constant, and no negative cycles. Classically the best bound is n^{2 + μ} with ω(1, μ, 1) = 1 + 2μ, by bridging sets and rectangular matrix multiplication [2], now n^{2.5275} [5]. Quantum minimum finding gives n^{2.5} for any weights. A quantum algorithm in time n^{2.5 − (2.5 − ω)/(4κ + 2)} for geometrically weighted graphs, which include small integer weights, is given in [1], where the use of rectangular matrix multiplication is suggested as a way to improve such bounds [1, footnote 2]. The balance of rectangular multiplication against quantum minimum finding used below was introduced for maximum witnesses of Boolean matrix products, all-pairs bottleneck paths in vertex-weighted graphs and all-pairs lowest common ancestors in [9], with time n^{2 + λ/2} where ω(1, λ, 1) = 1 + 1.5λ. Here it is carried to the bridging sets of [2].

Here ω(1, k, 1) denotes the exponent of multiplying an n × n^k matrix by an n^k × n matrix.

**Theorem 1.** In the quantum time model with classical memory readable in superposition, APSP in directed graphs with weights in {−M, …, M}, M constant, and no negative cycles can be solved with high probability in time n^{τ + o(1)}, where

τ = max over l ∈ [0, 1] of min{ l + ω(1, 1 − l, 1), 5/2 − l/2 }.

1. With the published bounds on ω(1, k, 1) [5, Table 1], τ < 2.41346.
2. If ω ≤ 9/4 and ω(1, 1/2, 1) = 2, as claimed in [6, 7, 8], then τ ≤ 19/8.
3. For every value of the exponents, τ ≥ 7/3, with equality if ω = 2.

Status: Claim. The exponent τ is evaluated by script with asserts.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| Quantum APSP, directed graphs, weights in {−M, …, M}, M constant | n^{2.4571}, implied by [1] (ℓ distance products, quantum single-source shortest paths from a sample of n/ℓ vertices after one reweighting by potentials, quantum minimum finding); classically n^{2.5275} [2, 5] | n^{2.41346} |
| The same, if ω ≤ 9/4 and ω(1, 1/2, 1) = 2 [6, 7, 8] | n^{29/12} ≈ n^{2.4167}, implied by [1]; classically n^{2.5} | at most n^{19/8} = n^{2.375} |

## 1. The algorithm

The bridging-set iteration of [2] starts with the weight matrix D and, for i = 1, …, ⌈log_{3/2} n⌉, sets s = (3/2)^i, draws a random set B of 9 n ln n / s vertices, and sets D ← min(D, D′[V, B] ⋆ D′[B, V]), where ⋆ is the min-plus product and D′ is D with every entry of absolute value above M s replaced by ∞. After the last scale D holds all distances with high probability [2]. Paths follow from witnesses, which both methods below return. This only needs each product to be exact.

At the scale s = n^l the product is an n × n^{1−l} by n^{1−l} × n min-plus product with entries in {−M s, …, M s}. It is computed by the cheaper of two methods:

- **Rectangular multiplication.** The encoding of entries x as polynomials in a variable of degree M s + x [3] turns the product into one integer product of the same shape with entries of O(M s log n) bits, in time n^{l + ω(1, 1 − l, 1) + o(1)}.
- **Quantum minimum finding.** For each of the n² pairs (u, v), the minimum of D[u, b] + D[b, v] over b ∈ B is found by quantum minimum finding [4] with error 1/poly(n), in time Õ(n² · n^{(1−l)/2}). This method needs no bound on the entries.

A union bound over the n² pairs and O(log n) scales keeps the error probability at 1/poly(n). The time is the sum over the scales of the cheaper cost, that is n^{τ + o(1)}.

## 2. Values

The function k ↦ ω(1, k, 1) is convex and at least 2, so the lower convex hull of published points bounds it from above. With the points of [5, Table 1], the two costs balance between k = 0.80 and k = 0.90, at l ≈ 0.1731, which gives τ ≈ 2.413455. With ω ≤ 9/4 and ω(1, 1/2, 1) = 2, convexity puts ω(1, k, 1) on or below the segment from (1/2, 2) to (1, 9/4), and the balance on that segment at l = 1/4 gives τ ≤ 19/8. Since ω(1, k, 1) ≥ 2, the first cost is at least l + 2, and the balance with 5/2 − l/2 bounds τ below by 7/3.

The bound implied by [1] uses square products for paths with at most ℓ = n^l edges and quantum single-source shortest paths beyond, with cost n^{l + ω} + n^{5/2 − l/2}, which balances at (5 + ω)/3.

## 3. Measurements

[`sim/exponent.py`](sim/exponent.py) evaluates τ on a grid of 200,001 values of l. It asserts τ = 2.413455 for the published bounds, 19/8 on the segment from (1/2, 2) to (1, 9/4), 7/3 for ω = 2, and that τ lies below (5 + ω)/3 and below the classical 2 + μ. Run it with `python exponent.py` in `sim/` (NumPy needed).

## 4. Limits

- The weights are integers of constant absolute value. The cost of the rectangular method grows linearly in M.
- Negative cycles are assumed absent; they show up as negative diagonal entries after the last scale.
- Memory is classical memory readable in superposition, with unit cost per access, as in [1].
- Part 2 holds under the claims of [6, 7, 8].
- If ω = 2, the bound 7/3 equals the bound (5 + ω)/3 implied by [1].
- Not formalized in Lean.

## References

1. A. Nayebi, V. Vassilevska Williams. Quantum algorithms for shortest paths problems in structured instances. arXiv:1410.6220.
2. U. Zwick. All pairs shortest paths using bridging sets and rectangular matrix multiplication. Journal of the ACM, 2002.
3. N. Alon, Z. Galil, O. Margalit. On the exponent of the all pairs shortest path problem. Journal of Computer and System Sciences, 1997.
4. C. Dürr, P. Høyer. A quantum algorithm for finding the minimum. arXiv:quant-ph/9607014.
5. J. Alman, R. Duan, V. Vassilevska Williams, Y. Xu, Z. Xu, R. Zhou. More asymmetry yields faster matrix multiplication. arXiv:2404.16349.
6. OpenAI. An upper bound of 9/4 for the matrix multiplication exponent. 2026, github.com/openai/math.
7. A. Amanov, M. van den Berg, J. Zuiddam. Multiplying matrices via polynomials: exposition and barriers. arXiv:2610.30054.
8. P. Uznański. Rectangular matrix multiplication from polynomial products. arXiv:2610.10494.
9. M. Kowaluk, A. Lingas. Quantum and approximation algorithms for maximum witnesses of Boolean matrix products. International Journal of Foundations of Computer Science, 2024, arXiv:2004.14064.

## Use of AI

The algorithm, the analysis, the script and this text were produced with the help of Claude Opus 5.5.
