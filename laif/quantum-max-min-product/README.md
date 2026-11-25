# Quantum (max, min)-product and all-pairs bottleneck paths

Written 25 Nov 2026.

The (max, min)-product of two n × n matrices is C[i, j] = max over k of min(A[i, k], B[k, j]). It computes all-pairs bottleneck paths in directed graphs with real edge weights, up to polylogarithmic factors. The best classical algorithm takes n^{(3+ω)/2} time. The first quantum algorithm below n^{5/2} for it runs in n^{2.473} [1, Theorem 4.1]. In [2] the (max, min)-product, the (min, ≤)-, (max, ≤)- and (min, =)-products are reduced to the All-Edges Monochromatic Equality Triangle problem (AE-MonoEq): given a graph on n vertices where each edge has a colour and a value, decide for every edge whether it lies in a triangle with all three edges of one colour and two edges of equal value.

Here the quantum enumeration of [1] is carried to AE-MonoEq, and the reductions of [2] carry the bound to the products. The (max, min)-product needs only the (min, ≤)-product [1, 2].

**Theorem 1.** In the quantum time model with classical memory readable in superposition, AE-MonoEq on n vertices can be solved with high probability in time Õ(n^{(5+ω)/3}). Consequently, the (max, min)-, (min, ≤)-, (max, ≤)- and (min, =)-products of n × n matrices, and all-pairs bottleneck paths in directed graphs with real edge weights, take time Õ(n^{(5+ω)/3}).

1. With the published bound ω < 2.371177 [3, Table 1; 6], the time is n^{2.45706}.
2. If ω ≤ 9/4, as claimed in [5], the time is at most n^{29/12} = n^{2.4167}.

Status: Claim. The exponents are evaluated by script with asserts.

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| Quantum (max, min)-product, all-pairs bottleneck paths with edge weights | n^{2.473} [1]; with the bounds of [3] in the formula of [1], n^{2.46932}; classically n^{2.6856} | n^{2.45706} |
| Quantum AE-MonoEq, AE-Monochromatic Triangle, (min, ≤)-product | n^{2.5} by quantum search over the third vertex or index | n^{2.45706} |
| The same, if ω ≤ 9/4 [5] | n^{2.4445} for the (max, min)-product, from the formula of [1] if also ω(1, 1/2, 1) = 2 | n^{2.4167} |

All-pairs bottleneck paths with weights on the vertices instead of the edges have a quantum algorithm in n^{2.434} [4]; that problem is equivalent to maximum witnesses of Boolean products and is not covered here.

## 1. The algorithm

The vertex set is copied into parts I, J, K, with every edge of the graph placed in I × J, I × K and J × K, and each edge gets the key (colour, value). Two edges of a good triangle share their value; the three choices of this pair are handled separately, for each of the three edge classes, and the answers are combined by OR. Let D = F = n^f, and let deg_c(i) be the number of colour-c edges at i.

**Values on I × K and J × K.** An edge (i, j) of colour c is good if some k has key(i, k) = key(j, k) with colour c.

- *Light endpoint.* If deg_c(i) ≤ D or deg_c(j) ≤ D, Grover search over those neighbours checks key equality, in time Õ(√D) per edge.
- *Frequent key.* A pair (k, κ) is frequent if at least F edges between k and J have key κ; there are at most n²/F of them. For each colour c, one Boolean product of the vertices of colour-c degree above D in I, the frequent keys of colour c, and the same vertices in J answers all such pairs.
- *Rare key.* The set Γ of pairs (edge (i, k) with a rare key, index b < F into the J-side list of that key at k) has at most n²F elements and is indexed in polylogarithmic time. Quantum enumeration with strike-out, as in [1, Lemma 3.1], finds every pair (i, j) with a marked element in Õ(√(|Γ| n²)) = Õ(n²√F).

**Values on I × J and J × K** (and symmetrically I × J and I × K). The pair (i, j) fixes the key κ = (c(i, j), v(i, j)), and it is good if some k has key(j, k) = κ and c(i, k) = c. If deg_c(i) ≤ D, Grover search runs over the colour-c neighbours of i. If at most F vertices k have key(j, k) = κ, Grover search runs over them. Otherwise, a Boolean product per colour of the high-degree vertices of I, all of K and the frequent pairs (j, κ) gives the answer.

## 2. Cost

The searches cost Õ(n^{2 + f/2}). A Boolean product of shape a × m × b with a, b ≤ m_c/n^f, where m_c is the number of colour-c edges in I × K and J × K, costs at most n^{1−f} m_c n^{ω−2} by square blocks, and the sum over colours is O(n^{ω+1−f}). The choice f = 2(ω − 1)/3 balances the two terms at (5 + ω)/3. The reductions of [2, Theorems 4.6, 4.7] call AE-MonoEq on instances of size n + 1 a polylogarithmic number of times and need only its answers, so a union bound keeps the error at 1/poly(n). They give the (min, =)- and (min, ≤)-products, and the (max, ≤)-product is implied by [2, Proposition 4.8]. The (max, min)-product follows from the (min, ≤)-product, and bottleneck paths from O(log n) (max, min)-products.

## 3. Measurements

[`sim/exponent.py`](sim/exponent.py) computes (5 + ω)/3 and the bound n^{(5−γ)/2} of [1, Theorem 4.1], with γ + 2ω(1 + γ, 1 + γ, 1) = 5, from the lower convex hull of the points of [3, Table 1]. It asserts that the bound of this work lies below the one of [1] for the published bounds, under ω ≤ 9/4 with ω(1, 1/2, 1) = 2, and for ω = 2 (7/3 against 2.4), and that the formula of [1] with the 2013 constants stays below 2.473. Run it with `python exponent.py` in `sim/`.

## 4. Limits

- Memory is classical memory readable in superposition, with unit cost per access, as in [1]. It holds the input, the lists built in preprocessing and the set of pairs already found, which is updated classically between searches.
- Faster rectangular multiplication does not lower the exponent of this scheme: its worst case has n^{1−f} colours with n^{1+f} edges each, where every product is square.
- Part 2 holds under the claim of [5].
- Not formalized in Lean.

## References

1. F. Le Gall, H. Nishimura. Quantum algorithms for matrix products over semirings. SWAT 2014, Chicago Journal of Theoretical Computer Science 2017, arXiv:1310.3898.
2. V. Vassilevska Williams, Y. Xu. Monochromatic triangles, triangle listing and APSP. FOCS 2020, arXiv:2007.09318.
3. J. Alman, R. Duan, V. Vassilevska Williams, Y. Xu, Z. Xu, R. Zhou. More asymmetry yields faster matrix multiplication. arXiv:2404.16349.
4. M. Kowaluk, A. Lingas. Quantum and approximation algorithms for maximum witnesses of Boolean matrix products. International Journal of Foundations of Computer Science, 2024, arXiv:2004.14064.
5. OpenAI. An upper bound of 9/4 for the matrix multiplication exponent. 2026, github.com/openai/math.
6. E. Dupont, M. Eisenberger, B. Kozlovskii, A. Mehrabian, F. J. R. Ruiz, A. See, R. Zhou, J. Alman, V. Vassilevska Williams, M. Balog. Improving the matrix multiplication exponent with modern optimization and AlphaEvolve. arXiv:2608.16884.

## Use of AI

The algorithm, the analysis, the script and this text were produced with the help of Claude Opus 5.5.
