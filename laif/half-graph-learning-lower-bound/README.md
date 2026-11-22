# Learning column-permuted half graphs: a tight quantum lower bound

Written 22 Nov 2026.

**Setting.** As in [1]: a hidden n × n 0/1 matrix M is a column permutation of the lower triangular matrix L_n, so M[i, j] = 1 exactly when i ≥ π(j) for an unknown permutation π of [n]. An edge query returns one entry M[i, j]. Q(C_n) is the number of quantum queries needed to output π with error at most 1/3. Equivalently [1, Section 4.1.1], an unknown list that is a permutation of [n] is sorted with threshold comparisons "is X[j] ≥ i?".

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Q(C_n), lower bound | Ω(n) [1]; upper bound O(n log n) by binary search in every column [1] | Ω(n log n), so Q(C_n) = Θ(n log n) | Claim; checked by script for n ≤ 7 |

Theorem 1 confirms the conjecture Q(C_n) = Θ(n log n) of [1]. For half graphs with both rows and columns permuted, the bound Ω(n log n) follows from the lower bound for sorting [2], as noted in [1]. Theorem 1 gives the same order when the rows are fixed.

## Theorem 1

**Theorem 1.** For every n ≥ 2 and 0 ≤ ε < 1/2,

Q_ε(C_n) ≥ (1 − 2√(ε(1 − ε)))/2 · (n H_{n−1} − n + 1)/π,

where H_{n−1} = 1 + 1/2 + ⋯ + 1/(n − 1). In particular Q(C_n) = Ω(n log n).

*Proof.* We use the spectral adversary bound [3], with the constant of [4, Thm. 2]: for a nonnegative symmetric matrix Γ on the inputs with Γ[x, y] = 0 whenever x and y have the same output, Q_ε ≥ (1 − 2√(ε(1 − ε)))/2 · ‖Γ‖/max_q ‖Γ_q‖, where Γ_q keeps the entries Γ[x, y] with x_q ≠ y_q and sets the others to 0.

The inputs are the permutations π. For two columns j ≠ j′, let π′ = π ∘ (j j′) be π with the values of the columns j and j′ exchanged, and set Γ[π, π′] = 1/|π(j) − π(j′)|. All other entries are 0. Then Γ is symmetric, and every row contains one entry 1/|a − b| for each pair of values a < b, so every row sum equals

R = Σ_{1 ≤ a < b ≤ n} 1/(b − a) = Σ_{d=1}^{n−1} (n − d)/d = n H_{n−1} − n + 1.

A nonnegative symmetric matrix with constant row sums R has norm R, with the all-ones vector as eigenvector, so ‖Γ‖ = R.

Fix a query q = (i, j). An exchange of two columns other than j leaves M[i, j] unchanged. An exchange of j with j′ changes M[i, j] exactly when i separates the two values, that is, min(π(j), π(j′)) ≤ i < max(π(j), π(j′)). Group the permutations by the value a = π(j). For a ≠ b, the block of Γ_q from the group a to the group b maps π to the unique π′ with π′(j) = b, namely the exchange of j with the column π^{−1}(b), and this map is a bijection between the two groups of (n − 1)! permutations, since the same exchange maps π′ back to π. So this block is m_{ab} times a permutation matrix, with m_{ab} = 1/|a − b| if i separates a and b and m_{ab} = 0 otherwise. For every vector x = (x_a) split into the groups,

‖Γ_q x‖² = Σ_a ‖Σ_b B_{ab} x_b‖² ≤ Σ_a (Σ_b m_{ab} ‖x_b‖)² ≤ ‖m‖² Σ_b ‖x_b‖²,

so ‖Γ_q‖ ≤ ‖m‖. The matrix m consists of the block K_i[a, b] = 1/(b − a) with a ≤ i < b and its transpose, so ‖m‖ = ‖K_i‖. With a′ = i + 1 − a and b′ = b − i, the entries become 1/(a′ + b′ − 1), a submatrix of the infinite matrix (1/(s + t − 1))_{s,t ≥ 1}, whose norm is at most π by the inequality Σ_{s,t} x_s y_t/(s + t − 1) ≤ π‖x‖‖y‖ [5], also used in [2, Section 3.1]. Hence max_q ‖Γ_q‖ ≤ π, and the spectral adversary bound gives the claim. ∎

The same weights 1/|a − b| give the Ω(log n) lower bound for ordered search in [2]. The sorting bound of [2] puts the weight 1/d on cyclic shifts of d + 1 ranks, which change d + 1 columns at once. Here the weights sit on exchanges of two columns, so that a single threshold query separates only the exchanges that involve its own column.

## Scripts

`sim/check_adversary.py` builds Γ over all n! permutations for n ≤ 7. It checks that the row sums and the norm equal n H_{n−1} − n + 1, and that ‖Γ_q‖ ≤ ‖K_i‖ < π for every query, with a dense floating-point eigenvalue computation. It also checks ‖K_i‖ < π for n ∈ {50, 200, 800} and every ⌊n/40⌋-th i.

```
python sim/check_adversary.py
n = 2: ||Gamma|| = 1.0000 = n H_(n-1) - (n-1), max_q ||Gamma_q|| = 1.0000 < pi, ratio 1.000
n = 3: ||Gamma|| = 2.5000 = n H_(n-1) - (n-1), max_q ||Gamma_q|| = 1.1180 < pi, ratio 2.236
n = 4: ||Gamma|| = 4.3333 = n H_(n-1) - (n-1), max_q ||Gamma_q|| = 1.2676 < pi, ratio 3.419
n = 5: ||Gamma|| = 6.4167 = n H_(n-1) - (n-1), max_q ||Gamma_q|| = 1.3330 < pi, ratio 4.814
n = 6: ||Gamma|| = 8.7000 = n H_(n-1) - (n-1), max_q ||Gamma_q|| = 1.4083 < pi, ratio 6.178
n = 7: ||Gamma|| = 11.1500 = n H_(n-1) - (n-1), max_q ||Gamma_q|| = 1.4519 < pi, ratio 7.680
n = 50: max_i ||K_i|| = 1.9518 < pi
n = 200: max_i ||K_i|| = 2.1827 < pi
n = 800: max_i ||K_i|| = 2.3536 < pi
```

## Lean

The library `HalfGraph` in `lean/` (Lean 4, toolchain and Mathlib revision pinned in `lean-toolchain` and `lake-manifest.json`) proves, with only the standard axioms (`lean/axioms.txt`):

* `rowSum`: the row sum Σ_{1 ≤ a < b ≤ n} 1/(b − a) = Σ_{d=1}^{n−1} (n − d)/d (values indexed from 0), with `inner_sum` for the inner sum.
* `swap_apply_col`, `swap_swap_back`: for a fixed column j, the exchange of j with the column π^{−1}(b) puts the value b into column j, and the exchange with the column that now holds π(j) returns π. So the block from the group a to the group b is a bijection.
* `block_norm_le`: the triangle step ‖Σ_b B_b x_b‖ ≤ Σ_b m_b ‖x_b‖ for operators with ‖B_b‖ ≤ m_b.

**Not formalized:** the norm of Γ, the bound ‖Γ_q‖ ≤ ‖K_i‖ and the final bound. The spectral adversary bound and the inequality Σ_{s,t} x_s y_t/(s + t − 1) ≤ π‖x‖‖y‖ are classical.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. N. S. Mande, S. Sanyal, V. Zamaraev. Complexity of learning matchings and half graphs via edge queries. arXiv:2507.03151, 2025.
2. P. Høyer, J. Neerbek, Y. Shi. Quantum complexities of ordered searching, sorting, and element distinctness. Algorithmica 34, 2002. arXiv:quant-ph/0102078.
3. H. Barnum, M. Saks, M. Szegedy. Quantum query complexity and semi-definite programming. CCC 2003.
4. P. Høyer, T. Lee, R. Špalek. Negative weights make adversaries stronger. STOC 2007. arXiv:quant-ph/0611054.
5. G. H. Hardy, J. E. Littlewood, G. Pólya. Inequalities. Cambridge University Press, 1934.
