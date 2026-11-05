# Zero-sum games: a quantum lower bound with precision dependence

Written 5 Nov 2026.

## Result

Input: an m × n payoff matrix A with entries in [−1, 1], given by a quantum oracle for its entries. Task: an ε-approximate Nash equilibrium, that is, mixed strategies x, y with max_i (Ay)_i − min_j (xᵀA)_j ≤ ε, or the value of the game up to ±ε.

**Theorem.** For m, n ≥ 2 and 0 < ε < 1/4, every quantum algorithm that solves either task with probability at least 2/3 makes

    Ω(√(max(m, n) · min(m, n, 1/ε)))

queries. In particular it makes Ω(√((m + n)/ε)) queries when min(m, n) ≥ 1/ε.

| | Bound |
|---|---|
| Previous best lower bound | Ω(√(m + n)) for constant ε [3] |
| This folder | Ω(√(max(m, n) · min(m, n, 1/ε))) |
| Best upper bound | Õ(√(m + n) · ε^{−2.5} + ε^{−3}) [1], also [4]; Õ(√(m + n) · ε^{−3}) earlier [2] |

When min(m, n) ≥ 1/ε, the gap to the term √(m + n) · ε^{−2.5} shrinks from a factor ε^{−2.5} to ε^{−2}. For square games with n ≈ 1/ε, the bound is Ω(1/ε).

## The argument

By symmetry (replace A by −Aᵀ and swap the players), assume m ≥ n. Let c = min(n, ⌈1/(2ε)⌉ − 1), so 2 ≤ c, cε < 1/2 and c = Θ(min(n, 1/ε)).

**Instances.** Row i of A has 0/1 entries. On the first c columns it has a single 0 at column p_i, or no 0 at all. The other n − c columns are all ones. In a *no instance* every row has a 0. In a *yes instance* exactly one row j* has none.

**Value gap.** On a yes instance, the pure row j* earns 1 against every column. On a no instance, the losses 1 − (xᵀA)_l over the first c columns sum to Σ_i x_i = 1, so some column holds the row player to at most 1 − 1/c. Since ε < 1/(2c), the value up to ±ε tells the two cases apart.

**Equilibria locate the special row.** Let (x, y) be an ε-approximate equilibrium of a yes instance. Row j* earns 1 against y, so (xᵀA)_l ≥ 1 − ε for every column l. Summing the losses over the first c columns gives 1 − x_{j*} ≤ cε < 1/2, so x_{j*} > 1/2. A Grover search for a 0 in the heaviest row of x, with O(√c) queries, then decides the instance: that row has no 0 on a yes instance, and every row has one on a no instance.

**Lower bound.** Relate a no instance to the m yes instances that arise by deleting the 0 of one row. Each yes instance is related to the c no instances that arise by placing a 0 in its special row. For every input bit, at most one related partner differs in it, on either side. The relational adversary bound [5] then gives Ω(√(mc)) queries for telling yes from no. With the reductions above, an algorithm for either task with T queries gives T + O(√c) ≥ Ω(√(mc)), so T = Ω(√(mc)) once m exceeds a constant. Below that constant, c ≤ n ≤ m is also bounded and the claim is trivial.

## Machine check

`lean/ZeroSumLB.lean` checks the combinatorial part, with Lean 4.36.0-rc1 and Mathlib revision `d875a8de5222f62cf1c2fafc7984588adadc990a`. It contains no `sorry`, and its theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

- `loss_sum`: the losses over the first c columns sum to the weight on rows that have a 0.
- `yes_pure`, `no_gap`: the value is 1 on yes instances and at most 1 − 1/c on no instances.
- `yes_identifies`: every ε-approximate equilibrium of a yes instance with cε < 1/2 puts weight more than 1/2 on the special row.
- `rel_yes`, `left_many`, `right_many`, `left_unique`, `right_unique`: the relation of the adversary bound has the counts m, c, 1 and 1.

**Not machine-checked:** the relational adversary bound [5], Grover search, and the symmetry and padding steps.

## References

[1] A. Bouland, Y. M. Getachew, Y. Jin, A. Sidford, K. Tian. Quantum speedups for zero-sum games via improved dynamic Gibbs sampling. ICML 2023. arXiv:2301.03763.

[2] J. van Apeldoorn, A. Gilyén. Quantum algorithms for zero-sum games. arXiv:1904.03180, 2019.

[3] T. Li, S. Chakrabarti, X. Wu. Sublinear quantum algorithms for training linear and kernel-based classifiers. ICML 2019. arXiv:1904.02276.

[4] M. Gao, Z. Ji, T. Li, Q. Wang. Logarithmic-regret quantum learning algorithms for zero-sum games. NeurIPS 2023. arXiv:2304.14197.

[5] A. Ambainis. Quantum lower bounds by quantum arguments. J. Comput. Syst. Sci. 64(4), 2002. arXiv:quant-ph/0002066.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the Lean formalization, and to draft the text.
