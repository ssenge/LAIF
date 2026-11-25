# Classical simulation of quantum query algorithms on most inputs, with an explicit depth

Written 25 Nov 2026.

**Setting.** As in [1, 2]: X is uniform on {0,1}^N, and p is a real polynomial of total degree at most d ≥ 1 with 0 ≤ p(X) ≤ 1 for every X. The influence of the variable i is Inf_i[p] = E[(p(X) − p(X^i))²], where X^i is X with the i-th bit flipped. The acceptance probability of a quantum algorithm that makes T queries is such a polynomial with d = 2T [3].

| | Problem | Previous best bound | This folder | Status |
|---|---|---|---|---|
| Thm 1 | Deterministic classical queries that approximate p within ε on a 1 − δ fraction of the inputs | (4T)⁸ ε⁻¹⁴ δ⁻⁸ for d = 2T [2, Section 1], from the reduction of [1, Theorem 22] with the exponent 7 | ⌈2d/(δφ)⌉ ≤ 4447 · d⁷ ε⁻⁵ δ^{−7/2} + 1, with φ = (8√15/(125π⁴)) (ε²δ/2)^{5/2}/d⁶; for d = 2T this is at most 569 101 · T⁷ ε⁻⁵ δ^{−7/2} + 1 (implied by [2]) | Lean, assuming the influence bound of [2] and the total influence bound of [1, Lemma 20] |

In the same form, the previous bound is 65 536 · T⁸ ε⁻¹⁴ δ⁻⁸ and Theorem 1 gives 569 101 · T⁷ ε⁻⁵ δ^{−7/2} + 1. The ratio of the leading terms is 8.69 · ε⁹ δ^{9/2}/T, so Theorem 1 is smaller whenever T > 8.69 · ε⁹ δ^{9/2}: for ε = δ = 1 from T = 9 on, and for ε, δ ≤ 1/2 for every T ≥ 1.

## The two inputs

- (A) For p as above with variance at least v > 0, some variable has Inf_i[p] ≥ (8√15/(125π⁴)) v^{5/2}/d⁶. This is the explicit form of the bounded-polynomial influence bound proved in [2], and it is the statement of the theorem `aaronson_ambainis_explicit` in the Lean library of [2].
- (B) The total influence Σ_i Inf_i[p] is at most d [1, Lemma 20].

## Theorem 1, the proof

The tree is built greedily. At a node, let g be p with the bits queried so far fixed. If Var[g] < τ = ε²δ/2, the node is a leaf that outputs E[g]. Otherwise, by (A) some variable has Inf_i[g] ≥ φ, and the node queries it. The tree is cut at depth k.

**A leaf.** By the second-moment inequality, a leaf with Var[g] < τ errs by more than ε on at most a τ/ε² = δ/2 fraction of its inputs.

**The potential.** Write I(g) = Σ_j Inf_j[g] and g_b for g with x_i = b. Then I(g_0) + I(g_1) = 2(I(g) − Inf_i[g]): the restricted functions do not depend on x_i, and for j ≠ i the influence of x_j is the average of its influences in the two halves. By induction on k, the greedy tree of depth at most k for g has

k φ · bad(g) ≤ k φ · τ/ε² + I(g),

where bad(g) is the fraction of inputs on which the tree errs by more than ε. A leaf satisfies it by the leaf bound. At an inner node, bad(g) is the average of bad(g_0) and bad(g_1), so with the induction hypothesis for k − 1 and bad ≤ 1,

k φ · bad(g) ≤ (k − 1) φ τ/ε² + (I(g_0) + I(g_1))/2 + φ ≤ k φ τ/ε² + I(g) − Inf_i[g] + φ,

and Inf_i[g] ≥ φ.

**The depth.** By (B), I(p) ≤ d. For k = ⌈2d/(δφ)⌉ the bound gives bad(p) ≤ δ/2 + d/(kφ) ≤ δ. ∎

A subtree for g_b may query x_i again. Such a query is answered by b: the branch is read with x_i = b, and of the two readings 0 and 1 one is at least as good as the subtree itself, since g_b ignores x_i. This keeps the depth and the error bound.

## Scripts

`sim/check_sim.py` takes 60 random polynomials with values in [0,1] (N ≤ 8, d ≤ 4) and checks (B), the identity for I(g_0) + I(g_1), and the inequality of the potential for the greedy tree at every depth k ≤ N, with φ the least influence queried.

```
python sim/check_sim.py
all asserts passed (60 random polynomials)
depth bound 2d/(delta*phi) = 4446.1 * d^7 / (eps^5 delta^3.5)
T=1 eps=0.1 delta=0.1: ours 1.800e+14, exponent-7 bound 6.554e+26
T=5 eps=0.1 delta=0.1: ours 1.406e+19, exponent-7 bound 2.560e+32
T=10 eps=0.01 delta=0.01: ours 5.691e+29, exponent-7 bound 6.554e+56
```

## Lean

The library `AASimulation` in `lean/` (Lean 4, toolchain and Mathlib revision pinned in `lean-toolchain` and `lake-manifest.json`) proves, with only the standard axioms (`lean/axioms.txt`):

* `simulation`: Theorem 1. It is stated for a polynomial `p : MvPolynomial (Fin N) ℝ` of total degree at most `d ≥ 1` with `0 ≤ p ≤ 1` on the cube, for all ε, δ > 0. The conclusion is a decision tree of depth at most ⌈2d/(δφ)⌉ with at most δ 2^N inputs on which its output is more than ε from p. It assumes the propositions `ExplicitBound` (input (A), copied unchanged from `AaronsonAmbainis/Conjecture.lean` of the library of [2] at commit `2a6ceae`) and `TotalInfluenceBound` (input (B)).
* `exists_tree`: the potential argument for any class of functions that is closed under restrictions and in which every function of variance at least τ has a variable of influence at least φ.
* `mean_restrict`, `totInf_restrict`: averaging over one coordinate, and the identity for the total influence of the two restrictions.
* `bad_leaf_le`, `exists_fix_le`, `bad_node`, `DTree.eval_fix`: the leaf bound, the choice of the reading of x_i, and the error of an inner node.

Restriction keeps the total degree at most d: the substitution of a constant for a variable is proved not to raise the total degree.

**Not formalized:** input (B) is taken from [1]; input (A) is taken as a hypothesis here and is proved in the Lean library of [2]. The step from a quantum algorithm to its acceptance polynomial [3] is not formalized.

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the check scripts, and to draft the text.

## References

1. S. Aaronson, A. Ambainis. The need for structure in quantum speedups. Theory of Computing 10 (2014) 133–166. arXiv:0911.0996.
2. D. Turturean. A proof of the Aaronson–Ambainis conjecture. arXiv:2611.09773, 2026. Lean library: https://github.com/physical-superintelligence/aaronson-ambainis
3. R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf. Quantum lower bounds by polynomials. Journal of the ACM 48 (2001) 778–797. arXiv:quant-ph/9802049.
