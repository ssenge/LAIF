# Short-path algorithm for group relaxations of integer programs: an upper bound on the gain

_24 November 2026_

The group relaxation of an integer linear program drops the sign constraints on the basic variables of an optimal LP basis B. What remains is a linear cost f over a coset x̂ + K of a finite abelian group K. In [1], the generalized short-path algorithm of [2] is applied to this coset with a Cayley walk on K. The resulting runtime is O*((|K|/|K*|)^(1/2 − α)), where K* is the set of optimal elements and α > 0 is the gain over a quadratic speedup of Markov chain search. Two walks are used:

- a product of cycles built from a sparse generating set [1, Theorem 9];
- an expander built from C log|K| uniformly random elements of K [1, Theorem 11].

Both theorems state conditions under which α is a constant independent of the dimension.

## Result

Write L = ln(|K|/|K*|) for the logarithm of the expected number of samples of Markov chain search. On the feasible coset, let Γ = E_π f − OPT be the mean of f above the optimum and M = max f − OPT its maximum above the optimum. Let Γ_S be the mean of f(x* ± s) − OPT over the moves s of the walk at an optimum x*.

**Theorem 1 (every instance, every Cayley walk).** Take the runtime bound of [2, Theorem 4.3] ([1, Theorem 3]) with any admissible parameters η, b and shift of the cost. Then

  α < (2/15)(1 − η) · (δ / (1 − p_0)) · M / (Γ_S L), with δ / (1 − p_0) ≤ 1 + 1/(|K| − 1),

where δ is the spectral gap of the walk and p_0 its holding probability. The proof has three steps.

- **Stability at an optimum.** At an optimum, the stability condition [1, Definition 6] forces Δ_P ≥ E_y min(f(y) − OPT, η|E*|).
- **The size of the well.** The technical condition (4) of [1, Theorem 3] forces π(E ≤ (1 − η)E*) ≤ 1/16. Markov's inequality applied to f − OPT then bounds the depth of the well, η|E*| ≤ (16/15) Γ.
- **The exponent.** With b < δ/4, both bounds together bound the exponent η(1 − η)|E*| b / (2 Δ_P L).

**Corollary 2 (expander walk).** For the expander of [1, Theorem 11], each move x* ± s with s uniformly random is uniform on the coset, so the expected value of Γ_S is Γ. With high probability,

  α ≤ (4/15)(1 + o(1)) · M / (Γ L).

Whenever M/Γ = O(1), this gives α = O(1/n) in the regime of [1], where L = Θ(n). For the family of [1, Theorem 10], M = 2Γ exactly, so α ≤ (8/15)(1 + o(1)) / (m ln t), with m constraints and generators of order t.

This hints at a possible gap in the proof of [1, Theorem 11]. That proof needs the largest cyclic weight of the generators to be of order |OPT_B| / L, together with a shift |E*| of the order of |OPT_B|. A uniformly random element of K has mean cyclic weight at least M/4, measured over its support. So the condition forces |E*| to grow like L · M, and that conflicts with η|E*| ≤ (16/15) Γ from condition (4) once L is large.

The product-of-cycles walk of [1, Theorem 9] and the family of [1, Theorem 10] are not affected by this bound. The survey entry [3, Sec. 8.1] cites [1] for a super-quadratic speedup over classical local search on the group relaxation, and that rests on Theorem 9.

## Scope

- **Proved.** Theorem 1 and Corollary 2 are written proofs (Claim).
- **Checked.** `sim/alpha_bounds.py` tests them exactly on 126 random small instances: |K| up to about 1000, moves by sparse generators or random elements, holding probability 0, 1/3 and 1/2, five values of η and 25 shifts each. It computes the smallest valid Δ_P from [1, Definition 6] at every point and the exact spectral gap. The largest ratio of the exponent to the bound of Theorem 1 is 0.865.
- **Runtime bound only.** The bound applies to the runtime guarantee of [2, Theorem 4.3], the version used by [1, Theorem 11]. The true runtime of the short-path algorithm with the expander walk may be smaller.
- **Not formalized.** No part is in Lean.

## Files

- `sim/alpha_bounds.py`: exact checks of the steps and the bound of Theorem 1, the mean cyclic weight of random elements, and M = 2Γ on the family of [1, Theorem 10] (`python -I alpha_bounds.py`).

## Use of AI

The analysis, code and text were produced with Claude Opus 5.5.

## References

1. B. Augustino, D. Herman, G. Ozgul, J. Watkins, A. Acharya, E. Fontana, J. L. Kim, S. Chakrabarti. Quantum speedups for group relaxations of integer linear programs. arXiv:2602.13494.
2. S. Chakrabarti, D. Herman, G. Ozgul, S. Zhu, B. Augustino, T. Hao, Z. He, R. Shaydulin, M. Pistoia. Generalized short path algorithms: towards super-quadratic speedup over Markov chain search for combinatorial optimization. arXiv:2410.23270.
3. The compendium of super-quadratic computational quantum advantages. arXiv:2610.32595.
