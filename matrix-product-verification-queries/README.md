# Quantum query complexity of matrix product verification

Sebastian Senge, Independent Researcher. Written 4 Nov 2026.

## Result

**Theorem 1.** Let R be a ring with unit and with a nonzero element of finite additive order, for example any finite field, or Z/m with m ≥ 2. Any bounded-error quantum algorithm that decides AB = C for n×n matrices over R, with a query being a fixed unitary for each pair of position and value, makes Ω(n^{5/3}) queries. This holds even with C fixed and known.

With the upper bound O(n^{5/3}) over any ring [1, 5, 6], the query complexity over such rings is Θ(n^{5/3}).

**Previous proof.** Ω(n^{5/3}) has a previous proof by Kintali [8], which covers every nonzero unital ring, including Z, along with further versions of the bound. Our contribution is a Lean proof of the F₂ case and a short written proof with an explicit gadget, in which the averaged acceptance probability is exactly a sum of juntas. The written proof covers the rings of Theorem 1.

## Proof over F₂

**Lemma 2 (gadget).** Let n ≥ 256, d = ⌊n/128⌋, k = 11d + 8 and q = n − 2k, so q ≥ d ≥ n/256. There are k × n matrices G, H over F₂ and vectors a_1, …, a_q, b_1, …, b_q ∈ F₂ⁿ with:
1. GHᵀ = 0, Ha_x = 0, Gb_y = 0, ⟨a_x, b_y⟩ = δ_xy;
2. Gv ≠ 0 and Hv ≠ 0 for every nonzero v of weight below d.

*Proof.* Split the coordinates into blocks of sizes k, k, q. For k × q matrices Q, S and a k × k matrix M, let

G = [I, Mᵀ + QSᵀ, Q], H = [M, I, S], a_x = (0, Se_x, e_x), b_y = (Qe_y, 0, e_y).

Part 1 holds for all Q, M, S: GHᵀ = Mᵀ + (Mᵀ + QSᵀ) + QSᵀ = 0, Ha_x = Se_x + Se_x = 0, Gb_y = Qe_y + Qe_y = 0, and ⟨a_x, b_y⟩ = ⟨e_x, e_y⟩.

Take Q, M, S uniform and fix v = (v₁, v₂, v₃) ≠ 0. Then Gv = v₁ + Mᵀv₂ + QSᵀv₂ + Qv₃. If v₂ ≠ 0, then Mᵀv₂ is uniform given Q, S. If v₂ = 0 and v₃ ≠ 0, then Qv₃ is uniform. If v₂ = v₃ = 0, then Gv = v₁ ≠ 0. So Pr[Gv = 0] ≤ 2^{−k}. Likewise Hv = Mv₁ + v₂ + Sv₃, and Pr[Hv = 0] ≤ 2^{−k} by the cases v₁ ≠ 0, then v₃ ≠ 0, then v₂ ≠ 0.

The number L of vectors of weight below d satisfies L·32^{n−d} ≤ Σ_i C(n, i) 32^{n−i} = 33ⁿ. Write n = 128d + s with s < 128. As 33^{128} ≤ 2^{11}·32^{127} and 33^s ≤ 2⁶·32^s, this gives L ≤ 2^{11d+6}. The union bound over both matrices gives failure probability at most 2·2^{11d+6}·2^{−k} = 1/2. ∎

Let U and W be the row spaces of G and H. Part 1 says ⟨U, W⟩ = 0, ⟨a_x, W⟩ = 0, ⟨U, b_y⟩ = 0, ⟨a_x, b_y⟩ = δ_xy. Part 2 says U^⊥ and W^⊥ have no nonzero vector of weight below d.

**Consequence.** For uniform u ∈ U, any d − 1 coordinates of a_x + u are uniform on F₂^{d−1}, for every x. Indeed the marginal of a coset of U on a set P of coordinates is uniform exactly when U^⊥ has no nonzero vector supported in P. The same holds for b_y + w with w ∈ W.

**Reduction.** Let N = q. For f: [N] → [N] and u_i ∈ U, w_j ∈ W, let row i of A be a_{f(i)} + u_i and column j of B be b_{f(j)} + w_j for i, j ≤ N, with all other rows of A and columns of B zero. Let C = I_N ⊕ 0. By Lemma 2, part 1,

(AB)_ij = ⟨a_{f(i)} + u_i, b_{f(j)} + w_j⟩ = [f(i) = f(j)] for i, j ≤ N,

and the other entries of AB vanish. So AB = C exactly when f is injective.

**Degree.** Take a T-query algorithm with error at most 1/3. Its acceptance probability is a multilinear polynomial P of degree at most 2T in the entries of A and B [2]. Let Φ(f) be its average over independent uniform u_i and w_j. For a monomial m, write m_i and m'_i for its parts in row i of A and column i of B. By independence, the average of m is the product over i ≤ N of g_i(f(i)), where g_i(h) = E[m_i(a_h + u)] E[m'_i(b_h + w)], times a constant for the zero rows and columns. If m_i and m'_i both have degree below d, then g_i is constant by the consequence above. Otherwise g_i(f(i)) = Σ_h g_i(h) y_ih, with y_ih = [f(i) = h]. At most 2T/d indices i are of the second kind. So Φ is a polynomial of degree at most 2T/d in the y_ih. As every (A, B) is decided with error at most 1/3, Φ(f) ≥ 2/3 when f is injective, Φ(f) ≤ 1/3 otherwise, and 0 ≤ Φ ≤ 1. So Φ approximates element distinctness on f: [N] → [N] in the sense of Definition 1 of [3].

**Conclusion.** Any such polynomial has degree Ω(N^{2/3}). For range M = Ω(N²) this is Theorem 1 of [3], which states it by reference to [4], and Theorem 2 of [3] transfers it to range N. For completeness, it also follows from the degree bound Ω(N′^{1/3}) for the collision problem on N′ points [3, 4, 7]. Let N ≥ 20, N′ = 2⌈N²/40⌉ and M ≥ 3N′/2. Theorem 2 of [3] lifts Φ to a polynomial Φ′ of the same degree on functions [N] → [M] with the same guarantees. Let Q(y) be the average of Φ′(y ∘ τ) over uniform injections τ: [N] → [N′], for y: [N′] → [M]. Then Q has the degree of Φ. On a one-to-one y, Q ≥ 2/3. On a two-to-one y, τ misses all colliding pairs with probability at most exp(−N(N − 1)/(2N′)) < 10⁻³, so Q ≤ 1/3 + (2/3)·10⁻³. On all other y, 0 ≤ Q ≤ 1. So Q approximates collision, and the degree of Φ is Ω(N′^{1/3}) = Ω(N^{2/3}). Hence 2T/d = Ω(N^{2/3}), and with d, N ≥ n/256, T = Ω(n^{5/3}). ∎

## Machine check

The F₂ case is machine-checked in `lean/MatVerify/`, with Lean 4.36.0-rc1 and Mathlib revision `d875a8de5222f62cf1c2fafc7984588adadc990a`. The files contain no `sorry`, and `MatVerify.matverify_bound` uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`):

`EDDegree → ∃ c > 0, ∀ n T S (q : QAlg n T S), q.Decides → c · n^{5/3} ≤ T + 1`.

**The one hypothesis** is `EDDegree`, the degree bound for element distinctness on functions [N] → [N], which follows from Theorems 1 and 2 of [3]. For small N, degree 0 is impossible when N ≥ 2, because a constant cannot separate injective from non-injective f, so one constant c works for all N ≥ 2. It is stated for sums of functions that each depend on at most D coordinates of f, which is the same as polynomials of degree at most D in the indicators y_ih.

**Not machine-checked:** the upper bound, which is cited; rings other than F₂; and the variant with C fixed and known. The Lean statement assumes that the algorithm decides all inputs, while its proof uses only inputs with the same C.

**What the check does not cover.** Lean checks the proof against the definitions in `lean/MatVerify/Model.lean`. There, an algorithm is a sequence of T + 1 input-independent unitaries on a finite basis, interleaved with T phase queries to single entries, started in a basis state and measured in the basis. Workspace is included in the basis, and a query may leave a basis state unchanged.

The script `sim/check_gadget.py` tests the reduction and the degree claim on small cases, for a gadget found by search.

## Other rings

A nonzero element of finite additive order gives r ≠ 0 in the ring with pr = 0, p prime. Repeat the proof over F_p. Lemma 2 holds with the same d and with k = 12d + 8, using G = [I, −Mᵀ − QSᵀ, Q], H = [M, I, S], a_x = (0, −Se_x, e_x), b_y = (−Qe_y, 0, e_y). The probabilities become p^{−k}, and there are at most 2^{11d+6} p^{d−1} ≤ p^{12d+5} vectors of weight below d. Lift row entries to {0, …, p − 1}·1_R and column entries to {0, …, p − 1}·r. Then ⟨A_i, B^j⟩ = (Σ_t a_t b_t mod p)·r, as pr = 0, and C = r(I_N ⊕ 0). Entries are then functions of F_p values, so the acceptance probability is a polynomial of degree at most 2T in the indicators of (position, value), with one indicator per position in each monomial. The degree step is unchanged. Only finitely many ring values occur, so infinite rings are not an issue. Noncommutativity is not used.

## Remarks

- The bound uses the polynomial method. Buhrman and Špalek [1] note that the adversary methods of the time cannot exceed n^{3/2} here because of small certificates, and suggest the polynomial method.
- Lower bound instances have both A and B hidden. With B known the problem costs O(n^{3/2}).
- The gadget is a CSS code: U and W are the two check spaces and a_x, b_y are logical pairs. Lemma 2 asks for the pure form, in which U^⊥ and W^⊥ have no light vector at all.

## References

[1] H. Buhrman, R. Špalek. Quantum verification of matrix products. SODA 2006. arXiv:quant-ph/0409035.

[2] R. Beals, H. Buhrman, R. Cleve, M. Mosca, R. de Wolf. Quantum lower bounds by polynomials. J. ACM 48(4), 2001.

[3] A. Ambainis. Polynomial degree and lower bounds in quantum complexity: collision and element distinctness with small range. Theory of Computing 1, 2005. arXiv:quant-ph/0305179.

[4] S. Aaronson, Y. Shi. Quantum lower bounds for the collision and the element distinctness problems. J. ACM 51(4), 2004.

[5] R. Kothari. Efficient algorithms in quantum query complexity. PhD thesis, University of Waterloo, 2014.

[6] R. Kothari, A. Nayak. Quantum algorithms for matrix multiplication and product verification. Encyclopedia of Algorithms, 2016.

[7] S. Kutin. Quantum lower bound for the collision problem with small range. Theory of Computing 1, 2005.

[8] S. Kintali. An Optimal Quantum Query Lower Bound for Matrix-Product Verification. 2026. https://shivakintali.github.io/papers/QABC.pdf

## Use of AI

Claude Opus 5.5 (Anthropic) was used throughout this research: to explore approaches, to develop and check proofs, to write the simulation scripts and the Lean formalization, and to draft the text.
