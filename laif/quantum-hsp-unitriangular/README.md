# Hidden subgroups of the unitriangular group U₄(F_p) in time Õ(√p)

Written 26 Nov 2026.

The group U₄(F_p) of upper unitriangular 4 × 4 matrices over F_p has order p⁶ and nilpotency class 3. It is the smallest unitriangular group of class 3. For the hidden subgroup problem (HSP) over it, efficient quantum algorithms are known only for bounded p, from the nilpotent-group algorithm of [3]. For large p, [1] reduces the problem to two hard cases and shows where the pretty good measurement fails on them. To our knowledge no algorithm with time polynomial in log p is known.

Here the two hard cases are solved in time Õ(√p), by amplitude amplification over the single unknown that blocks the semidirect-product algorithm of [2].

**Theorem 1.** For primes p ≥ 5 there is a quantum algorithm that solves the HSP over U₄(F_p) with bounded error. It makes O(√p · polylog p) queries to the hiding function and uses O(√p · polylog p) further gates.

Since |U₄(F_p)| = p⁶, this is time |G|^{1/12+o(1)}. The query complexity of the HSP is polylog |G| for every group [7], so the comparison is about time. The reduction of [1] combined with quantum collision finding for p-to-1 functions [6] finds the hard cases in time Õ(p^{5/3}) with quantum random access memory, and the algorithm of [3] runs in time p^{O(p log p)} for these groups.

Status: Claim. Lemmas 2 and 3 are checked in Lean (`lean/UnitriHSP.lean`), and the group-theoretic steps by brute force for p = 5 and p = 7 (`sim/reduction_check.py`).

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| HSP over U₄(F_p), p prime, large (time) | Õ(p^{5/3}) with quantum random access memory, implied by [1] with [6]; p^{O(p log p)} [3] | Õ(p^{1/2}), no quantum random access memory |

## 1. Notation

Write an element as g = (b₁, z, c₂, b₂, c₁, a) for the matrix with first row (1, b₁, b₂, a), second row (0, 1, z, c₁) and third row (0, 0, 1, c₂). Then:

- The superdiagonal (b₁, z, c₂) is additive under multiplication, so g ↦ (b₁, z, c₂) is a homomorphism onto F_p³.
- K = {b₁ = c₂ = 0} is the abelian normal subgroup of the top-right 2 × 2 block, K ≅ F_p⁴, and U₄/K ≅ F_p² through (b₁, c₂).
- For p ≥ 5 every element other than the identity has order p.

For a direction δ ∈ F_p² \ {0}, let F_δ be the preimage of the line F_p·δ. It is a subgroup of order p⁵, K is normal in it, and F_δ = K ⋊ ⟨d⟩ for any d ∈ F_δ \ K, so F_δ ≅ F_p⁴ ⋊ Z_p.

## 2. The hard cases

The algorithm of [1, Proposition 2] runs in time polylog p. It finds H, or it reduces to one of two cases:

1. H = ⟨h⟩ is cyclic of order p, or trivial.
2. H = ⟨h₀, h₁⟩, where h₁ ∈ U₄′ is known and h₀ commutes with h₁.

In both cases it handles h ∈ K, h in the Heisenberg subgroup {z = 0} and the axis directions b₁ = 0 or c₂ = 0, by the algorithm of [2] for F_(1,0) and F_(0,1) and the algorithm of [5] for the Heisenberg group of order p⁵. What remains is the case where the entries b₁ and c₂ of h (resp. h₀) are both nonzero. This is where the pretty good measurement fails [1, Section 5].

**Lemma 2.** Let b₁ and c₂ of h be nonzero and r = c₂/b₁. In case 1, H ≤ F_(1,r), and H ∩ F_(1,s) is trivial for every s ≠ r. In case 2 with h = h₀, H ≤ F_(1,r), and H ∩ F_(1,s) = ⟨h₁⟩ for every s ≠ r.

*Proof.* The powers h^k have superdiagonal k·(b₁, z, c₂), so for k ≢ 0 they lie in F_(1,s) exactly when s = r. In case 2 every element of H is h₀^k h₁^j with h₁ ∈ U₄′ ≤ K, and the same argument applies. ∎

**Lemma 3.** Conjugation σ_r by diag(1, 1, 1, r) is an automorphism of U₄ that maps F_(1,r) onto F_(1,1).

*Proof.* It multiplies the entry in row i and column j by t_i/t_j, so it fixes b₁ and divides c₂ by r. ∎

## 3. The algorithm

For a candidate r ∈ F_p^*, restrict the hiding function f ∘ σ_r^{−1} to the fixed group F_(1,1) ≅ F_p⁴ ⋊ Z_p. It hides σ_r(H ∩ F_(1,r)). The algorithm of [2, Theorem 6] for F_p^m ⋊ Z_p with fixed m and any action finds this subgroup with bounded error in time polylog p. By Lemma 2 its output contains an element outside the known part (trivial in case 1, ⟨h₁⟩ in case 2) only when r is the right ratio. One query, f(x) = f(e), verifies such an element.

So the right ratio is the unique marked item among the p − 1 candidates, and a run marks it with probability at least 2/3. Amplitude amplification with unknown success probability [4] finds it after O(√p) coherent runs, each of cost polylog p. If no run succeeds, H is trivial in case 1 and H = ⟨h₁⟩ in case 2. For the right r the run of [2] returns σ_r(H), and σ_r^{−1} gives H.

## 4. Lean

`lean/UnitriHSP.lean` (Lean 4, Mathlib, standard axioms only, `lean/axioms.txt`) works in the coordinates of Section 1 over `ZMod p`, p prime:

- `mul_eq_matrix`: the coordinate product is the matrix product;
- `pw_b1`, `pw_c2`, `pw_inF_iff`, `direction_unique`: a power h^k with k ≢ 0 lies in F_(1,s) exactly when s·b₁ = c₂, and for b₁ ≠ 0 only one s works (Lemma 2, case 1);
- `inF_mul_K`: multiplying by an element of K does not change membership in F_(1,s) (Lemma 2, case 2);
- `inF_mul`: F_(1,s) is closed under the product;
- `sigma_mul`, `sigma_eq_conj`, `sigma_inF`: σ_r is conjugation by diag(1, 1, 1, r), respects the product and maps F_(1,r) onto F_(1,1) (Lemma 3);
- `example_instance`: for p = 5 an element with b₁ = 2, z = 1, c₂ = 1 lies in F_(1,3) and not in F_(1,2), so the notions are not vacuous.

## 5. Script

`sim/reduction_check.py` checks by brute force, for p = 5 and p = 7, all of the following:

- the group law and that every element has order dividing p;
- that K is abelian and normal;
- that F_(1,r) is a subgroup of order p⁵ and σ_r maps it onto F_(1,1);
- for every element h with b₁, z and c₂ all nonzero (8000 elements for p = 5, 74088 for p = 7), that ⟨h⟩ lies in F_(1,r) exactly for r = c₂/b₁ and meets every other F_(1,s) trivially;
- on 200 random instances of case 2, that H meets F_(1,s) in ⟨h₁⟩ for s ≠ r.

## 6. Limits

- The algorithm is not polynomial in log p. A polynomial-time algorithm would have to find the ratio r, the image of H in U₄/K ≅ F_p², directly. That is the question of producing coset states of HK, and it remains open.
- The run on F_(1,1) uses [2, Theorem 6] with m = 4. There Z_p acts on K by one Jordan block of size 3 and one of size 1, so F_(1,1) has class 3, while F_(1,0) and F_(0,1) have class 2.
- Not formalized: the reduction of [1], the algorithms of [2] and [5], and the amplitude amplification step. Lean covers Lemmas 2 and 3.

## References

1. D. Poquillon. Perspectives on the hidden subgroup problem over unitriangular groups. arXiv:2611.23590 (2026).
2. D. Bacon, A. M. Childs, W. van Dam. From optimal measurement to efficient quantum algorithms for the hidden subgroup problem over semidirect product groups. FOCS 2005, arXiv:quant-ph/0504083.
3. M. Imran, G. Ivanyos. Zero sum subsequences and hidden subgroups. arXiv:2304.08376 (2023).
4. G. Brassard, P. Høyer, M. Mosca, A. Tapp. Quantum amplitude amplification and estimation. Contemporary Mathematics 305 (2002), arXiv:quant-ph/0005055.
5. H. Krovi, M. Rötteler. An efficient quantum algorithm for the hidden subgroup problem over Weyl-Heisenberg groups. Quantum Information and Computation 8 (2008), 330-351.
6. G. Brassard, P. Høyer, A. Tapp. Quantum cryptanalysis of hash and claw-free functions. LATIN 1998, arXiv:quant-ph/9705002.
7. M. Ettinger, P. Høyer, E. Knill. The quantum query complexity of the hidden subgroup problem is polynomial. Information Processing Letters 91 (2004), arXiv:quant-ph/0401083.

## Use of AI

The algorithm, the analysis, the script and this text were produced with the help of Claude Opus 5.5.
