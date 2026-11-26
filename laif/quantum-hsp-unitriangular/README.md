# Hidden subgroups of the unitriangular group U₄(F_p) in time Õ(√p)

Written 26 Nov 2026.

The group U₄(F_p) of upper unitriangular 4 × 4 matrices over F_p has order p⁶ and nilpotency class 3. It is the smallest unitriangular group of class 3. For the hidden subgroup problem (HSP) over it, efficient quantum algorithms are known only for bounded p, from the nilpotent-group algorithm of [3]. For large p, [1] reduces the problem to two hard cases and shows where the pretty good measurement fails on them. To our knowledge no algorithm with time polynomial in log p is known.

Here the two hard cases are solved in time Õ(√p), by amplitude amplification over the single unknown that blocks the semidirect-product algorithm of [2].

**Theorem 1.** For primes p ≥ 5 there is a quantum algorithm that solves the HSP over U₄(F_p) with bounded error. It makes O(√p · polylog p) queries to the hiding function and uses O(√p · polylog p) further gates.

Since |U₄(F_p)| = p⁶, this is time |G|^{1/12+o(1)}. The reduction of [1] combined with a Grover search over the hidden generator gives time Õ(p^{5/2}), and the algorithm of [3] runs in time p^{O(p log p)} for these groups.

Status: Claim. The group-theoretic steps are checked by brute force for p = 5 and p = 7 (`sim/reduction_check.py`).

## Before and after

| Problem | Previous best bound | This work |
|---|---|---|
| HSP over U₄(F_p), p prime, large | Õ(p^{5/2}), implied by [1] with a Grover search; p^{O(p log p)} [3] | Õ(p^{1/2}) |

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

In both cases it handles h ∈ K, h in the Heisenberg subgroup {z = 0} and the axis directions b₁ = 0 or c₂ = 0, by HSP algorithms for F_(1,0), F_(0,1) and the Heisenberg group of order p⁵ [2]. What remains is the case where the entries b₁ and c₂ of h (resp. h₀) are both nonzero. This is where the pretty good measurement fails [1, Section 5].

**Lemma 2.** Let b₁ and c₂ of h be nonzero and r = c₂/b₁. In case 1, H ≤ F_(1,r), and H ∩ F_(1,s) is trivial for every s ≠ r. In case 2 with h = h₀, H ≤ F_(1,r), and H ∩ F_(1,s) = ⟨h₁⟩ for every s ≠ r.

*Proof.* The powers h^k have superdiagonal k·(b₁, z, c₂), so for k ≢ 0 they lie in F_(1,s) exactly when s = r. In case 2 every element of H is h₀^k h₁^j with h₁ ∈ U₄′ ≤ K, and the same argument applies. ∎

**Lemma 3.** Conjugation σ_r by diag(1, 1, 1, r) is an automorphism of U₄ that maps F_(1,r) onto F_(1,1).

*Proof.* It multiplies the entry in row i and column j by t_i/t_j, so it fixes b₁ and divides c₂ by r. ∎

## 3. The algorithm

For a candidate r ∈ F_p^*, restrict the hiding function f ∘ σ_r^{−1} to the fixed group F_(1,1) ≅ F_p⁴ ⋊ Z_p. It hides σ_r(H ∩ F_(1,r)). The algorithm of [2] for F_p^m ⋊ Z_p with fixed m finds this subgroup with bounded error in time polylog p. By Lemma 2 its output contains an element outside the known part (trivial in case 1, ⟨h₁⟩ in case 2) only when r is the right ratio. One query, f(x) = f(e), verifies such an element.

So the right ratio is the unique marked item among the p − 1 candidates, and a run marks it with probability at least 2/3. Amplitude amplification with unknown success probability [4] finds it after O(√p) coherent runs, each of cost polylog p. If no run succeeds, H is trivial in case 1 and H = ⟨h₁⟩ in case 2. For the right r the run of [2] returns σ_r(H), and σ_r^{−1} gives H.

## 4. Script

`sim/reduction_check.py` checks by brute force, for p = 5 and p = 7, all of the following:

- the group law and that every element has order dividing p;
- that K is abelian and normal;
- that F_(1,r) is a subgroup of order p⁵ and σ_r maps it onto F_(1,1);
- for every element h with b₁, z and c₂ all nonzero (8000 elements for p = 5, 74088 for p = 7), that ⟨h⟩ lies in F_(1,r) exactly for r = c₂/b₁ and meets every other F_(1,s) trivially;
- on 200 random instances of case 2, that H meets F_(1,s) in ⟨h₁⟩ for s ≠ r.

## 5. Limits

- The algorithm is not polynomial in log p. A polynomial-time algorithm would have to find the ratio r, the image of H in U₄/K ≅ F_p², directly. That is the question of producing coset states of HK, and it remains open.
- The run on F_(1,1) uses the algorithm of [2] for F_p^m ⋊ Z_p with m = 4, where F_(1,1) acts on K by one Jordan block of size 3 and one of size 1.
- Not formalized: the whole argument. The script checks the group-theoretic steps for p = 5 and p = 7 only.

## References

1. D. Poquillon. Perspectives on the hidden subgroup problem over unitriangular groups. arXiv:2611.23590 (2026).
2. D. Bacon, A. M. Childs, W. van Dam. From optimal measurement to efficient quantum algorithms for the hidden subgroup problem over semidirect product groups. FOCS 2005, arXiv:quant-ph/0504083.
3. M. Imran, G. Ivanyos. Zero sum subsequences and hidden subgroups. arXiv:2304.08376 (2023).
4. G. Brassard, P. Høyer, M. Mosca, A. Tapp. Quantum amplitude amplification and estimation. Contemporary Mathematics 305 (2002), arXiv:quant-ph/0005055.

## Use of AI

The algorithm, the analysis, the script and this text were produced with the help of Claude Opus 5.5.
