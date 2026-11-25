# Layer saturation of the variational transverse-field spin chain ansatz fails for every even chain length

2026-11-25

## Problem

On a ring of L qubits let H_X = −Σ_i X_i and H_ZZ = −Σ_i Z_i Z_{i+1} (periodic). The variational quantum-classical simulation ansatz of depth p prepares

|Ψ(γ, β)⟩ = e^{−iβ_p H_X} e^{−iγ_p H_ZZ} ⋯ e^{−iβ_1 H_X} e^{−iγ_1 H_ZZ} |+ ⋯ +⟩,  γ, β ∈ ℝ^p.

The strong form of the saturation conjecture of [1] states: for even L, every state that the ansatz prepares at some depth is also prepared at depth L/2. In [2] it fails at L = 4: an explicit state needs depth 3. The weak form (ground states of the transverse-field chain at depth L/2) is a separate statement and is not addressed here.

| chain length | depth needed by a state beyond depth L/2 |
|---|---|
| L = 4 [2] | a state that needs depth 3 |
| Theorem 1, every even L ≥ 4 | the state ψ_L below is preparable, but not at any depth p ≤ L/2 |
| Proposition 2, L = 4, 6, 8, 10 | ψ_L is prepared at depth L/2 + 1 (numerical) |

So the strong form fails for every even L ≥ 4.

## Setting: pseudospins

The free-fermion solution of the chain [3, 4] splits the ansatz into L/2 independent two-level systems, one for each momentum k_j = (2j − 1)π/L, j = 1, …, L/2. Write the state of pseudospin j as a unit direction vector w_j ∈ ℝ³. All of them start at e_x = (1, 0, 0). One layer acts on w_j by the rotation by 4γ about n_j = (cos k_j, 0, sin k_j), followed by the rotation by 4β about e_x. The overlap of two ansatz states is the product of the pseudospin overlaps (1 + w_j · w_j′)/2. So two ansatz states agree up to a phase exactly when all their direction vectors agree.

**Definition.** For even L ≥ 4, ψ_L is the ansatz state with w_j = e_x for j < L/2 and w_{L/2} = −e_x. It exists by Theorem 1(a). It is unique up to a phase by the overlap identity.

Numerically, ψ_L is the X-basis state

ψ_L ∝ Σ_{i<j} sin(π(j − i)/L) |−_i −_j⟩,

where all sites other than i and j are |+⟩. This is asserted to 10⁻⁹ for L = 4, 6, 8, 10. At L = 4 it is the state of [2].

## Results

**Theorem 1.** Let L ≥ 4 be even and k* = k_{L/2} = (L − 1)π/L.

(a) ψ_L is prepared by the ansatz at some finite depth.

(b) Let p ≤ L/2. Suppose a depth-p circuit brings the pseudospin of k* to −e_x. Then p = L/2, and 4γ_j ≡ π (mod 2π) for every j and 4β_j ≡ π (mod 2π) for every j < p. Every such circuit prepares |− ⋯ −⟩, the state with all w_j = −e_x.

In particular ψ_L is not prepared at any depth p ≤ L/2.

**Proposition 2 (numerical).** For L = 4, 6, 8, 10, ψ_L is prepared at depth L/2 + 1. The angles are listed in `sim/out_family.txt`, with residual below 2·10⁻¹⁵ in the direction vectors. With Theorem 1(b), the minimal depth of ψ_L is L/2 + 1 for these L.

## Proof

**(b), a distance bound.** Let e = −e_x and a = π/L, so that the angle between n_{L/2} and e is a. Let f(w) be the angle between w and e. Rotations about e_x keep f. For a rotation R about n = n_{L/2}, the angle between Rw and n equals the angle between w and n. The triangle inequality on the sphere, used twice, gives

f(Rw) ≥ ∠(Rw, n) − a = ∠(w, n) − a ≥ f(w) − 2a.

The start has f(e_x) = π, so after p layers f ≥ π − 2pa = π(1 − 2p/L). Reaching −e_x needs f = 0, hence p ≥ L/2. For p = L/2 both inequalities are equalities in every layer.

**(b), equality.** Let C be the great circle of the xz-plane, which contains e and n. Equality in the second inequality puts n on a shortest arc from w to e, so w lies on C on the side of e that contains n. Equality in the first puts e on a shortest arc from Rw to n, so Rw lies on C on the other side.

- *The rotations about n.* The orbit of w under rotations about n is a circle around n. It meets C in two points: w and its mirror image across n. Since f drops by 2a > 0, Rw ≠ w, so the rotation angle is π.
- *The rotations about e_x between layers.* After layer j < p the vector has f = π − 2ja ∈ [2a, π − 2a]. It has to move from one side of e on C to the other, at the same f. The orbit around e_x meets C in exactly these two points, so the rotation angle is π.
- *The first rotation.* It starts at −e and moves the vector, so its angle is π as well.

**(b), all pseudospins flip.** A rotation by π about an axis in the xz-plane maps the xz-plane to itself as the reflection across that axis. Write a vector of C by its angle φ from e_x. The reflection across n_j maps φ to 2k_j − φ, and the reflection across e_x maps φ to −φ. Starting at φ = 0, the p reflections across n_j, interleaved with p − 1 reflections across e_x, give φ = 2pk_j = (2j − 1)π. So w_j = −e_x for every j, and the last rotation about e_x fixes it.

**(a), every configuration is reached.** In the algebra of infinitesimal rotations of the L/2 pseudospins, let A = Σ_j x_j and B = Σ_j (cos k_j x_j + sin k_j z_j). Here x_j, y_j, z_j generate the rotations of pseudospin j about the three axes.

1. [A, B] is a multiple of Σ sin k_j y_j, and [A, Σ sin k_j y_j] is a multiple of D = Σ sin k_j z_j.
2. So E = B − D = Σ cos k_j x_j lies in the generated algebra.
3. Repeated brackets with E, and one more bracket with A for odd powers, give Σ_j cos^m(k_j) sin(k_j) z_j for every m ≥ 0.
4. The values cos k_j are distinct and sin k_j > 0, so the matrix (cos^m k_j) is invertible. Hence each z_j lies in the generated algebra.
5. Brackets with A then give y_j and x_j.

So A and B generate the full algebra of SO(3)^{L/2}. Both one-parameter groups e^{tA} and e^{tB} are periodic, so negative times are not needed. Products of these one-parameter groups therefore make up all of the connected compact group SO(3)^{L/2} [5]. Any element is a finite product, which is an ansatz circuit of finite depth. In particular, so is the element that rotates only pseudospin L/2 by π about the y-axis.

## Check

- `sim/reduce.py` compares the physical overlap of two random ansatz states with the product of pseudospin overlaps for L = 4, 6, 8. The difference is below 10⁻¹⁴ (asserted).
- `sim/family.py`, output in `sim/out_family.txt`:
  - finds depth L/2 + 1 preparations of ψ_L for L = 4, 6, 8, 10;
  - asserts the closed form above on the 2^L amplitudes;
  - asserts the distance bound of (b) on random depth-L/2 circuits and the all-flip of the all-π circuit, for L = 4, …, 30;
  - asserts that A and B generate an algebra of dimension 3L/2 for L = 4, …, 24.

## Scope

- Theorem 1 uses the free-fermion reduction of [3, 4] as stated. It is checked numerically for L ≤ 8 by `sim/reduce.py`.
- Proposition 2 and the closed form of ψ_L are numerical. For L ≥ 12 the minimal depth of ψ_L is not determined here; Theorem 1 gives at least L/2 + 1.
- The weak form of the conjecture of [1] is not covered.
- The statements are Claims with the listed checks.

## References

1. W. W. Ho, T. H. Hsieh. Efficient variational simulation of non-trivial quantum states. SciPost Physics 6, 029 (2019).
2. A counterexample to the Ho–Hsieh VQCS saturation conjecture. arXiv:2611.31308 (2026).
3. Z. Wang, S. Hadfield, Z. Jiang, E. G. Rieffel. Quantum approximate optimization algorithm for MaxCut: a fermionic view. Physical Review A 97, 022304 (2018).
4. G. B. Mbeng, A. Russomanno, G. E. Santoro. The quantum Ising chain for beginners (2020).
5. V. Jurdjevic, H. J. Sussmann. Control systems on Lie groups. Journal of Differential Equations 12, 313 (1972).

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
