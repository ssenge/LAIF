# Two-copy measurements in the qubit bandit: no gain over the spectral measurement, by a numerically certified dual certificate

Written 11 Nov 2026.

## Problem

In [1], an arm of a quantum bandit is a qubit state ρ, and the reward is the effect F = |0⟩⟨0|. For a suboptimal arm with mean μ_k = ⟨0|ρ|0⟩ below the best mean μ⋆, the confusing set is Λ = {σ : ⟨0|σ|0⟩ ≥ μ⋆}. Write a qubit state as (I + xX + yY + zZ)/2 with state vector (x, y, z). Then Λ is z ≥ z⋆ with z⋆ = 2μ⋆ − 1.

For a measurement M on two copies, write D_2(M, σ) for the relative entropy between the outcome distributions of ρ⊗ρ and σ⊗σ. Section VII of [1] studies

V_2 = sup_M inf_{σ∈Λ} D_2(M, σ)/2,

the best per-copy exponent of a fixed two-copy measurement. The supremum runs over all finite-outcome measurements. The product spectral measurement (both copies in the basis |0⟩, |1⟩) gives V_2 ≥ K_inf, the single-copy optimum of [1, Theorem 1].

At the running instance of [1] (arm state vector (0.9, 0, 0), μ⋆ = 0.95, K_inf = 0.830366), a search over projective two-copy bases found nothing better. [1] writes that "these observations support the conjecture V_2 = K_inf at this instance, but do not prove it", and that the search "does not cover all POVMs".

## Result

**Result 1 (numerically certified).** At the instance of [1], V_2 = K_inf = 0.830366, over all two-copy measurements with any number of outcomes. The upper bound comes from an explicit dual certificate (Lemma 2). Its parts are in closed form except a finitely supported measure on a circle of states, and its one inequality (2) is checked numerically: the largest violation found is below 10⁻¹⁵. A slack δ in (2) would give V_2 ≤ K_inf + 2δ (replace Y by Y + δI). The same holds at five further instances (Check). The arm must be mixed, so that the circle consists of full-rank states.

So, up to this numerical certification, pairs of copies give no collective advantage at this instance, even with measurements that are not projective. Lemma 2 also shows that the game in which the adversary may randomise over σ has value K_inf, with μ as an optimal mixture. Together with the two-copy envelope K^(2) ≈ 0.8718 that [1] reports for a single σ, this indicates a strict gap between the sup-inf value V_2 and the inf-sup value K^(2).

## Proof

Write R = ρ⊗ρ. For a unit vector ψ in C⁴ and a state σ, put

φ_σ(ψ) = p log(p/q),  p = ⟨ψ|R|ψ⟩,  q = ⟨ψ|σ⊗σ|ψ⟩.

**Lemma 2 (weak duality).** Let μ be a probability measure on Λ, and let Y be self-adjoint on C⁴ with

⟨ψ|Y|ψ⟩ ≥ E_{σ∼μ} φ_σ(ψ) for every unit ψ.  (2)

Then V_2 ≤ tr Y/2.

*Proof.* Fix a measurement M = {E_i}. An infimum is at most an average, so inf_σ D_2(M, σ) ≤ E_μ D_2(M, σ). Write each E_i as a sum of rank-one pieces w|ψ⟩⟨ψ|. By the log-sum inequality, splitting an outcome into pieces can only increase the relative entropy. Each piece contributes w φ_σ(ψ), so E_μ D_2(M, σ) ≤ Σ w E_μ φ_σ(ψ). By (2) this is at most Σ w ⟨ψ|Y|ψ⟩ = tr Y, since the pieces sum to the identity. ∎

No minimax theorem is needed for this direction.

**The certificate.** Rotating about the z axis keeps Λ, so we may take ρ_01 real and nonnegative. Put s_0 = (1 + z⋆)/2 and s_1 = (1 − z⋆)/2, the diagonal of every state on the boundary disc z = z⋆. Put α = ρ_00/s_0 and β = ρ_11/s_1. Write G(a, b) = √(ab) for the geometric mean and L(a, b) = (a − b)/log(a/b) for the logarithmic mean.

1. *The circle.* Let C be the set of states on the disc z = z⋆ with |σ_01|² = s_0 s_1 ρ_01²/(ρ_00 ρ_11). On C, σ⊗σ and ρ⊗ρ have the same ratio between the off-diagonal and diagonal entries of the block spanned by |01⟩ and |10⟩. At the instance of [1], C has transverse radius √(0.19 · 0.81) = 0.392301.
2. *The measure.* μ is a finitely supported probability measure on C. In terms of σ_01 = |σ_01| e^{−iθ}, it has
   - E e^{iθ} = G(α, β)/L(α, β) = u/sinh u;
   - E e^{2iθ} = G(α², β²)/L(α², β²) = 2u/sinh 2u,

   with u = ½ log(α/β); the imaginary parts vanish. At the instance these are 0.713028 and 0.310802. A measure on the circle with these moments exists, since 2u/sinh 2u ≥ 2(u/sinh u)² − 1. The moments alone do not suffice: a measure with three atoms and the same moments violates (2) near e_11. The certificate of the check uses about 20 atoms, found by a linear program, and is symmetrised under y ↦ −y.
3. *The operator.* Let q_i be the diagonal of σ⊗σ on C in the product basis e_00, e_01, e_10, e_11 (the same for every σ in C), p_i = R_ii and S̄ = E_μ σ⊗σ. Define Y by its columns

   Y e_i = (log(p_i/q_i) + 1) R e_i − (p_i/q_i) S̄ e_i.

   Then tr Y = Σ_i p_i log(p_i/q_i) = 2 K_inf, because the product spectral measurement has value K_inf on the whole disc.

**Why these choices.** Equality in Lemma 2 forces structure on any certificate with tr Y = 2K_inf.
- The product spectral measurement has D_2 ≥ 2K_inf on Λ, with equality exactly on the disc z = z⋆. Since E_μ D_2 ≤ tr Y = 2K_inf for it, μ lives on the disc, and (2) must hold with equality at the four basis vectors. So the gradient of the right side of (2) at e_i must be Y e_i, which is the formula in item 3.
- Y must be self-adjoint. The entries of S̄ that this involves are s_0 E σ_01, s_1 E σ_01 and E σ_01². Self-adjointness forces E σ_01 = ρ_01/L(α, β) and E σ_01² = ρ_01²/L(α², β²). The two conditions on E σ_01 coincide because q is a product.
- A second measurement also has per-copy value K_inf: count the copies in |0⟩, and in the block spanned by |01⟩ and |10⟩ measure the symmetric and antisymmetric vectors. On the disc, its D_2 equals 2K_inf exactly on C and is larger elsewhere. Since E_μ D_2 ≤ tr Y = 2K_inf, μ must be supported on C.
- Dividing by |σ_01| on C gives the moments of item 2.

So the only freedom left is the shape of μ beyond its first two moments, and inequality (2) is what has to be checked.

**Numerical part.** The check solves a linear program for the weights of μ on 720 angles of C. It adds cutting planes at the most violated vectors ψ, until the largest violation of (2) is below 10⁻¹⁰. These vectors are found by local maximisation from 3000 random starts and from starts near the basis vectors. A fresh search of the same size confirms the result. At the instance of [1] the largest violation is 4.8 · 10⁻¹⁶. Equality holds at the product basis vectors and on the block spanned by |01⟩ and |10⟩. Away from this set the gap in (2) grows quadratically: its second derivative is positive definite on the normal directions, so small changes of μ that keep the two moments do not break (2).

## Remarks

- Every refinement of the count measurement has value at most K_inf. In the block spanned by |01⟩ and |10⟩, the compression of every σ⊗σ to the block equals σ_00σ_11 I + |σ_01|² X. So such a measurement sees only the ratio |σ_01|²/(σ_00σ_11), and on C the adversary matches it. Any gain would have to give up count information. Lemma 2 and the certificate show that at this instance no measurement gains.
- The result concerns the fixed two-copy measurement value V_2, as in Section VII of [1]. It does not address larger blocks or adaptive policies across blocks.

## Check

`sim/check.py` (about 15 minutes) checks:
1. that the product spectral measurement gives K_inf and the basis of maximally entangled vectors gives 0.345 at the instance of [1];
2. the certificate at the instance of [1]: the moments, Y self-adjoint, tr Y/2 = K_inf, and the largest violation of (2);
3. the same at the instances with arm state vector (0.6, 0, 0), (0.9, 0, 0.3), (0.5, 0, −0.5), (0.99, 0, 0), (0.3, 0, 0.2), and thresholds z⋆ = 0.9, 0.9, 0.5, 0.5, 0.95.

The output is in `sim/out.txt`.

## References

1. S. H. Ng. The Single-Copy Quantum Bandit Is Classical: An Exact Spectral Collapse. arXiv:2609.40339 (2026).
