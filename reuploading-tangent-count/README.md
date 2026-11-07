# Tangent count of re-uploading circuits: exact value 2(2^N − 1)(E + 1)

Written 7 Nov 2026.

## Problem

[1] compares re-uploading circuits with the same spectrum. A circuit on N qubits (d = 2^N) applies blocks W^(0), …, W^(L) of general SU(d) gates with encoding layers S(x) in between; each encoding gate is a rotation e^{−ixX/2} on one qubit, and E is the total number of encoding gates. The output is f(x) = ⟨0|U(x)†MU(x)|0⟩. For a coordinate θ_j of a gate (one per generator of su(d), as in [1]), the tangent-coefficient function is

h_j(x) = (⟨r|U(x)† ∂_j U(x)|0⟩)_{r = 1, …, d−1},

a vector of trigonometric polynomials of degree at most E, and T is the real span of all h_j [1, Section 4.3]. [1, Proposition 4.4] shows that dim T = 2(E + 1) for the serial circuit (one qubit, L = E) and dim T = 5E + 6 for the parallel two-qubit circuit (both qubits encoded, L = E/2), each for almost every choice of gates, with the upper bound for every choice. For the ancilla circuit (two qubits, encoding on qubit 0 only, L = E) it proves dim T ≥ 6(E + 1) for almost every choice of gates, by an argument written for any N (dim T ≥ 2(2^N − 1)(L + 1) with one encoded qubit) [1, Appendix B]; the upper bound available there is 6 + 8E, eight per layer [1, Table 3], and the value 6(E + 1) is reported from numerical checks.

## Result

**Theorem 1 (upper bound for every circuit).** For every circuit of this form on N qubits with E encoding gates, in any arrangement over the layers and with any number of gates per block, and for every choice of gates,

dim T ≤ 2(2^N − 1)(E + 1).

**Theorem 2 (one encoded qubit).** If all E encoding gates act on the same qubit (L = E, one per layer), then dim T = 2(2^N − 1)(E + 1) for almost every choice of gates. Each block adds exactly 2(2^N − 1) directions. The lower bound is the argument of [1, Appendix B]; the new part is the equality, from Theorem 1.

**Corollary 3.** For the ancilla circuit of [1], dim T ≤ 6(E + 1) for every choice of gates, with equality for almost every choice. So [1, Proposition 4.4(ii)] holds with equality, the upper bound 6 + 8E improves to 6E + 6, and for almost every choice of gates dim T exceeds the rank 2E + 1 of the coefficient Jacobian [1, Lemma 3.3] by exactly 4E + 5. The bound 2(E + 1) for the serial circuit is the case N = 1 of Theorem 1. The parallel circuit has at most 5E + 6 < 6(E + 1) for E ≥ 1, so the bound of Theorem 1 is not attained by every layout.

**Interpretation.** 2(d − 1)(E + 1) is the dimension of the unit-norm vector polynomials p(z) = Σ_{k≤E} a_k z^k in C^d (2d(E + 1) real coefficients, 2E + 1 real constraints from ‖p(z)‖ = 1 on the circle), less the global phase, near a generic point of that set (the count itself is classical). Theorem 2 says that one encoded qubit already moves the state in all of these directions.

## Proofs

Write z = e^{ix}, and let P_± be the projectors onto the eigenspaces X = ±1 of the encoded qubit. Then e^{−ixX/2} = e^{−ix/2}(P_+ + zP_−), so U(x) = e^{−iEx/2}V(z) with V a matrix polynomial of degree at most E, unitary on the circle. Write p_r(z) = V(z)|r⟩ and p = p_0. Then h_{j,r} = ⟨p_r, ∂_j p⟩ pointwise on the circle.

**Theorem 1.** Let 𝒫 be the vector polynomials of degree at most E in C^d, of real dimension 2d(E + 1), and let Γ(q) = Re⟨p, q⟩, a real trigonometric polynomial of degree at most E (a space of dimension 2E + 1). Every variation ∂_j p lies in 𝒫, since the varied circuit has the same form, and Γ(∂_j p) = 0, since ‖p‖ = 1 on the circle. So T is contained in Φ(ker Γ), with Φ(q) = (⟨p_r, q⟩)_{r≥1}. The element ip lies in ker Γ and in ker Φ, so

dim T ≤ dim ker Γ − 1 = 2d(E + 1) − rank Γ − 1.

It remains to show rank Γ = 2E + 1 for gates in a dense set. Take W^(0) mapping |0⟩ to a unit vector w in the joint eigenspace X = −1 of all encoded qubits and all other gates equal to the identity. Then p(z) = z^E w and Γ(q) = Re Σ_k ⟨w, q_k⟩ z^{k−E}, which reaches every real trigonometric polynomial of degree at most E. So a minor of order 2E + 1 of Γ, a polynomial in the gate entries, is not identically zero, and rank Γ = 2E + 1 outside its zero set, which has empty interior. There dim T ≤ 2(d − 1)(E + 1). Finally, dim T is the rank of the matrix of values of the h_j at 4E + 7 points (enough to determine trigonometric polynomials of degree E), which depends continuously on the gates, so the set where dim T exceeds the bound is open. Being disjoint from a dense set, it is empty.

**Theorem 2.** The coordinates of block ℓ give h_{Q,r}(x) = i⟨r|B_ℓ(x)† Q B_ℓ(x)|0⟩ for traceless Hermitian Q, where B_ℓ(x) = S(x)W^(ℓ−1)⋯S(x)W^(0) (for several gates in a block, conjugation by the earlier gates of the block gives the same span). Write B_ℓ(x) = e^{−iℓx/2} Σ_{k=0}^{ℓ} z^k β_k. Then β_ℓ = P_−W^(ℓ−1)P_−⋯P_−W^(0) and β_0 = P_+W^(ℓ−1)P_+⋯P_+W^(0). The block-ℓ functions have degree at most ℓ, and their coefficients at z^ℓ and z^{−ℓ} are

i(⟨β_0 r| X u⟩)_{r≥1} and i(⟨β_ℓ r| X† v⟩)_{r≥1},

with u = β_ℓ|0⟩, v = β_0|0⟩ and X = P_+QP_−, which runs over all maps from the image of P_− to the image of P_+. Take W^(1) = ⋯ = W^(ℓ−1) = I and W^(0) with W^(0)|0⟩ outside the images of P_+ and P_−. Then u, v ≠ 0, and w ↦ (⟨β_0 r|w⟩)_{r≥1} is injective on the image of P_+ (likewise for β_ℓ and P_−). In bases with u and v as first vectors, Xu is the first column of X and X†v the conjugate of its first row, and the pair is free except for the shared entry. So the map Q ↦ (top, bottom coefficients) has real rank d + d − 2 = 2(d − 1). This rank condition is again polynomial in the gates, so it holds outside a null set [1, Lemma B.1], for each ℓ = 1, …, E at once. All functions of blocks 0, …, ℓ − 1 have degree at most ℓ − 1, so block ℓ adds at least 2(d − 1) dimensions, and block 0 adds 2(d − 1) (the constants i(Q_{r0})_r fill C^{d−1}). This gives dim T ≥ 2(d − 1)(E + 1), and Theorem 1 gives equality.

## Check

`sim/check.py` (numpy, about 5 s) samples the h_j and computes dim T as a matrix rank. It checks:
- Theorem 2 block by block for N = 1 (E ≤ 5), N = 2 (E ≤ 6) and N = 3 (E ≤ 4), and with three gates per block;
- Theorem 1 for six other layouts on two and three qubits, three of which attain the bound, and the value 5E + 6 for the parallel circuit at E = 4;
- Theorem 1 at special gates (identity, sign-transform and controlled-not gates);
- rank Γ = 2E + 1 at random gates for E ≤ 6.

The output is in `sim/out.txt`.

## References

1. M. Poppel, D. Bucher, M. Zorn, M. Baumann, S. Wölckert, C. Linnhoff-Popien, P. Altmann, J. Stein. Same Spectrum, Harder First-Order Training: Phase-Locking in Single- versus Multi-Qubit Re-Uploading Circuits. arXiv:2610.21778 (2026).
