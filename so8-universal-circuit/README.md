# A universal SO(8) circuit with the optimal number of CZ gates, through triality

Written 7 Nov 2026.

## Problem

[1] gives brick wall circuits of CZ gates and one-qubit rotations that use the minimal number of parameters and of two-qubit gates for SU(2^n), SO(2^n) and the symplectic group, and conjectures that they are universal. For SO(8), on three qubits, the circuit has three Y rotations, then 13 bricks, each a CZ gate followed by a Y rotation on both of its qubits, alternating between the qubit pairs (0, 1) and (1, 2); the last brick keeps only the rotation on qubit 0. This is 28 = dim SO(8) parameters and 13 CZ gates, both minimal by [1, Eq. (A1)]. [1] reports that three of its ten random SO(8) targets could not be compiled to this circuit from any start, and calls the evidence for SO(8) less conclusive than for the other groups. Its route to a proof of universality needs [1, Conjecture 3], that the critical values of such a circuit have dimension at most d − 2. [2] gives a counterexample for a circuit of 15 rotations about two-qubit strings that is onto SU(4).

This note uses triality of SO(8) [4] to turn three-qubit circuits of CZ gates and Y rotations into networks of rotations in coordinate planes. In that form, a small change of the brick order gives a circuit with 13 CZ gates and 28 parameters that is provably universal for SO(8).

## Result

**Notation.** Qubit 0 is the leftmost tensor factor, RY_q(t) = e^{−itY_q/2} is a real rotation, and a circuit with d rotations and angles x ∈ T^d = (ℝ/4πℤ)^d gives F(x) ∈ SO(8). Strings are tensor products of I, X, Y, Z. Let S+ be a half-spin representation of SO(8): γ_1, …, γ_8 are anticommuting real symmetric 16 × 16 matrices, S+ is the +1 eigenspace of γ_1 ⋯ γ_8, and an antisymmetric 8 × 8 matrix A acts on S+ as ¼ Σ A_ij γ_i γ_j. Exponentiating gives a map ρ+ from the spin group to SO(S+), and each gate of a circuit has a lift, so a circuit gives F+(x) ∈ SO(S+). For an edge e = {a, b} with a < b and a basis l_0, …, l_7, G_e(t) is the rotation by t in the plane of l_a and l_b, from l_a toward l_b. The derivative matrix J of a circuit has one column per rotation: the coefficients of V_k Y_q V_k^T in the strings with an odd number of Y, computed as tr(P V_k Y_q V_k^T)/8, where V_k is the part of the circuit after rotation k. The loss of x for a target U is 1 − tr(U^T F(x))/8.

**Theorem 1 (half-spin form).** There is an orthonormal basis l_0, …, l_7 of S+ with the following properties.

- For each qubit q, the lift of RY_q(t) acts on S+ as G_e(t) for one edge e. The lift of each CZ gate permutes the basis up to signs.
- So for every three-qubit circuit of CZ gates and Y rotations, F+(x) = K · G_{e_d}(±x_d) ⋯ G_{e_1}(±x_1), with a fixed K and edges e_k and signs given by the circuit. The edges that can occur form a cube graph on the eight basis vectors; each circuit uses some of them.
- F is onto SO(8) if and only if every element of SO(S+) lies in F+(T^d) or in −F+(T^d).

**Theorem 2 (a universal circuit).** Take three Y rotations, then 13 bricks on the qubit pairs

(0, 1), (1, 2), (1, 2), (0, 1), (0, 1), (1, 2), (1, 2), (0, 1), (0, 1), (1, 2), (1, 2), (0, 1), (0, 1),

each a CZ gate followed by a Y rotation on both qubits, except that the last brick keeps only the rotation on qubit 1 (where [1] keeps qubit 0). This is the circuit of [1] with the bricks after the first one taken in pairs. It has 28 parameters and 13 CZ gates, both minimal by [1, Eq. (A1)], and nearest neighbour connectivity. Every element of SO(8) is F(x) for some x.

**Theorem 3 (the circuit of [1]).**

- Its word uses all 8 edges of a cycle through the eight basis vectors, while every word of the kind used in Theorem 2 uses the 7 edges of a path.
- It has a fold point: at x0 = (π/4)(5, 7, 0, 0, 7, 6, 3, 1, 3, 0, 6, 0, 3, 5, 6, 6, 2, 7, 6, 7, 6, 3, 6, 0, 0, 5, 1, 2), the derivative matrix J has entries in ℚ(√2), rank 27 with σ_27 = 0.170, and κ = u^T (∂_v J) v ≠ 0 for its null vectors u and v, with |κ| = 0.0452 for unit ones (κ as in [3]). So F(C) contains a 27-dimensional piece, and [1, Conjecture 3] does not hold for this circuit.

**The targets of [1].** The check samples the ten SO(8) targets as the code of [1] does. Here are the results with least squares from random starts:

| Circuit | Targets 0, 2, 3 and 6 to 9 | Targets 1, 4, 5 |
|---|---|---|
| circuit of [1] | loss below 10⁻²², within 20 starts | best loss 1.2 · 10⁻⁴, 3.8 · 10⁻³, 1.5 · 10⁻³ after 120 starts each |
| paired circuit (Theorem 2) | loss below 10⁻²², first start | loss below 10⁻²², first start |

The three hard targets are the same three, by the costs stored in the code repository of [1]. At the best points found for them, J has one singular value below 10⁻⁸ and the next one above 0.08, and |κ| is between 0.069 and 0.093 for unit null vectors, so up to numerical precision these are fold points. The residual is parallel to the missed direction u, as stationarity requires at such a point. This is what one expects if these targets lie outside the image of the circuit of [1], beyond a fold, but the numerics do not prove it. For the paired circuit, 100 further uniform targets also reach loss below 10⁻²¹ from the first start.

## Proof

**Theorem 1.** The check builds γ_1, …, γ_8 from eight anticommuting symmetric real strings on four qubits and confirms the following.

- The map A ↦ ¼ Σ A_ij γ_i γ_j on S+ preserves commutators.
- The generator of RY_q is −iY_q/2, whose eigenvalues are ±i/2, four times each. Its image on S+ has rank 2 with eigenvalues ±i. This is triality: the three generators, which rotate four planes at once on ℝ⁸, rotate a single plane on S+.
- CZ_ab is the rotation by π in the plane of the two basis vectors where it is −1. Its lift is a signed permutation of a basis l_0, …, l_7, in which the planes of the three generators, moved by these permutations, give exactly 12 coordinate planes: the edges of a cube graph.

Moving every fixed element to the left conjugates each rotation by a signed permutation, which gives the product form.

For the last claim, let F̃ be the lift of F to the spin group, so that F = ρ(F̃) for the vector representation ρ and F+ = ρ+(F̃). The shift x_k ↦ x_k + 2π changes RY_q to −RY_q on ℝ⁸ and leaves its action on S+ unchanged. On the spin group it multiplies F̃ by a central element ω with ρ(ω) = −1 and ρ+(ω) = 1, so F̃(T^d) ω = F̃(T^d). The kernel of ρ+ is {1, ω}. The element −1 of the spin group is central and different from ω, so ρ+(−1) is a central element of SO(S+) of order 2, which is −1. So:

- F is onto exactly when F̃(T^d) · {±1} is the whole spin group;
- this set is invariant under {1, ω}, so it is the whole group exactly when its image under ρ+ is SO(S+);
- that image is F+(T^d) ∪ −F+(T^d). □

**Theorem 2.** The check computes the word of the paired circuit. Its edges are the 7 edges of the path l_0, l_1, l_3, l_5, l_7, l_6, l_4, l_2. Order the basis along this path. Then each letter is an adjacent transposition, and the product of the 28 transpositions is the reversal of the eight positions, which has 28 inversions. So the word is a reduced word of the longest permutation. Let C(x) be the product of the rotations G_{e_k}(±x_k). Three facts give C(T^28) = SO(8).

- **A nested word.** Write p_0, …, p_7 for the basis in path order. Take the word that applies a nested word for p_0, …, p_6 and then the rotations in the planes (p_6, p_7), (p_5, p_6), …, (p_0, p_1). It is a reduced word of the reversal. Its image is SO(8) by induction [5]: the last seven rotations map p_7 to every unit vector by spherical coordinates, and what remains fixes p_7.
- **Moves keep the image.** Rotations in disjoint planes commute. Three rotations in the planes (i, i+1), (i+1, i+2), (i, i+1) parametrize all of SO(3) on these three coordinates, and so do (i+1, i+2), (i, i+1), (i+1, i+2). The image of a word is the product of the images of consecutive pieces, so a braid or commutation move does not change it.
- **Word property.** Any two reduced words of the same permutation are connected by braid and commutation moves [6, 7].

The signs ±x_k are a change of parameters. So F+(T^28) = K · SO(8) = SO(S+), and F is onto by Theorem 1. □

**Theorem 3.** The check computes the word and finds 8 distinct edges, each vertex on two of them, connected: a cycle. A reduced word of the reversal on a path has exactly 7 distinct edges, the path's. The fold conditions are checked in exact arithmetic as in [3]: the conjugation action of each gate on strings has entries in {0, ±1, ±cos t, ±sin t}, which at t ∈ (π/4)ℤ lie in ℚ(√2). The check finds rank 27, null vectors u and v, and u^T (∂_v J) v = −√2 for its unnormalized null vectors. Then F(C) contains a 27-dimensional embedded piece through F(x0) [3]. □

## Remarks

1. **Scope.**
   - Triality exists only for SO(8), so the method covers n = 3 and the group SO(8). The circuits of [1] for SO(16) and SO(32), and for SU(2^n) and the symplectic groups, are not treated.
   - That the circuit of [1] misses the three targets is a numerical observation, not a theorem.
2. **Other circuits.** Among circuits of this shape (three Y rotations, 13 bricks, one of the 29 rotations left out), 8 with nearest neighbour CZ gates have a reduced word on a path, and 24 when CZ gates on all three pairs are allowed. All 8 take the bricks in pairs. The paired circuit is the only one of them that, like the circuit of [1], starts with a CZ gate on (0, 1) and leaves out a rotation of the last brick.
3. **Compilation.** The proof gives a direct compiler for the paired circuit. Lift the target U to SO(S+) through a real logarithm, write the result along the nested word by elimination one coordinate at a time, then apply the moves that lead to the word of the circuit, solving each braid move on three coordinates in closed form; if the angles give −U, shift one of them by 2π. The check runs this on 235 targets with largest entrywise error 1.4 · 10⁻¹³. Least squares also works for this circuit: every target tried converged from its first start.

## Check

`sim/so8_check.py` runs in about 2 minutes with numpy and scipy. It verifies Theorems 1 to 3, enumerates the circuits of Remark 2, and runs both compilation experiments.

```
half-spin form: Y rotations act on S+ as rotations in coordinate planes of one basis; 12 planes = edges of a cube graph [(0, 1), (0, 2), (0, 6), (1, 3), (1, 7), (2, 3), (2, 4), (3, 5), (4, 5), (4, 6), (5, 7), (6, 7)]; CZ images are signed permutations
circuit of [1]: word of 28 rotations on the 8 edges of a cycle through all vertices
paired circuit: word of 28 rotations on the 7 edges of the path [0, 1, 3, 5, 7, 6, 4, 2]; as adjacent transpositions its product is the reversal with 28 inversions, so the word is reduced
circuits of this shape with a reduced word on a path: 8 with CZ on (0, 1), (1, 2), 24 with all three pairs; the 8 take the bricks in pairs, and the paired circuit is the only one of them that starts with CZ_01 and leaves out a rotation of the last brick, as the circuit of [1] does
fold of the circuit of [1] at x = (pi/4) [5, 7, 0, 0, 7, 6, 3, 1, 3, 0, 6, 0, 3, 5, 6, 6, 2, 7, 6, 7, 6, 3, 6, 0, 0, 5, 1, 2]: exact over Q(sqrt 2), rank J = 27, sigma_27 = 0.170, u^T (d_v J) v = 0 + -1 sqrt2 for the null vectors of the check, -0.0452 for unit ones
circuit of [1], the 10 targets of [1] (best loss, starts): 2.1e-26 (1), 1.2e-04 (120), 3.4e-23 (4), 4.0e-26 (20), 3.8e-03 (120), 1.5e-03 (120), 3.1e-26 (1), 3.8e-26 (1), 8.7e-27 (1), 1.2e-27 (1)
  target 1: at the best point sigma_min(J) = 7.0e-11, sigma_27 = 0.081, |kappa| = 0.080 for unit null vectors, |cos(residual, u)| = 1.000000
  target 4: at the best point sigma_min(J) = 5.2e-10, sigma_27 = 0.165, |kappa| = 0.069 for unit null vectors, |cos(residual, u)| = 1.000000
  target 5: at the best point sigma_min(J) = 2.3e-09, sigma_27 = 0.181, |kappa| = 0.093 for unit null vectors, |cos(residual, u)| = 1.000000
paired circuit, the 10 targets of [1]: 2.6e-24 (1), 1.4e-24 (1), 1.4e-25 (1), 4.5e-26 (1), 5.1e-26 (1), 2.7e-26 (1), 3.1e-26 (1), 3.2e-25 (1), 2.1e-23 (1), 8.1e-26 (1)
paired circuit, 100 uniform targets: largest loss 4.0e-22, starts used at most 1
exact compilation into the paired circuit (lift, nested word, moves): 235 targets (the 10 of [1], 25 special ones, 200 uniform), largest max |F(x) - U| = 1.4e-13
all checks pass
```

## References

1. D. Wierichs, K. Kottmann, N. Killoran. Unitary synthesis with optimal brick wall circuits. arXiv:2511.16736 (2025).
2. The Omega Institute. trureturing, issue #15435 and pull request #15606, github.com/the-omega-institute/trureturing (11 Oct 2026).
3. Spurious local minima at fold points of parametrized quantum circuits. This repository, folder pqc-fold-traps (2026).
4. É. Cartan. Le principe de dualité et la théorie des groupes simples et semi-simples. Bulletin des Sciences Mathématiques 49, 361 (1925).
5. A. Hurwitz. Über die Erzeugung der Invarianten durch Integration. Nachrichten der Gesellschaft der Wissenschaften zu Göttingen, Mathematisch-Physikalische Klasse, 71 (1897).
6. H. Matsumoto. Générateurs et relations des groupes de Weyl généralisés. Comptes Rendus de l'Académie des Sciences Paris 258, 3419 (1964).
7. J. Tits. Le problème des mots dans les groupes de Coxeter. Symposia Mathematica 1, 175 (1969).
