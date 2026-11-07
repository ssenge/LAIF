# Spurious local minima at fold points of parametrized quantum circuits

Written 6 Nov 2026. Theorem 3 added 7 Nov 2026.

## Problem

A parametrized quantum circuit (PQC) in the sense of [1, Definition 1] consists of stabilizer gates and d rotations e^{−itP/2} with P ∈ {X, Y, Z} on one qubit, one parameter per rotation. Strings are tensor products of the one-qubit matrices I, X, Y, Z, and stabilizer gates map strings to strings, up to sign, under conjugation. It gives a map F: T^d → G into a compact matrix group, such as SU(D) with D = 2^n. Let J(x) be its derivative matrix and C = {x : rank J(x) < d} the critical set.

**The conjecture.** [1] proves that if J has full rank at one point, then it has full rank almost everywhere [1, Lemma 2]. For a proof of universality of its brick wall circuits, [1] then needs [1, Conjecture 3]: for d = dim G, the critical values F(C) of a PQC that has full rank almost everywhere form an at most (d − 2)-dimensional subset of G. [5] gives a counterexample on two qubits: a circuit with the 15 strings once each and a fold point at angles in {0, π/4}, with a Lean proof, reported there, that F(C) then has dimension at least 14.

**Local minima.** For a target U_t, the compilation loss is L(x) = 1 − Re tr(U_t† F(x))/D. A local minimum with L > 0 is spurious when another parameter reaches L = 0. Spurious minima are known for underparametrized circuits [3]. Overparametrization, the saturation of the rank, is associated with their disappearance [2].

This note asks what a fold point does to the loss landscape. The answer: at every fold point of a PQC with d = dim SU(D), targets moved slightly off F(x0) to the side the nearby parameters miss give strict local minima, and these are spurious whenever F(x0) also has a regular preimage. The note also gives a certified fold point of the SU(8) brick wall circuit of [1] itself, so [1, Conjecture 3] does not hold for that circuit, and finds such spurious minima next to it.

## Result

**Notation.** Let R_P(t) = e^{−itP/2} for a string P, and F(x) = R_{P_d}(x_d) ⋯ R_{P_1}(x_1) with stabilizer gates absorbed into the words. Write H_k = V_k P_k V_k† with V_k = R_{P_d}(x_d) ⋯ R_{P_{k+1}}(x_{k+1}), so ∂_k F = −(i/2) H_k F. Let J(x) be the d × d matrix whose k-th column holds the string coefficients tr(P_w H_k)/D of H_k. A point x0 with rank J(x0) = d − 1 is a fold point when κ = u^T (∂_v J)(x0) v ≠ 0, where v and u are unit right and left null vectors of J(x0). Changing the sign of u changes the sign of κ.

**Theorem 1 (the fold of [5], exact).** Take the 15 words (ZZ, XI, YX, YI, ZI, XZ, IX, YZ, XY, IZ, ZX, ZY, XX, IY, YY), the first acting first, and x0 with x_5 = x_8 = x_9 = x_10 = π/4 and all other coordinates 0 (counting from 1). This is the witness of [5] in the order used here. At x0 every entry of J and of ∂_j J lies in ℚ(√2), and:

- rank J(x0) = 14, with σ_14(J(x0)) = 0.541;
- κ = −√6/21 for the null vector u of the check.

So x0 is a fold point. J has rank 15 at random points, so full rank almost everywhere.

**Theorem 2 (spurious minima at fold points).** Let x0 be a fold point of a PQC F: T^d → SU(D) with d = D² − 1, with u, v and κ as above. Let W = Σ_w u_w P_w and U_ε = e^{−iεW/2} F(x0).

- **Traps.** If εκ < 0 and |ε| is small enough, then L_ε, the loss for the target U_ε, is strictly convex on a ball of radius of order |ε| around x0. Its unique critical point there is a strict local minimum within O(|ε|³) of x0, with value 1 − tr cos(εW/2)/D + O(ε⁶) = ε²/8 − ε⁴ tr(W⁴)/(384 D) + O(ε⁶).
- **The other side.** If εκ > 0 and |ε| is small enough, the second-derivative matrix of L_ε at x0 has a negative eigenvalue, and U_ε has two preimages within O(|ε|^{1/2}) of x0.
- **Spuriousness.** If F(x0) also has a regular preimage x1, then for small |ε| the target U_ε has a preimage near x1. So the local minimum is spurious.

**The instance.** For the fold of Theorem 1, F(x0) has a regular preimage x1, with smallest singular value 0.245 of J(x1). For ε = 10⁻², 10⁻³ and 10⁻⁴ on the trap side, the check finds the strict local minimum of Theorem 2 and a parameter with loss below 10⁻¹⁵. So these targets have spurious local minima at loss ε²/8, at the critical parameter count d = dim SU(4) and with rank saturated almost everywhere.

**Theorem 3 (a fold of the SU(8) brick wall of [1]).** Take the SU(8) circuit of [1]: RZ, RY and RZ on each of the three qubits, then 14 bricks on the qubit pairs (0, 1), (1, 2), (0, 1), …, each CZ followed by RY on both qubits and RZ on both qubits, except that the last brick keeps only the two RY. It has d = 63 = dim SU(8) rotations and 14 CZ gates. Fix all angles except x_36 (counting from 1; the RZ on qubit 0 in the 7th brick) at the double precision values listed in the check. Then there is t* in an interval of width 1.4 · 10⁻⁴³ around 5.0230182363654284306 such that the point x* with x_36 = t* is a fold point. There, σ_62 = 0.0205 and κ = −0.0232 for unit null vectors (floating point).

So F(C) contains a 62-dimensional embedded piece through F(x*), and [1, Conjecture 3] does not hold for this circuit; J has full rank almost everywhere, since det J changes sign at x*.

**The instance for the brick wall (floating point).** Let x0 be the double precision point nearest to x*. F(x0) has a regular preimage x1, found by least squares from the first random start (max |F(x1) − F(x*)| = 7 · 10⁻¹⁵, smallest singular value 0.021 of J(x1)). For ε = 10⁻³ and 10⁻⁴ on the trap side, the check finds the strict local minimum of Theorem 2, at loss ε²/8 to within 10⁻⁵ relative, with smallest second-derivative eigenvalue |εκ|/4 to within 1%, while a parameter near x1 reaches loss below 10⁻¹⁴. So the brick wall circuit of [1] for SU(8) has compilation targets with spurious strict local minima.

## Proof

**Fold conditions.** At a point x0 of corank one, adj J(x0) = c v u^T with c = ± σ_1 ⋯ σ_{d−1} ≠ 0. So for every direction w,

∂_w det J(x0) = tr(adj J(x0) ∂_w J(x0)) = c u^T (∂_w J)(x0) v.

- With w = v this gives ∂_v det J(x0) = cκ ≠ 0. So C = {det J = 0} is a smooth hypersurface near x0.
- Its tangent space at x0 is the kernel of ∇ det J(x0), which does not contain v. So ker J(x0) is transverse to C, and F restricted to C is an immersion at x0. These are the conditions of a fold [4], and F(C) contains a (d − 1)-dimensional embedded submanifold through F(x0).

**Proof of Theorem 1.** For anticommuting strings P and Q, R_P(t) Q R_P(t)† = cos t Q − i sin t PQ, and commuting words are fixed. So the adjoint action of each gate on string coefficients is a matrix with entries in {0, 1, ±cos t, ±sin t}, and at t ∈ {0, π/4} these lie in ℚ(√2). The columns of J(x0) and of each ∂_j J(x0) are products of such matrices applied to a unit vector. The check computes them in exact arithmetic, finds rank 14, null vectors u and v, and κ = −√6/21. □

**Proof of Theorem 3.** Write g = det J, and for a fixed index j let w(x) = adj J(x) e_j and h(x) = tr(adj J(x) ∂_{w(x)} J(x)), all as functions of t = x_36 with the other angles fixed.

- **A fold where h ≠ 0.** Suppose g(t*) = 0 and h(t*) ≠ 0. Then adj J(t*) ≠ 0, so rank J(t*) = 62 and adj J(t*) = c v u^T with c ≠ 0. So w = c u_j v and h = c u^T (∂_w J) v = c² u_j κ, hence κ ≠ 0: a fold point.
- **Bounds.** Every column of J has norm 1, since H_k is a unitary conjugate of a string. Every column of a first or second derivative of J has norm at most 1, since differentiating the action of one rotation maps cos t Q + sin t R to a vector of the same norm and kills commuting strings. By the determinant bound through column norms, every entry of adj J has modulus at most 1, and every entry of its derivative along t has modulus at most 62, since that derivative is a sum of 62 determinants with one column differentiated. With |tr(A B)| ≤ max|A_ij| Σ|B_ij| and Σ|B_ij| ≤ d^{3/2} for a matrix with columns of norm at most 1, the product rule gives |h′(t)| ≤ 125 d^{5/2} for every t.
- **Certificate.** The check finds a and b = a + 1.4 · 10⁻⁴³ such that, in interval arithmetic at 160 digits, g(a) and g(b) have opposite signs and |h(a)| ≥ 2.1 · 10⁻³³ > (b − a) · 125 d³. So h has no zero on [a, b], g has one, and that zero is a fold point. The intervals use the exact binary values of the listed angles, and the entries of J and of its derivatives come from the adjoint action of the gates as in the proof of Theorem 1. □

**Proof of Theorem 2.** Write F(x0 + y)F(x0)† = e^{−iA(y)/2} with A = Σ_w a_w P_w and a(y) = J(x0)y + ½Q[y, y] + O(|y|³). Here tr(P_w P_{w′})/D = δ_{ww′}, Q_u = u·Q is a symmetric form, and |u| = 1 gives tr(W²)/D = 1. Then L_ε(x0 + y) = 1 − Re tr(e^{iεW/2} e^{−iA(y)/2})/D.

- **Value and gradient at x0.** At y = 0 the loss is 1 − tr cos(εW/2)/D. The derivative of e^{−iA/2} at A = 0 is −(i/2) dA, so the gradient at x0 is −½ J(x0)^T s(ε), where s_w(ε) = tr(P_w sin(εW/2))/D. Since s(ε) = (ε/2)u + O(ε³) and J(x0)^T u = 0, the gradient is O(ε³). It is also orthogonal to v, since v^T J(x0)^T = 0.
- **Second derivatives.** To second order in y, the loss is L_ε(x0) + (linear term) + |a(y)|²/8 − ε u·a(y)/4 + O(ε²|y|² + |y|³). The term of order ε y² from W A² drops out, since W and A² are self-adjoint and it carries a factor i. Since u ⊥ range J(x0), u·a(y) = ½Q_u[y, y] + O(|y|³). So
  H(ε) = (J(x0)^T J(x0) − εQ_u)/4 + O(ε²).
- **The kernel direction.** The derivative of the exponential map contributes only commutators of A(tv) = O(t) with ∂A = J(x0)v + O(t). These vanish to first order, so Q_u[v, v] = d/dt (u^T J(x0 + tv) v) at t = 0, which is κ.
- **The local minimum.** In the splitting along v and v^⊥, H(ε) has the entry −εκ/4 + O(ε²) on v, a block at least σ_{d−1}²/4 − O(ε) on v^⊥, and off-diagonal part O(ε). For εκ < 0 and small |ε| this gives H(ε) ≥ |εκ|/8. Third derivatives of L_ε are bounded, so this bound, with 1/16 in place of 1/8, holds on a ball of radius c|ε| around x0, where L_ε is strictly convex. The second-order step from x0 is H(ε)^{−1} g with g = O(ε³) in v^⊥. The off-diagonal part couples v^⊥ to v with weight O(ε)/|εκ| = O(1), so the step is O(ε³), and the critical point lies within O(|ε|³) of x0. Its value differs from L_ε(x0) by ½ g^T H^{−1} g + O(|ε|⁹) = O(ε⁶). Expanding tr cos(εW/2)/D gives the stated value.
- **The other side.** For εκ > 0, v^T H(ε) v = −εκ/4 + O(ε²) < 0. In the normal form of a fold [4], the target moved by ε to the covered side has two preimages at distance of order |ε|^{1/2}.
- **Spuriousness.** If x1 is a regular preimage of F(x0), then by the inverse function theorem every U near F(x0) has a preimage near x1, where L = 0. □

## Remarks

1. **Scope.**
   - F(x0) has a regular preimage, so it is an interior point of the image F(T^15). The fold does not bound the image there, and the surjectivity of this circuit is not treated.
   - The same holds for the fold of the SU(8) brick wall in Theorem 3, whose value has a regular preimage in floating point, so it is an interior point of the image up to that precision; and the universality of that circuit is not treated here. For the SO(8) brick wall of [1], see [10].
   - Theorem 2 needs d = dim G, so that F is locally a map between spaces of equal dimension. Circuits with more parameters than dim G are not treated.
2. **Sign changes of det J.** For d = dim SU(D), the degree of F is 0: F is the product of d maps of circles into SU(D), and the primitive generators of the cohomology of SU(D) have degree at least 3, so they pull back to 0 on T^d. If J has full rank somewhere, a regular value in the open image has a preimage, and degree 0 forces preimages of both orientations. So det J takes both signs and C is never empty. A sign change alone does not make a fold, which is why Theorem 1 checks κ.
3. **Overparametrization.** The rank of J saturates almost everywhere at d = dim SU(4). Theorem 2 shows that this saturation alone does not exclude spurious local minima for compilation targets near F(C).
4. **Quantum control.** Whether controls where the end-point map has deficient rank can be traps has been discussed for quantum control landscapes [6, 7], and [8] shows that traps are absent for almost all systems. [9] gives sufficient conditions for convergence of the variational quantum eigensolver in the language of control landscapes. Theorem 2 is a finite-dimensional instance: a fold of the end-point map of a PQC with d = dim G produces strict local minima next to it.

## Check

`sim/fold_check.py` runs in about 2 minutes with numpy, scipy, sympy and mpmath. `sim/brickwall_check.py` runs in about 1 minute with numpy, scipy and mpmath.

- **Theorem 1.** It computes J(x0) and ∂_j J(x0) exactly over ℚ(√2) from the adjoint action, compares J(x0) with the floating point derivative matrix, and asserts rank 14 and κ ≠ 0.
- **Regular preimage.** It compiles F(x0) from random starts by least squares, to residual 5 · 10⁻¹⁶ at a point where the smallest singular value of J is 0.245.
- **Theorem 2.** For ε = ±10⁻², ±10⁻³ and ±10⁻⁴, it computes the second-derivative matrix of L_ε at x0 at 40 digits. It is positive definite exactly on the trap side, and indefinite otherwise. On the trap side it finds the critical point near x0 by least squares and second-order steps at 40 digits, and asserts the following:
  - the gradient is below λ_min²/30, which with third derivatives bounded by (√15/2)³ < 7.3 gives a strict local minimum;
  - the value is ε²/8 to within 1%;
  - another parameter, found from random starts, has loss below 10⁻⁶ times the minimum, evaluated at 40 digits.

```
exact over Q(sqrt 2): rank J(x0) = 14, kappa = u^T (d_v J) v = -sqrt(6)/21 = -0.116642 != 0 (unit null vectors); sigma_14 = 0.5412: a fold point
F(x0) has the regular preimage x1 (residual 5.1e-16, sigma_min = 0.245), so targets near F(x0) have loss-zero parameters near x1
eps = +1e-02 (outside the local image): smallest second-derivative eigenvalue of the loss at x0 +2.794e-04; -eps kappa/4 = +2.916e-04
eps = -1e-02 (inside the local image): smallest second-derivative eigenvalue of the loss at x0 -3.038e-04; -eps kappa/4 = -2.916e-04
  local minimum at distance 1.7e-08 from x0: loss 1.249995e-05 = 0.999996 eps^2/8, gradient 4.0e-29, smallest second-derivative eigenvalue 2.794e-04; another parameter has loss 1.1e-16, so the minimum is spurious
eps = +1e-03 (outside the local image): smallest second-derivative eigenvalue of the loss at x0 +2.904e-05; -eps kappa/4 = +2.916e-05
eps = -1e-03 (inside the local image): smallest second-derivative eigenvalue of the loss at x0 -2.928e-05; -eps kappa/4 = -2.916e-05
  local minimum at distance 1.7e-11 from x0: loss 1.250000e-07 = 1.000000 eps^2/8, gradient 3.6e-29, smallest second-derivative eigenvalue 2.904e-05; another parameter has loss 1.5e-16, so the minimum is spurious
eps = +1e-04 (outside the local image): smallest second-derivative eigenvalue of the loss at x0 +2.915e-06; -eps kappa/4 = +2.916e-06
eps = -1e-04 (inside the local image): smallest second-derivative eigenvalue of the loss at x0 -2.917e-06; -eps kappa/4 = -2.916e-06
  local minimum at distance 1.7e-14 from x0: loss 1.250000e-09 = 1.000000 eps^2/8, gradient 2.1e-29, smallest second-derivative eigenvalue 2.915e-06; another parameter has loss 2.7e-16, so the minimum is spurious
fold and trap checks pass
```

`sim/brickwall_check.py` compares the derivative matrices of the interval code with floating point and finite differences, certifies Theorem 3, and checks the instance for the brick wall:

```
SU(8) brick wall of [1], all angles fixed but x_36: det J changes sign on (a, b) with a = 5.023018236365428430626359, b - a = 1.37e-43, and |h| >= 2.144e-33 > (b - a) * 125 d^3 there, in interval arithmetic at 160 digits: a fold point
  at x_36 = t0 (floating point): sigma_62 = 0.0205, sigma_63 = 8.5e-16, kappa = -0.0232 for unit null vectors
F(x0) has a regular preimage x1: max |F(x1) - F(x0)| = 7.2e-15, sigma_min(J(x1)) = 0.021
eps = +1e-03 (trap side): critical point at distance 3.0e-10 from x0, loss 1.250000e-07 = 1.00000 eps^2/8, smallest second-derivative eigenvalue 5.74e-06 (|eps kappa|/4 = 5.79e-06); from x1 the loss reaches 2.4e-15, so the minimum is spurious
eps = +1e-04 (trap side): critical point at distance 1.6e-11 from x0, loss 1.250000e-09 = 1.00000 eps^2/8, smallest second-derivative eigenvalue 5.79e-07 (|eps kappa|/4 = 5.79e-07); from x1 the loss reaches 2.0e-15, so the minimum is spurious
brick wall checks pass
```

The distances scale as ε³ and the value at ε = 10⁻² is 1 − ε² tr(W⁴)/(48 D) = 0.999996 times ε²/8, with tr(W⁴)/D = 17/9, as in Theorem 2.

## References

1. D. Wierichs, K. Kottmann, N. Killoran. Unitary synthesis with optimal brick wall circuits. arXiv:2511.16736 (2025).
2. M. Larocca, N. Ju, D. García-Martín, P. J. Coles, M. Cerezo. Theory of overparametrization in quantum neural networks. Nature Computational Science 3, 542 (2023), arXiv:2109.11676.
3. E. R. Anschuetz, B. T. Kiani. Quantum variational algorithms are swamped with traps. Nature Communications 13, 7760 (2022), arXiv:2205.05786.
4. H. Whitney. On singularities of mappings of Euclidean spaces. I. Mappings of the plane into the plane. Annals of Mathematics 62, 374 (1955).
5. The Omega Institute. trureturing, issue #15435 and pull request #15606, github.com/the-omega-institute/trureturing (11 Oct 2026).
6. A. N. Pechen, D. J. Tannor. Are there traps in quantum control landscapes? Physical Review Letters 106, 120402 (2011), arXiv:1508.05434.
7. H. Rabitz, T.-S. Ho, R. Long, R. Wu, C. Brif. Comment on "Are there traps in quantum control landscapes?". Physical Review Letters 108, 198901 (2012), arXiv:1105.2367.
8. B. Russell, H. Rabitz, R. Wu. Quantum control landscapes are almost always trap free. arXiv:1608.06198 (2016).
9. M. Wiedmann, D. Burgarth, G. Dirr, T. Schulte-Herbrüggen, E. Malvetti, C. Arenz. On the convergence of the variational quantum eigensolver and quantum optimal control. arXiv:2509.05295 (2025).
10. A universal SO(8) circuit with the optimal number of CZ gates, through triality. This repository, folder so8-universal-circuit (2026).
