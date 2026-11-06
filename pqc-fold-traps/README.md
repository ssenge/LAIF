# Folds in a two-qubit circuit: critical values of codimension one and spurious local minima

Written 6 Nov 2026.

## Problem

A parametrized quantum circuit (PQC) in the sense of [1, Definition 1] consists of Clifford gates and d single-qubit Pauli rotations, one parameter per rotation. It gives a map F: T^d → G into a Lie group of dimension d, such as SU(2^n). Let J(x) be its Jacobian and C = {x : rank J(x) < d} the critical set.

**The conjecture.** [1] proves that if J has full rank at one point, then it has full rank almost everywhere [1, Lemma 2]. For a proof of universality of its brick wall circuits, [1] then needs the following [1, Conjecture 3]:

> The critical values F(C) of a PQC that has full rank almost everywhere in T^d form an at most (d − 2)-dimensional subset of G.

If the conjecture holds, the critical values cannot wall off part of G, and full rank somewhere implies surjectivity.

**Local minima.** For a target U_t, the compilation loss is L(x) = 1 − Re tr(U_t† F(x))/D with D = 2^n. A local minimum with L > 0 is spurious when another parameter reaches L = 0. Spurious minima are known for underparametrized circuits [3]. Overparametrization, the saturation of the rank, is associated with their disappearance [2].

## Result

**The circuit.** On two qubits, let R_P(t) = e^{−itP/2} for a Pauli word P. Take

F(x) = R_{P_15}(x_15) ⋯ R_{P_1}(x_1),  (P_1, …, P_15) = (YX, XY, IX, IY, XX, IZ, YZ, XI, YY, ZX, YI, IY, IX, XX, XZ).

Each R_P is a Clifford conjugate of a single-qubit rotation, so F is a PQC in the sense of [1], with d = 15 = dim SU(4). Write H_k = V_k P_k V_k† with V_k = R_{P_15}(x_15) ⋯ R_{P_{k+1}}(x_{k+1}), so ∂_k F = −(i/2) H_k F. Let J(x) be the 15 × 15 matrix whose k-th column holds the Pauli coefficients tr(P_w H_k)/4 of H_k. Its columns are unit vectors. J has rank 15 at random points, so full rank almost everywhere.

**Theorem 1 (computer-assisted).** There is x0 ∈ T^15 with:

- rank J(x0) = 14, with σ_14(J(x0)) = 0.0795;
- κ = u^T (∂_v J)(x0) v = −0.00293 ≠ 0, where v and u are unit right and left null vectors of J(x0).

So x0 is a fold point. Near x0 the critical set C is a smooth hypersurface, ker J(x0) is transverse to it, and F restricted to C is an immersion at x0. Hence F(C) contains a 14-dimensional embedded submanifold of SU(4) through F(x0). So the statement of [1, Conjecture 3] does not extend to every PQC. The brick wall circuits for which [1] needs it are a different family and are not covered by this example.

**Theorem 2 (spurious minima at fold points).** Let x0 be a fold point of a PQC F: T^d → SU(D) with d = D² − 1, with u, v and κ as above. Let W = Σ_w u_w P_w and U_ε = e^{−iεW/2} F(x0).

- If εκ < 0 and |ε| is small enough, the loss L_ε for the target U_ε has a strict local minimum within O(ε²) of x0. Its value is ε²/8 + O(ε³).
- If εκ > 0 and |ε| is small enough, x0 is near a saddle: the Hessian at x0 has a negative eigenvalue.
- If F(x0) also has a regular preimage x1, then for small |ε| the target U_ε has a preimage near x1. So the local minimum is spurious.

For the circuit above, F(x0) has a regular preimage, with smallest singular value 0.117. So for small ε > 0, the target U_ε has a spurious local minimum at loss ε²/8, at the critical parameter count d = dim SU(4) and with rank saturated almost everywhere. The check verifies this at ε = 10⁻³ and ε = 10⁻⁴.

## Proof

**Fold conditions.** At a point x0 of corank one, adj J(x0) = c v u^T with c = ± σ_1 ⋯ σ_14 ≠ 0. So for every direction w,

∂_w det J(x0) = tr(adj J(x0) ∂_w J(x0)) = c u^T (∂_w J)(x0) v.

- With w = v this gives ∂_v det J(x0) = cκ ≠ 0. So ∇ det J(x0) ≠ 0, and C = {det J = 0} is a smooth hypersurface near x0.
- Its tangent space at x0 is the kernel of ∇ det J(x0), which does not contain v. So ker J(x0) ∩ T_{x0}C = 0, and the differential of F restricted to C is injective at x0.
- An immersion of a 14-dimensional manifold has an embedded 14-dimensional image near each point. These are the conditions of a fold [4].

**The certificate for Theorem 1.** The computation runs at 60 significant digits.

- **A zero of det J.** It locates a point x with |det J(x)| tiny and evaluates det J at x ± δn, where n is the unit gradient direction and δ = 10⁻³⁰. The two values have opposite signs. So by continuity there is x0 with det J(x0) = 0 and |x0 − x| ≤ δ.
- **Derivative bounds.** For |w| = 1, ‖∂_w H_k‖ ≤ Σ_j |w_j| ≤ √15 in the normalized Frobenius norm, since each derivative is a commutator with a conjugated Pauli word over 2. Hence ‖∂_w J‖_F ≤ 15 and ‖∂²_w J‖_F ≤ 60.
- **Transfer from x to x0.**
  - Singular values move by at most 15δ, so σ_14(J(x0)) ≥ 0.0794 − 15δ.
  - The null vectors move by an angle at most 15δ/(σ_14 − 15δ) [5].
  - So κ moves by at most 1.2 · 10⁻²⁶, against |κ| = 2.9 · 10⁻³.
- **Margins.** This is floating point arithmetic, not interval arithmetic. Every inequality used holds with a margin above 10²⁰ times the working precision. □

**Proof of Theorem 2.** Write F(x0 + y)F(x0)† = e^{−iA(y)/2} with A = Σ_w a_w P_w and a(y) = J(x0)y + ½Q[y, y] + O(|y|³). Here tr(P_w P_{w′})/D = δ_{ww′}, and Q_u = u·Q is a symmetric form.

- **Expansion.** Expand tr(e^{iεW/2} e^{−iA/2})/D. The terms of order ε² y and ε y² have imaginary trace, since W² and A, or W and A², are Hermitian. So
  L_ε(x0 + y) = ε²/8 + |a(y)|²/8 − ε u·a(y)/4 + O(|y|³ + ε³|y| + ε²|y|²).
- **Gradient and Hessian.** Since u ⊥ range J(x0), u·a(y) = ½Q_u[y, y] + O(|y|³). So the gradient at x0 is O(ε³), and the Hessian is
  H(ε) = (J(x0)^T J(x0) − εQ_u)/4 + O(ε²).
- **The kernel direction.** The derivative of the exponential map contributes only commutators of A(tv) = O(t) with ∂A = J(x0)v + O(t). These vanish to first order, so Q_u[v, v] = d/dt (u^T J(x0 + tv) v) at t = 0 = κ.
- **The local minimum.** J^T J ≥ σ_14² on v^⊥, and v^T H(ε) v = −εκ/4 + O(ε²). By the block decomposition along v and v^⊥, H(ε) ≥ |εκ|/8 for εκ < 0 and small |ε|. Third derivatives of L_ε are bounded, so H stays positive on a ball of radius of order |ε| around x0. The gradient is O(ε³), so a unique critical point lies within O(ε²) of x0, and it is a strict local minimum with value ε²/8 + O(ε³). For εκ > 0, v^T H(ε) v < 0.
- **Spuriousness.** If x1 is a regular preimage of F(x0), then by the inverse function theorem every U near F(x0) has a preimage near x1, where L = 0. □

## Remarks

1. **Geometry.** The image of a neighbourhood of x0 lies, to second order along v, on the side sign(κ)·W of F(C). The traps sit exactly on the other side, at targets the nearby parameters cannot reach. The basin of each trap has size of order |ε|. For the circuit above, the Hessian at x0 is already indefinite at ε = 10⁻².
2. **Scope.**
   - The example is one circuit with d = dim G. The brick wall circuits of [1], and whether Conjecture 3 holds for them, are not treated here. Neither is the surjectivity of the circuit above.
   - Theorem 2 needs d = dim G, so that F is locally a map between spaces of equal dimension. Circuits with more parameters than dim G are not treated.
3. **Overparametrization.** The rank of J saturates almost everywhere at d = dim SU(4). Theorem 2 shows that this saturation alone does not exclude spurious local minima for compilation targets near F(C).

## Check

`sim/fold_check.py` runs in about 75 s with numpy, scipy and mpmath.

- **Theorem 1.** It scans random lines for a sign change of det J and refines the zero at 60 digits. It then certifies the sign change at distance 10⁻³⁰, σ_14 and κ, and evaluates the perturbation bound.
- **Regular preimage.** It compiles F(x0) from random starts by least squares, to residual 5 · 10⁻¹⁶ at a point where the smallest singular value of J is 0.117.
- **Theorem 2.** For ε = ±10⁻³ and ±10⁻⁴, it computes the Hessian of L_ε at x0 at 40 digits. It is positive definite exactly for εκ < 0, and indefinite otherwise. For εκ < 0 it finds the critical point near x0 by least squares and second-order steps at 40 digits, and asserts the following:
  - the gradient is below λ_min²/30, which with third derivatives bounded by (√15/2)³ < 7.3 gives a strict local minimum;
  - the value is ε²/8 to six digits;
  - other parameters, found from random starts, reach residual 6 · 10⁻¹⁶ at regular points.

```
fold point x0 within 1.0e-30 of x: det J changes sign (-5.19e-33, 5.19e-33)
sigma_14 = 0.0794837, sigma_15 = 4.17e-63 at x; |grad det J| = 0.005189
kappa = u^T (d_v J) v = -0.00292765, perturbation bound 1.18e-26: rank 14 and kernel transverse at x0, a fold
F(x0) has the regular preimage x1 (residual 4.8e-16, sigma_min = 0.117), so targets near F(x0) have loss-zero parameters near x1
eps = +1e-03 (outside the local image): smallest Hessian eigenvalue of the loss at x0 +6.449e-07; eps v^T H1 v = +7.319e-07
eps = -1e-03 (inside the local image): smallest Hessian eigenvalue of the loss at x0 -8.177e-07; eps v^T H1 v = -7.319e-07
  local minimum at distance 7.9e-10 from x0: loss 1.250000e-07 = 1.000000 eps^2/8, gradient 3.2e-29, smallest Hessian eigenvalue 6.449e-07; other parameters reach residual 5.6e-16 at a regular point (sigma_min = 0.010), so the minimum is spurious
eps = +1e-04 (outside the local image): smallest Hessian eigenvalue of the loss at x0 +7.233e-08; eps v^T H1 v = +7.319e-08
eps = -1e-04 (inside the local image): smallest Hessian eigenvalue of the loss at x0 -7.405e-08; eps v^T H1 v = -7.319e-08
  local minimum at distance 7.3e-13 from x0: loss 1.250000e-09 = 1.000000 eps^2/8, gradient 4.3e-29, smallest Hessian eigenvalue 7.233e-08; other parameters reach residual 5.1e-16 at a regular point (sigma_min = 0.117), so the minimum is spurious
fold and trap checks pass
```

## References

1. D. Wierichs, K. Kottmann, N. Killoran. Unitary synthesis with optimal brick wall circuits. arXiv:2511.16736 (2025).
2. M. Larocca, N. Ju, D. García-Martín, P. J. Coles, M. Cerezo. Theory of overparametrization in quantum neural networks. Nature Computational Science 3, 542 (2023), arXiv:2109.11676.
3. E. R. Anschuetz, B. T. Kiani. Quantum variational algorithms are swamped with traps. Nature Communications 13, 7760 (2022), arXiv:2205.05786.
4. H. Whitney. On singularities of mappings of Euclidean spaces. I. Mappings of the plane into the plane. Annals of Mathematics 62, 374 (1955).
5. P.-Å. Wedin. Perturbation bounds in connection with singular value decomposition. BIT 12, 99 (1972).
