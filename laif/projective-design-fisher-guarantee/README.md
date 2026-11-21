# Fisher guarantees of projective designs at even orders

2026-11-21

## Problem

A finite weighted ensemble E = {(π_i, |φ_i⟩)} of pure states in ℂ^d is a projective t-design if Σ_i π_i (|φ_i⟩⟨φ_i|)^{⊗t} equals the Haar average. It defines the rank-one POVM M_E = {d π_i |φ_i⟩⟨φ_i|}. At a pure state |ψ⟩ and a unit tangent vector |ν⟩ ⊥ |ψ⟩, the normalized Fisher form ⟨ν, G_{ψ,M} ν⟩ is a quarter of the classical Fisher information of M along the direction |ν⟩⟨ψ| + |ψ⟩⟨ν|, with outcomes of probability 0 omitted. It equals 1 for the quantum Fisher information and 1/2 for the continuous Haar measurement. The Fisher floor η(M) is the least eigenvalue of G_{ψ,M}, minimized over all pure states, and the design Fisher guarantee is

η_des(d, t) = inf over t-designs E of η(M_E)

[1, Equations (8), (9) and (16)]. In [1, Theorem 1], η_des(d, t) is determined for t = 2 and every odd t ≥ 3. For even t = 2k ≥ 4, [1] proves c_{d,2k} ≤ η_des(d, 2k) ≤ (1/2)(1 − d/((k + 1)(d + k − 1))), with c_{d,2k} = (1/2)(1 − d/(k(d + k)) + (d + 1)/(8k²(d + k)²)), and the optimal even-order guarantees are stated as undetermined [1, Sections III and VI].

Previous best bounds for qubits [1, Equations (22) and (24)]:

| t | lower | upper |
|---|---|---|
| 4 | 387/1024 = 0.3779296875 | 7/18 = 0.3888… |
| 6 | 521/1200 = 0.4341666… | 7/16 = 0.4375 |
| 8 | 1409/3072 = 0.4586588… | 23/50 = 0.46 |

and for t = 4 in higher dimensions [1, Equations (22) and (24)]:

| d | lower | upper |
|---|---|---|
| 3 | 141/400 = 0.3525 | 3/8 = 0.375 |
| 4 | 773/2304 = 0.3355034… | 11/30 = 0.3666… |
| 5 | 507/1568 = 0.3233418… | 13/36 = 0.3611… |

## Results

**Theorem 1.** For qubit projective designs,

| t | lower bound | upper bound |
|---|---|---|
| 4 | 0.3825684005 | 0.3825684109 |
| 6 | 0.4359033629 | 0.4359033733 |
| 8 | 0.4594193577 | 0.4594193687 |

that is, η_des(2, t) lies between the two values. Each bound is an explicit certificate in exact rational arithmetic: the lower bound is E_Haar[q] for a rational polynomial q, and the upper bound is the Fisher ratio of an explicit finite weighted t-design. Numerically, the optimality systems below give η_des(2, 4) = 0.38256841056650…, η_des(2, 6) = 0.43590337295590… and η_des(2, 8) = 0.45941936777292….

**Theorem 2.** For projective 4-designs in dimensions 3, 4 and 5,

| d | lower bound | upper bound |
|---|---|---|
| 3 | 0.3594473 | 0.3594530 |
| 4 | 0.3440453 | 0.3440659 |
| 5 | 0.3330398 | 0.3330513 |

The lower bounds are again E_Haar[q] for explicit rational polynomials q. The upper bounds are the values of explicit rational measures with 22 support points in the reduced variables below; each gives a finite weighted 4-design with that Fisher ratio.

## Proof

*Reduction.* For a qubit, write the Bloch vector of φ as n = (x, y, z). At |ψ⟩ = |0⟩ (north pole) and |ν⟩ = |1⟩, the normalized Fisher form of M_E is

⟨ν, G ν⟩ = Σ_i π_i f(n_i),  f(n) = x²/(1 + z),

with f = 0 at the south pole, where the outcome has probability 0 and is omitted. This is 1/2 for the uniform measure. A projective t-design of a qubit is a spherical t-design of its Bloch vectors, and rotations of a t-design are t-designs. The tangent space at |ψ⟩ is the real plane of the vectors e^{iα}|1⟩, so η_des(2, t) = inf_E Σ_i π_i f(n_i) over t-designs E.

*Lower bound.* Let q(z, u) = Σ q_{ac} u^a z^c, with u = x² and 2a + c ≤ t, be a polynomial of degree at most t on the sphere. If f ≥ q on S², then every t-design gives Σ π_i f(n_i) ≥ Σ π_i q(n_i) = E_Haar[q]. Writing u = s(1 − z²) with s ∈ [0, 1], the condition f ≥ q is h(z, s) = s(1 − z) − q(z, s(1 − z²)) ≥ 0 on [−1, 1] × [0, 1]. This includes the south pole, where it reads q(−1, 0) ≤ 0. The rational coefficients of q are in `sim/cert_t{4,6,8}.json`. Nonnegativity of h is certified in exact arithmetic by subdividing the square into boxes on which all Bernstein coefficients of h are nonnegative: 313, 865 and 1761 boxes for t = 4, 6, 8. The Haar moments are E[x^{2a} z^c] = (2a − 1)!! (c − 1)!!/(2a + c + 1)!! for even c, and E_Haar[q] is the stated lower bound.

*Upper bound.* A probability measure on the region {(z, u) : −1 ≤ z ≤ 1, 0 ≤ u ≤ 1 − z²} lifts to a measure on S² by placing equal weights on (±√u, ±√(1 − z² − u), z). The lifted measure is invariant under x → −x and y → −y, so its odd moments vanish. Its remaining moments of degree at most t are those of u^a z^c with 2a + c ≤ t, after y² = 1 − z² − u is eliminated. The certificates use 9, 16 and 25 rational points (z_j, u_j) with rational weights w_j ≥ 0 (`sim/cert_t{4,6,8}.json`) that satisfy these moment equations exactly. Each lifted measure is a finite weighted t-design. Its Fisher ratio at the frame above is Σ w_j u_j/(1 + z_j), the stated upper bound, and η(M_E) is at most this value.

*Higher dimensions.* For d ≥ 3, take |ψ⟩ = e_1 and |ν⟩ = e_2; every pure state with a unit tangent vector is of this form after a unitary change of basis, which maps designs to designs. For |φ⟩ = (φ_1, …, φ_d) write a = |φ_1|², b = |φ_2|² and c = cos² of the phase of φ̄_1 φ_2. The normalized Fisher form is ⟨ν, G ν⟩ = Σ_i π_i f(φ_i) with f = d b c for a > 0 and f = 0 for a = 0 [1, Equation (10)]; its Haar average is 1/2. Let H be the group generated by the unitaries on e_3, …, e_d, the joint phase on e_1 and e_2, the sign change of e_2, and complex conjugation. Its invariant polynomials of degree at most (t, t) on the unit sphere are spanned by a^i b^j (abc)^l with i + j + 2l ≤ t, since φ_1 φ̄_2 has modulus √(ab) and Re((φ_1 φ̄_2)^{2k}) is a polynomial in ab and ab·c.

Lower bound: if q is in this span and f ≥ q, every t-design gives Σ π_i f(φ_i) ≥ E_Haar[q]. With b = s(1 − a), the condition is h(a, s, c) = d s (1 − a) c − q(a, s(1 − a), c) ≥ 0 on [0, 1]³, together with q(0, b, c) ≤ 0 for b ∈ [0, 1] on the face a = 0, where q does not depend on c. Both are certified by Bernstein subdivision in exact arithmetic (3441, 2633 and 3603 boxes for d = 3, 4, 5). The Haar moments are E[a^p b^r] = (d − 1)! p! r!/(d − 1 + p + r)!, with (a, b) distributed as Dirichlet(1, 1, d − 2), and E[c^l] = C(2l, l)/4^l, with the phase uniform and independent.

Upper bound: a probability measure μ on the points (a, b, c) whose moments a^i b^j (abc)^l agree with the Haar moments for i + j + 2l ≤ 4 lifts to an H-invariant measure on the sphere, by averaging the state (√a, √b e^{iθ}, √(1 − a − b), 0, …, 0) with cos²θ = c over H. Its moments of degree (4, 4) are those of its H-average, so it is a 4-design, and its Fisher ratio at the frame is E_μ[f]. A finite measure with the same moments of degree (4, 4) and the same value of E[f] exists by the theorem on finitely supported measures with prescribed integrals of finitely many functions [2], so η_des(d, 4) ≤ E_μ[f]. The rational measures are in `sim/cert_d{3,4,5}_t4.json` and match the moment equations exactly.

*Structure of the optimum (numerical).* The linear program over t-designs was solved numerically, and its optimum is supported on few orbits: 4 for t = 4, at (z, u) ≈ (−0.8591, 0), (−0.2490, 0.6760), (0.3610, 0) and (0.8031, 1 − z²), and 8 and 11 for t = 6 and 8. At these orbits the dual polynomial touches f. The two certificates are rational perturbations of this pair.

## Check

`sim/lp_qubit.py` solves the linear program over measures on 6002 points of the sphere. It reproduces the exact values of [1] at t = 2, 3 and 5 (1/(3 + √3), 1/3 and 5/12). `sim/exact4.py` (t = 4) and `sim/exact_t.py` (any t) solve the optimality system, made of the touching conditions of the dual polynomial and the moment equations, in high precision; primal and dual values agree to at least 30 digits. `sim/run_cert4.py` and `sim/run_cert_t.py`, with `sim/cert4.py`, build and check the rational certificates and write `sim/cert_t{4,6,8}.json`. Output in `sim/out.txt` and `sim/out_t68.txt`. For d ≥ 3, `sim/lp_qudit.py` solves the linear program in (a, b, c) on a grid and reproduces the exact values of [1] at t = 2, 3 and 5 for d = 3 (1/6, 5/16 and 2/5, up to grid error). `sim/exchange_qudit.py` refines the dual by cutting planes, and `sim/run_cert_qudit2.py`, with `sim/cert_qudit.py`, builds and checks the rational certificates. Output in `sim/out_qudit.txt`.

## Scope

- Qubits with t = 4, 6, 8, and dimensions 3, 4, 5 with t = 4.
- For d ≥ 3 the upper bound is the value of an explicit H-invariant 4-design; the finite design with the same value is given by an existence theorem, not explicitly.
- The bounds are computer-checked certificates in exact rational arithmetic; they are not formalized in Lean.
- Closed forms of η_des(2, t) are not stated here; the values with many digits are numerical.

## References

[1] Z. Yang, B. Xiao, H. Zhu. Sharp uniform Fisher information bounds from projective designs. arXiv:2611.17288.

[2] H. Richter. Parameterfreie Abschätzung und Realisierung von Erwartungswerten. Blätter der DGVFM 3 (1957).

## Use of AI

The results, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
