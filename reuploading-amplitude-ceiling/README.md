# Amplitude ceilings for re-uploading: exact values, the same for every depth

Written 7 Nov 2026.

## Problem

[1] considers m qubits, each encoded by RY(x) = e^{−ixY/2} on |0⟩, then re-encoded L times in total, with arbitrary channels (ancillas, noise, outcome-averaged measurements) between and after the uploads and a readout O with ‖O‖ ≤ 1. The output f(x) = Σ_k c_k e^{ikx} has frequencies |k| ≤ mL. [1] shows

|c_{mL−d}| ≤ T(m, d) = Pr[Bin(m, 1/2) ≤ d] = 2^{−m} Σ_{i≤d} C(m, i),

independent of L. It is tight at d = 0 and loose below the top. For L = 1 it computes the exact ceiling c*(m, k), the largest |c_k| over all channels and readouts, as a small eigenvalue problem [1, Theorem 2]. The exact ceiling for L ≥ 2 and its dependence on L are left open.

## Result

Write B(c) = C(m, c)/2^m and K = mL − d. Let Γ(m, d) be the largest value of Σ_{t=0}^{d} √(a_t b_t) over all ways to split each mass B(c), c = 0, …, m, into parts a(c, t) placed at t ≥ c and parts b(c, t) placed at t ≤ c − (m − d), with a_t = Σ_c a(c, t) and b_t = Σ_c b(c, t) (t = 0, …, d; the rest of the mass is unused).

**Theorem 1 (exact ceiling).** Let L ≥ 2 and 0 ≤ d < m. Then the largest |c_{mL−d}| over all channels and all readouts with ‖O‖ ≤ 1 equals Γ(m, d). In particular it does not depend on L ≥ 2.

**Theorem 2 (the top half).** If 2d < m, then

Γ(m, d) = 2^{−m} Σ_{t=0}^{d} √(C(m, t) C(m, d − t)) = c*(m, m − d),

with C(m, t) the binomial coefficient.

So for the frequencies within m/2 of the top, re-uploading any number of times, with any channels in between, reaches exactly the single-upload ceiling and no more. For d = 1 the ceiling is 2√m/2^m (m ≥ 3), against T(m, 1) = (m + 1)/2^m.

**Corollary 3.** For L ≥ 2 and 1 ≤ d < m:
- Γ(m, d) < T(m, d);
- Γ(m, d) ≤ 1/2;
- for fixed d, Γ(m, d)/T(m, d) = Θ(m^{−d/2}).

So T(m, d) is not reached at any depth, and for fixed d it is too large by a factor of order m^{d/2}. The ceiling also stays at most 1/2. At the same distance d = m − 1 from the top, a single upload reaches about 0.57 to 0.62 for 3 ≤ m ≤ 12 (Table 1 of [1]), while every L ≥ 2 gives 1/2 in the cases computed below.

**Values for 2d ≥ m** (program solved numerically, script output):

| m | d | Γ(m, d), any L ≥ 2 | c*(m, m − d), L = 1 | T(m, d) |
|---|---|---|---|---|
| 2 | 1 | 0.5 | 0.5 | 0.75 |
| 3 | 2 | 0.5 | 0.5728 | 0.875 |
| 4 | 2 | 0.4665 | 0.4665 | 0.6875 |
| 4 | 3 | 0.5 | 0.5757 | 0.9375 |
| 6 | 4 | 0.4958 | 0.5058 | 0.8906 |
| 8 | 5 | 0.4480 | 0.4456 | 0.8555 |

The two ceilings agree in every computed case with 2d = m and also at (m, d) = (5, 3) and (7, 4), but not at (3, 2). Otherwise they differ in both directions: mostly the single upload is higher (heuristically, because for L = 1 the pairs of counts at distance m − d overlap and can interfere), while at (8, 5) depth is slightly higher. For the computation, the symmetry c ↦ m − c of the program (which exchanges the low and the high parts) and its concavity give an optimum with b_t = a_{d−t}; `sim/check.py` solves this symmetric form.

## Proofs

**Bookkeeping.** Dilate every channel to an isometry. An encoding is e^{−ix/2}P_+ + e^{ix/2}P_−, with P_± the projectors onto Y = ±1. Add a counter register, incremented on the P_+ branch of every encoding; the evolution stays an isometry. The final state is Σ_j χ_j ⊗ |j⟩ with Σ_j ‖χ_j‖² = 1, where χ_j collects the paths with j plus branches, and the actual output state is ψ(x) = Σ_j e^{−i(2j − mL)x/2} χ_j. Hence c_K = Σ_{t=0}^{d} ⟨χ_t|O|χ_{t+K}⟩ up to conjugation, and

|c_K| ≤ Σ_{t=0}^{d} √(w(t) w(K + t)), w(j) = ‖χ_j‖².   (1)

**Constraints on w.** After the first upload the state is Σ_c α_c ⊗ |c⟩ with orthogonal α_c, ‖α_c‖² = B(c), because |0⟩^{⊗m} splits by the number c of qubits on the P_+ branch. Write Φ_c for the image of α_c ⊗ |c⟩ under the rest of the evolution: the Φ_c are orthogonal, ‖Φ_c‖² = B(c), and Φ_c has counter values in [c, c + m(L − 1)]. Projecting onto counter values ≥ J kills every Φ_c with c < J − m(L − 1), and a projection does not increase norms, so

Σ_{j≥J} w(j) ≤ Σ_{c ≥ J − m(L−1)} B(c), and likewise Σ_{j≤J} w(j) ≤ Σ_{c≤J} B(c).

So w lies between the binomial law and its shift by m(L − 1) in the stochastic order. The coupling that pairs the two laws in rank order then splits each B(c) over j ∈ [c, c + m(L − 1)] with marginal w: the lower tail bound gives j ≥ c and the upper one j ≤ c + m(L − 1). The terms of (1) use j = t ≤ d, which needs c ≤ t (and t ≤ c + m(L − 1) holds since d < m), and j = K + t, which needs c ≥ K + t − m(L − 1) = m − d + t (and K + t ≥ c holds since K ≥ 2m − d > m). This gives |c_K| ≤ Γ(m, d).

**Attainment.** Take an optimal split. After the first upload, an isometry defined on the span of the α_c maps α̂_c = α_c/‖α_c‖ to α̂_c (moved to an ancilla) ⊗ Σ_s √(π(c, c + s)/B(c)) |s⟩ (a flag register). Write s = s_2 + ⋯ + s_L with 0 ≤ s_ℓ ≤ m. Before upload ℓ, the encoded qubits are prepared, conditioned on the flag, in a Y eigenstate with s_ℓ qubits on the plus branch, and after it this eigenstate is mapped back to |0⟩^{⊗m}, again conditioned on the flag. Here π(c, j) is the split, with the unused mass of c placed at some j in (d, K) ∩ [c, c + m(L − 1)]. This set is nonempty: j = max(c, d + 1) satisfies j ≤ c + m(L − 1) because d + 1 ≤ m, and j < K because c ≤ m < K and 2d + 1 < 2m ≤ mL. Then the χ_j are orthogonal with ‖χ_j‖² = w(j), and the counts t ≤ d and K + t ≥ K > d are disjoint. So O = Σ_t (|χ̂_t⟩⟨χ̂_{K+t}| + h.c.), with χ̂ the normalised vectors, is a sum of disjoint 2 × 2 swaps, has norm 1, and gives equality in (1). The program does not involve L, which proves Theorem 1.

**Theorem 2.** For 2d < m the parts a use c ≤ d and the parts b use c ≥ m − d > d, so they do not compete. The constraint on a is Σ_{t≤J} a_t ≤ F(J) = Σ_{c≤J} B(c) for J ≤ d: it is necessary, and it is sufficient because mass at t may come from any c ≤ t, so assigning the a_t in increasing t from the smallest c with mass left always succeeds. Under c ↦ m − c the reversed vector b'_u = b_{d−u} obeys the same constraint, and the objective is Σ_t √(a_t b'_{d−t}). The objective is concave and the problem is symmetric under exchanging a and b', so there is an optimum with b' = a. It remains to maximise g(a) = Σ_t √(a_t a_{d−t}) subject to the prefix constraints. At a* = (B(0), …, B(d)) all constraints are tight and ∂g/∂a_t = r_t = √(B(d − t)/B(t)). The ratio r_{t+1}/r_t = √((d − t)(t + 1)/((m − d + t + 1)(m − t))) is at most 1 because d ≤ m. So ∇g(a*) = Σ_J μ_J ∇(Σ_{t≤J} a_t) with μ_J = r_J − r_{J+1} ≥ 0 (r_{d+1} = 0). By concavity g(a) ≤ g(a*) + ∇g(a*)·(a − a*) ≤ g(a*) for every feasible a. For L = 1 the pairs of counts (t, t + m − d) are disjoint when 2d < m, and the trace-norm formula of [1, Theorem 2] splits into 2 × 2 blocks with the same value.

**Corollary 3.** By the inner-product inequality, Σ_t √(a_t b_t) ≤ √(Σa · Σb). Both Σa and Σb are at most F(d) = T(m, d), and they sum to at most 1 because they are disjoint parts of the total mass 1. This gives Γ ≤ T and Γ ≤ 1/2. For 2d < m the first bound is strict because B(t) is not proportional to B(d − t) when 1 ≤ d < m. For 2d ≥ m we have T(m, d) > 1/2 ≥ Γ. For the rate at fixed d (so 2d < m for large m), C(m, t) C(m, d − t) ≤ m^d/(t!(d − t)!) and T(m, d) ≥ C(m, d)/2^m give Γ/T = O(m^{−d/2}); the term t = 0 gives Γ ≥ √(C(m, d))/2^m, and T(m, d) ≤ (d + 1)C(m, d)/2^m, so Γ/T = Ω(m^{−d/2}).

## Check

`sim/check.py` (about 10 minutes) checks:
- the closed form of Theorem 2 against the single-upload ceiling for m ≤ 12 and against the program for m ≤ 8;
- the table above, together with Γ ≤ 1/2 and Γ ≤ T;
- the formula for d = 1;
- as a sanity check, random circuits (uniform unitaries on the encoded qubits plus one or two ancillas between uploads, optimal readout), which stay below Γ(m, d).

Its output is in `sim/out.txt`. `sim/optimise.py` maximises |c_{mL−d}| locally over such circuits. Its best values, in `sim/optimise_out.txt`, are:
- 0.5000 for (m, L, d) = (2, 2, 1), with one or two ancillas;
- 0.4327 for (3, 2, 1);
- 0.5000 for (3, 2, 2);
- 0.5000 for (2, 3, 1).

The ceilings are 0.5, 0.4330, 0.5 and 0.5, and T(m, d) is 0.75, 0.5, 0.875 and 0.75.

## References

1. P. Sulimov, C. Lehmann. Hidden selection rules and amplitude ceilings in quantum Fourier models. arXiv:2611.01314 (2026).
