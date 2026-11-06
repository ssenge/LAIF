# Hardness of small-angle patches in a hardware-efficient ansatz

Written 6 Nov 2026.

## Setting

**Ansatz.** N qubits on a ring, sites 0, …, N − 1, and an even number L of layers. The cost is

U(θ) = E R_L ⋯ E R_1,  R_ℓ = ⊗_q e^{−iθ_{ℓ,q,y} Y_q} e^{−iθ_{ℓ,q,z} Z_q},  E = ∏_q CZ_{q,q+1},  C(θ) = ⟨0^N| U(θ)† Z_0 U(θ) |0^N⟩.

This is the hardware-efficient ansatz with Y and Z rotation layers and a ring of CZ gates. It has D = 2NL parameters. At θ = 0 the circuit is the Clifford E^L = I. Rotations are written e^{−iθP}; [1] and [2] write e^{−iθP/2}, which changes patch widths by a factor 2 and no exponent below.

**Patches.** Write B_r = [−D^{−r}, D^{−r}]^D for the patch of width D^{−r} around θ = 0. Known results on B_r:

| Patch | Status |
|---|---|
| r ≥ 1 | the cost is computed classically to precision ε at every point, in time D^{O(log(1/ε))}, so polynomial for constant ε: Pauli path or power series surrogates around the Clifford point [2, Theorem 2 and Supplemental Theorem 7], [1, Theorem 3] |
| r > 1/2 | random points are classically simulable with high probability [2, Theorem 2], [1, Theorem 4] |
| r < 1 | the power series surrogate of [1] needs super-polynomial time at typical points [1, Theorem 3]; for costs modified by its Linear Clifford Encoder, [1] gives numerical evidence of a transition patch of width D^{−(1−δ)} with polynomially decaying gradients, and asks for formal proofs |

The question behind this, raised in [3] and [4], is whether polynomially large gradients and classical hardness can occur together in natural models.

## Results

**Theorem 1 (worst case).** Fix a rational r ∈ [0, 1).
- Let V be a circuit of s gates on a ring of n ≥ 2 qubits, drawn from H, T and CZ between ring neighbours.
- Take N = 2n, and let L be the least even integer at least (72πs)^{1/(1−r)}(4n)^{r/(1−r)}.

A classical algorithm computes, in time poly(s, n), a point θ ∈ B_r, with entries rational multiples of π, such that

C(θ) = ⟨0^n| V† Z_0 V |0^n⟩.

So evaluating C on B_r to within any error below 1/3 is PromiseBQP-hard. Unless PromiseBQP ⊆ PromiseBPP, no classical polynomial-time algorithm does this at every point of B_r.

Together with the case r ≥ 1 in the table, r = 1 is a sharp transition in worst-case complexity. In the worst case over B_r with r < 1, super-polynomial classical cost is unavoidable unless PromiseBQP ⊆ PromiseBPP. At typical points with r > 1/2 it is not.

**Theorem 2 (regions with large gradients).** Fix a rational r ∈ [0, 1), and let V be as above with output error at most 0.01: ⟨Z_0⟩ ≤ −0.98 on yes instances and ≥ 0.98 on no instances. With N = 2n and L as in the proof below, a classical algorithm computes, in time poly(s, n), a point θ* with ‖θ*‖_∞ ≤ D^{−r}/2 such that every point θ of the box

Q = θ* + [−0.01/D, 0.01/D]^D ⊆ B_r

satisfies:

1. |C(θ)| ≥ 0.53, and C(θ) has the sign of ⟨Z_0⟩ after V;
2. at least K ≥ (π/4)D^r coordinates k have |∂_k C(θ)| ≥ 1, so ‖∇C(θ)‖ ≥ √K.

Hence, for every instance and every θ ∈ Q, an estimate of C(θ) to ±1/2 decides the instance. Unless PromiseBQP ⊆ PromiseBPP, no classical polynomial-time algorithm returns such an estimate at a point of Q, whichever point it is given. This hardness part already follows from Theorem 1 at θ*. The new content is part 2: gradients of order one at every point of a box on which the cost is hard.

The boxes of [2, Theorem 2] around Clifford points have the same width O(1/D) and are classically easy. Theorem 2 shows that boxes of that width centred at other points of B_r can carry gradients of order one together with BQP-hardness. It does not settle the question of [1], which concerns random initialization around the Clifford point. Since C varies by at most 0.02 over Q, part 2 is a pointwise statement and leaves little room to train inside Q.

## Proof

**Heisenberg form.** E is a product of commuting CZ gates, so E² = I. With L even,

U(θ) = R̃_L ⋯ R̃_1,  R̃_ℓ = R_ℓ for odd ℓ,  R̃_ℓ = E R_ℓ E for even ℓ,

where E Z_q E = Z_q and E Y_q E = Z_{q−1} Y_q Z_{q+1}. So odd layers offer the rotations e^{−iαZ_q} and e^{−iαY_q}, and even layers offer e^{−iαZ_q} and e^{−iα Z_{q−1}Y_qZ_{q+1}}.

**Lemma 1 (accumulation).** Suppose each layer has at most one nonzero slot, and the K slots of one rotation e^{−iφP} are consecutive among the nonzero layers. Then they compose to e^{−iφP}. So a rotation with |φ| ≤ π/2 and P one of the four types above takes K = ⌈|φ|/σ⌉ layers of the right parity, each with angle φ/K, where |φ/K| ≤ σ. Including skipped layers of the other parity, it uses at most 2K layers.

*Proof.* In the Heisenberg form, a zero layer has R̃_ℓ = I, and a layer with one nonzero slot is a single rotation of the stated type. The K slots of one rotation are separated only by identities, so they compose, and rotations with the same generator add. □

**Compilation.** Logical qubit j sits at site 2j, and the ancilla at site 2j + 1 stays in |0⟩.

- **One-qubit gate on logical j.** It has a ZYZ form e^{−iaZ}e^{−ibY}e^{−icZ}. Each angle can be reduced modulo π to |angle| ≤ π/2, at the cost of a global sign, so the gate takes 3 rotations on site 2j. For H, T and the Clifford G below, all ZYZ angles are rational multiples of π.
- **CZ between logical j and j + 1.** Write m = 2j + 1, and let G be a one-qubit Clifford with G Y G† = ±Z, for example e^{−iπX/4}. Then

  G_m e^{−iα Z_{m−1} Y_m Z_{m+1}} G_m† = e^{∓iα Z_{m−1} Z_m Z_{m+1}},

  which acts as e^{∓iα Z_{m−1} Z_{m+1}} while the ancilla is in |0⟩. With α = ∓π/4 this is e^{iπZ_aZ_b/4}. Then

  CZ_{ab} = e^{iπ/4} e^{−iπZ_a/4} e^{−iπZ_b/4} e^{iπZ_aZ_b/4}.

  G and G† cost 3 rotations each by their ZYZ forms, so the CZ costs 3 + 1 + 3 + 2 = 9 rotations. The ancilla returns to |0⟩.

So V becomes P ≤ 9s rotations, each with |angle| ≤ π/2 ≤ π, and every angle is a rational multiple of π.

*Proof of Theorem 1.* Take σ = D^{−r} with D = 4nL. Since r is rational, an integer K with |φ|/σ ≤ K ≤ |φ|/σ + 2 is found from a rational approximation of D^r, and any such K keeps |φ/K| ≤ σ. So the compiled circuit fits into at most 2P(πD^r + 2) layers. The choice of L gives L^{1−r} ≥ 8πP(4n)^r and L ≥ 8πP, hence 2PπD^r ≤ L/4 and 4P ≤ L/2. So the circuit fits into L layers with all angles at most D^{−r}.

Then U(θ)|0^N⟩ is V|0^n⟩ on the even sites with the ancillas in |0⟩, up to a global phase, so C(θ) = ⟨Z_0⟩ = 1 − 2 Pr[V outputs 1]. A promise problem in BQP has a uniform family of such circuits, with ⟨Z_0⟩ ≤ −1/3 on yes instances and ≥ 1/3 on no instances. An estimate of C(θ) to within less than 1/3 decides it. □

*Proof of Theorem 2.* Take σ = D^{−r}/2, and let L be the least even integer at least (16π(9s + 1))^{1/(1−r)}(4n)^{r/(1−r)}. Compile V followed by one more rotation, P′ ≤ 9s + 1 rotations in all. As in Theorem 1, they fit into 2P′(2πD^r + 2) ≤ L layers. The last rotation is e^{−iΦY_0} with Φ = π/8. It takes K ≥ (π/8)/σ = (π/4)D^r slots of angle Φ/K in odd layers, on site 0. Let z and x be the values of ⟨Z_0⟩ and ⟨X_0⟩ after V. Then

C(θ*) = cos(2Φ) z − sin(2Φ) x,  ∂_k C(θ*) = dC/dΦ = −2 sin(2Φ) z − 2 cos(2Φ) x

for each of the K slots k. From |z| ≥ 0.98 and |x| ≤ √(1 − z²) ≤ 0.199, we get |C(θ*)| ≥ (0.98 − 0.199)/√2 ≥ 0.55, with the sign of z, and |∂_k C(θ*)| ≥ √2(0.98 − 0.199) ≥ 1.10.

Every generator is a Pauli operator up to a Clifford conjugation and ‖Z_0‖ = 1. So |∂_j C| ≤ 2 and |∂_j ∂_k C| ≤ 4 everywhere. For θ ∈ Q, ‖θ − θ*‖_1 ≤ 0.01, hence

|C(θ) − C(θ*)| ≤ 0.02  and  |∂_k C(θ) − ∂_k C(θ*)| ≤ 0.04.

This gives parts 1 and 2. Since 0.01/D ≤ D^{−r}/2, Q lies in B_r. □

## Remarks

1. **Typical and atypical points.** For 1/2 < r < 1, random points of B_r are classically simulable with high probability [2, Theorem 2], [1, Theorem 4]. So the hard points of Theorem 1 are atypical there, and Theorem 2 needs a centre θ* that depends on V. That centre is a warm start computed from the instance. The ansatz and the observable are standard.
2. **The ℓ₁ view.** The hard points of Theorem 1 have ‖θ‖₁ ≤ πP/2 ≤ 9πs/2, whatever D is. Near-Clifford methods cost about exp(O(‖θ‖₁)) [1, Theorem 3]. So the quantity that matters is the total rotation ‖θ‖₁. The threshold r = 1 is how this appears for boxes, since ‖θ‖₁ ≤ D^{1−r} on B_r.
3. **Quantum-enhanced surrogates.** Theorem 2 rules out classical surrogates only. Surrogates built from quantum data cover boxes of width O(1/D) around arbitrary points [2, Theorem 1], so they cover Q. This fits the quantum-enhanced simulation of [3].
4. **Entangler.** The proof uses only E² = I and the three-body generator Z_{q−1}Y_qZ_{q+1}. It applies to any entangling layer of commuting CZ gates whose conjugated Y rotations connect neighbouring logical qubits in this way. Extra CZ neighbours on ancillas only add Z factors on qubits in |0⟩. The mHEA of [1] uses circular entanglement (CX in the EfficientSU2 default) and a final rotation layer; it is not covered here.
5. **Size.** For constant r, L = O((s n^r)^{1/(1−r)}), so D = O(nL) is polynomial; for r → 1 the degree grows like 1/(1 − r).
6. **Related statements.** Writing a rotation as many small ones with the same generator is standard, as in Trotterized simulation. [5] notes qualitatively that some architectures avoid barren plateaus and are worst-case hard to simulate, including deep circuits with small-angle initialization. Trainable and BQP-hard models built from two separate circuits are given in [4]. Theorems 1 and 2 are explicit versions for small-angle patches of a standard ansatz.

## Check

`sim/smallangle_check.py` has two parts.

- **Theorem 1.** It compiles random circuits of one-qubit gates and CZ gates on 2 and 3 logical qubits into the ansatz with σ = 0.1, 0.05 and 0.02. It also compiles one circuit of H, T and CZ gates at r = 0.3 with the L of Theorem 1. It simulates U(θ) layer by layer, not through the Heisenberg form, and compares the result with the target circuit.
- **Theorem 2.** It appends the rotation by π/8 and computes the K derivatives by finite differences. It then samples 20 points of Q and compares the differences of C and of the gradient with the bounds 2‖δ‖₁ and 4‖δ‖₁.

```
n = 2, N = 4, s = 6, L = 594, D = 4752, max|theta| = 0.098 <= 0.1: |<target|ansatz>| = 1.000000000000, C = +0.967341 vs +0.967341
n = 3, N = 6, s = 8, L = 1898, D = 22776, max|theta| = 0.050 <= 0.05: |<target|ansatz>| = 1.000000000000, C = -0.985701 vs -0.985701
n = 3, N = 6, s = 6, L = 3850, D = 46200, max|theta| = 0.020 <= 0.02: |<target|ansatz>| = 1.000000000000, C = +0.259857 vs +0.259857
H, T, CZ at r = 0.3: s = 3, L = 27052 (formula), D = 216416, max|theta| = 0.02493 <= D^-r = 0.02508, |<target|ansatz>| = 1.000000000000
sign +1: C(theta*) = +0.6719, min |dC/dtheta_k| over the last 4 slots = 1.4563; in the box of width 0.01/D: |dC|/l1 <= 0.014 (bound 2), |d grad|/l1 <= 0.020 (bound 4)
sign -1: C(theta*) = -0.7925, min |dC/dtheta_k| over the last 4 slots = 1.2151; in the box of width 0.01/D: |dC|/l1 <= 0.012 (bound 2), |d grad|/l1 <= 0.032 (bound 4)
small-angle compilation checks pass
```

## References

1. S. Meyer, F. Scala, F. Tacchino, A. Lucchi. Gradient Scalability and Taylor Surrogation of Quantum Cost Landscapes. arXiv:2507.06344.
2. S. Lerch, R. Puig, M. S. Rudolph, A. Angrisani, T. Jones, M. Cerezo, S. Thanasilp, Z. Holmes. Efficient quantum-enhanced classical simulation for patches of quantum landscapes. arXiv:2411.19896.
3. M. Cerezo, M. Larocca, D. García-Martín, N. L. Diaz, P. Braccia, E. Fontana, M. S. Rudolph, P. Bermejo, A. Ijaz, S. Thanasilp, E. R. Anschuetz, Z. Holmes. Does provable absence of barren plateaus imply classical simulability? Nature Communications 16, 7907 (2025), arXiv:2312.09121.
4. E. Gil-Fuster, C. Gyurik, A. Pérez-Salinas, V. Dunjko. On the relation between trainability and dequantization of variational quantum learning models. ICLR 2025, arXiv:2406.07072.
5. A. Deshpande, M. Hinsche, K. Najafi, K. Sharma, R. Sweke, C. Zoufal. Dynamic parameterized quantum circuits: expressive and barren-plateau free. arXiv:2411.05760.
