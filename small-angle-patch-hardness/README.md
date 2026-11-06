# Hardness of small-angle patches in a hardware-efficient ansatz

Written 6 Nov 2026.

## Setting

**Ansatz.** N qubits on a ring, sites 0, …, N − 1, and an even number L of layers. The cost is

U(θ) = E R_L ⋯ E R_1,  R_ℓ = ⊗_q e^{−iθ_{ℓ,q,y} Y_q} e^{−iθ_{ℓ,q,z} Z_q},  E = ∏_q CZ_{q,q+1},  C(θ) = ⟨0^N| U(θ)† Z_0 U(θ) |0^N⟩.

This is the hardware-efficient ansatz with Y and Z rotation layers and a ring of CZ gates. It has D = 2NL parameters. At θ = 0 the circuit is the Clifford E^L = I.

**Patches.** Write B_r = [−D^{−r}, D^{−r}]^D for the patch of width D^{−r} around θ = 0. Known results on B_r:

| Patch | Status |
|---|---|
| r ≥ 1 | the cost is computed classically to any constant precision at every point, in polynomial time: Taylor or Pauli path surrogates around the Clifford point [2, Proposition 1], [1, Theorem 3] |
| r > 1/2 | random points are classically simulable with high probability [2], [1, Theorem 4] |
| r < 1 | the Taylor surrogate of [1] needs super-polynomial time [1, Theorem 3]; [1] gives numerical evidence that gradients there decay only polynomially, and asks for formal proofs |

The question behind this, raised in [3] and [4], is whether polynomially large gradients and classical hardness can occur together in natural models.

## Results

**Theorem 1 (worst case).** Fix r ∈ [0, 1).
- Let V be a circuit of s gates on a ring of n ≥ 2 qubits, drawn from H, T and CZ between ring neighbours.
- Take N = 2n, and let L be the least even integer at least (72πs)^{1/(1−r)}(4n)^{r/(1−r)}.

A classical algorithm computes, in time poly(s, n), a point θ ∈ B_r, with entries rational multiples of π, such that

C(θ) = ⟨0^n| V† Z_0 V |0^n⟩.

So it is PromiseBQP-hard to evaluate C to ±1/3 on B_r. Unless PromiseBQP ⊆ PromiseBPP, no classical polynomial-time algorithm evaluates C to ±1/3 at every point of B_r.

Together with the case r ≥ 1 in the table, this makes r = 1 a sharp transition in worst-case complexity. The super-polynomial cost of the surrogate in [1, Theorem 3] is not an artifact of that method.

**Theorem 2 (regions with large gradients).** Fix r ∈ [0, 1), and let V be as above with output error at most 0.01: ⟨Z_0⟩ ≤ −0.98 on yes instances and ≥ 0.98 on no instances. With N = 2n and L as in the proof below, a classical algorithm computes, in time poly(s, n), a point θ* with ‖θ*‖_∞ ≤ D^{−r}/2 such that every point θ of the box

Q = θ* + [−0.01/D, 0.01/D]^D ⊆ B_r

satisfies:

1. |C(θ)| ≥ 0.53, and C(θ) has the sign of ⟨Z_0⟩ after V, so its sign is the answer;
2. at least K ≥ (π/4)D^r coordinates k have |∂_k C(θ)| ≥ 1. So ‖∇C(θ)‖ ≥ √K at every point of Q, and there is no barren plateau on Q.

So, unless PromiseBQP ⊆ PromiseBPP, there is no classical polynomial-time algorithm that, given θ* and any single point of Q, returns C at that point to ±1/2.

The boxes of [2, Proposition 1] around Clifford points have the same width O(1/D) and are classically easy. Theorem 2 shows that boxes of that width centred at other points of B_r can carry gradients of order one together with BQP-hardness.

## Proof

**Heisenberg form.** E is a product of commuting CZ gates, so E² = I. With L even,

U(θ) = ∏_{i = L/2, …, 1} (E R_{2i} E) R_{2i−1},

where E Z_q E = Z_q and E Y_q E = Z_{q−1} Y_q Z_{q+1}. So odd layers offer the rotations e^{−iαZ_q} and e^{−iαY_q}, and even layers offer e^{−iαZ_q} and e^{−iα Z_{q−1}Y_qZ_{q+1}}.

**Lemma 1 (accumulation).** Suppose only one slot of a layer is nonzero, and every layer between two such layers of the same parity is zero. Then those slots compose like consecutive rotations. So a rotation e^{−iφP} with |φ| ≤ π and P one of the four types above takes K = ⌈|φ|/σ⌉ layers of the right parity, each with angle φ/K, where |φ/K| ≤ σ. Including the zero layers in between, it uses at most 2K layers. Unused layers are zero and act as the identity.

*Proof.* A zero layer is E·I = E, and E² = I, so the zero layers cancel in pairs. By the Heisenberg form, a slot in an odd (even) layer acts as the rotation of its type above. Rotations with the same generator add. □

**Compilation.** Logical qubit j sits at site 2j, and the ancilla at site 2j + 1 stays in |0⟩.

- **One-qubit gate on logical j.** It has an Euler form e^{−iaZ}e^{−ibY}e^{−icZ}, so it takes 3 rotations on site 2j.
- **CZ between logical j and j + 1.** Write m = 2j + 1, and let G be a one-qubit Clifford with G Y G† = ±Z, for example e^{−iπX/4}. Then

  G_m e^{−iα Z_{m−1} Y_m Z_{m+1}} G_m† = e^{∓iα Z_{m−1} Z_m Z_{m+1}},

  which acts as e^{∓iα Z_{m−1} Z_{m+1}} while the ancilla is in |0⟩. With α = ∓(−π/4) this is e^{iπZ_aZ_b/4}. Then

  CZ_{ab} = e^{iπ/4} e^{−iπZ_a/4} e^{−iπZ_b/4} e^{iπZ_aZ_b/4}.

  G and G† cost 3 rotations each by their Euler forms, so the CZ costs 3 + 1 + 3 + 2 = 9 rotations. The ancilla returns to |0⟩.

So V becomes P ≤ 9s rotations, each with |angle| ≤ π, and every angle is a rational multiple of π.

*Proof of Theorem 1.* Take σ = D^{−r} with D = 4nL. By Lemma 1 the compiled circuit fits into 2P(πD^r + 1) layers. The choice of L gives L^{1−r} ≥ 8πP(4n)^r and L ≥ 8πP, hence 2PπD^r ≤ L/4 and 2P ≤ L/4. So the circuit fits into L layers with all angles at most D^{−r}.

Then U(θ)|0^N⟩ is V|0^n⟩ on the even sites with the ancillas in |0⟩, up to a global phase, so C(θ) = ⟨Z_0⟩ = 1 − 2 Pr[V outputs 1]. A promise problem in BQP has a uniform family of such circuits, with ⟨Z_0⟩ ≤ −1/3 on yes instances and ≥ 1/3 on no instances. An estimate of C(θ) to within less than 1/3 decides it. □

*Proof of Theorem 2.* Take σ = D^{−r}/2, and let L be the least even integer at least (16π(9s + 1))^{1/(1−r)}(4n)^{r/(1−r)}. Compile V followed by one more rotation, P′ ≤ 9s + 1 rotations in all; as in Theorem 1 they fit into 2P′(2πD^r + 1) ≤ L layers. The last rotation is e^{−iΦY_0} with Φ = π/8, which takes K = ⌈(π/8)/σ⌉ ≥ (π/4)D^r slots of angle Φ/K in odd layers, on site 0. Let z and x be the values of ⟨Z_0⟩ and ⟨X_0⟩ after V. Then

C(θ*) = cos(2Φ) z − sin(2Φ) x,  ∂_k C(θ*) = dC/dΦ = −2 sin(2Φ) z − 2 cos(2Φ) x

for each of the K slots k. From |z| ≥ 0.98 and |x| ≤ √(1 − z²) ≤ 0.199, we get |C(θ*)| ≥ (0.98 − 0.199)/√2 ≥ 0.55, with the sign of z, and |∂_k C(θ*)| ≥ √2(0.98 − 0.199) ≥ 1.10.

Every generator is a Pauli operator up to a Clifford conjugation and ‖Z_0‖ = 1. So |∂_j C| ≤ 2 and |∂_j ∂_k C| ≤ 4 everywhere. For θ ∈ Q, ‖θ − θ*‖_1 ≤ 0.01, hence

|C(θ) − C(θ*)| ≤ 0.02  and  |∂_k C(θ) − ∂_k C(θ*)| ≤ 0.04.

This gives parts 1 and 2. Since 0.01/D ≤ D^{−r}/2, Q lies in B_r. □

## Remarks

1. **Typical and atypical points.** For 1/2 < r < 1, random points of B_r are classically simulable with high probability [2], [1, Theorem 4]. So the hard points of Theorem 1 are atypical there, and Theorem 2 needs a centre θ* that depends on V. That centre is a warm start computed from the instance. The ansatz and the observable are standard.
2. **Quantum-enhanced surrogates.** Theorem 2 rules out classical surrogates only. A surrogate built from quantum data, as in [2] and [3], may still cover Q, for instance from estimates of C and its derivatives at θ*.
3. **Entangler.** The proof uses only E² = I and the three-body generator Z_{q−1}Y_qZ_{q+1}. It applies to any entangling layer of commuting CZ gates whose conjugated Y rotations connect neighbouring logical qubits in this way. The mHEA of [1] uses a circular CX layer, which is not covered here.
4. **Size.** For constant r, L = O((s n^r)^{1/(1−r)}), so D = O(n L) is polynomial; for r → 1 the degree grows like 1/(1 − r).

## Check

`sim/smallangle_check.py` compiles random circuits of one-qubit gates and CZ gates on 2 and 3 logical qubits into the ansatz with σ = 0.1, 0.05 and 0.02. It simulates U(θ) layer by layer, not through the Heisenberg form, and compares the result with the target circuit.

For Theorem 2 it appends the rotation by π/8, computes all K derivatives by finite differences, and samples 20 points of Q to compare differences of C and of the gradient with the bounds 2‖δ‖_1 and 4‖δ‖_1.

```
n = 2, N = 4, s = 6, L = 648, D = 5184, max|theta| = 0.098 <= 0.1: |<target|ansatz>| = 1.000000000000, C = +0.967341 vs +0.967341
n = 3, N = 6, s = 8, L = 1996, D = 23952, max|theta| = 0.050 <= 0.05: |<target|ansatz>| = 1.000000000000, C = -0.985701 vs -0.985701
n = 3, N = 6, s = 6, L = 3850, D = 46200, max|theta| = 0.020 <= 0.02: |<target|ansatz>| = 1.000000000000, C = +0.259857 vs +0.259857
sign +1: C(theta*) = +0.7086, min |dC/dtheta_k| over the last 4 slots = 1.3829; in the box of width 0.01/D: |dC|/l1 <= 0.013 (bound 2), |d grad|/l1 <= 0.021 (bound 4)
sign -1: C(theta*) = -0.6890, min |dC/dtheta_k| over the last 4 slots = 1.4221; in the box of width 0.01/D: |dC|/l1 <= 0.012 (bound 2), |d grad|/l1 <= 0.016 (bound 4)
small-angle compilation checks pass
```

## References

1. S. Meyer, F. Scala, F. Tacchino, A. Lucchi. Gradient Scalability and Taylor Surrogation of Quantum Cost Landscapes. arXiv:2507.06344.
2. S. Lerch, R. Puig, M. S. Rudolph, A. Angrisani, T. Jones, M. Cerezo, S. Thanasilp, Z. Holmes. Efficient quantum-enhanced classical simulation for patches of quantum landscapes. arXiv:2411.19896.
3. M. Cerezo, M. Larocca, D. García-Martín, N. L. Diaz, P. Braccia, E. Fontana, M. S. Rudolph, P. Bermejo, A. Ijaz, S. Thanasilp, E. R. Anschuetz, Z. Holmes. Does provable absence of barren plateaus imply classical simulability? Nature Communications 2025, arXiv:2312.09121.
4. E. Gil-Fuster, C. Gyurik, A. Pérez-Salinas, V. Dunjko. On the relation between trainability and dequantization of variational quantum learning models. ICLR 2025, arXiv:2406.07072.
