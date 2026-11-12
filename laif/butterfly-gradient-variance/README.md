# Gradient variance of the unitary butterfly at quarter filling

Written 7 Nov 2026.

## Problem

[1] trains k-particle fermionic circuits on n modes. The input has k/2 blocks (|1100⟩ + |0011⟩)/√2 on the modes 0, …, 2k − 1, with the other n − 2k modes empty. It is spread by the sign transform H_ab = (−1)^{a·b}/√n on mode labels a, b ∈ {0, …, n − 1} (a·b is the bitwise inner product), and a layer of data phases follows [1, Section II]. The trainable circuit is the unitary butterfly [1, Section III C]: for n = 2^K, layer ℓ = 1, …, K applies one Rz phase to every mode and then rotations on the n/2 pairs at stride 2^{ℓ−1}. All angles and phases are independent and uniform on [0, 2π). The loss is L = ⟨n_i n_j⟩ for a pair of modes i ≠ j.

For a parameter whose prefix circuit is the identity, such as a phase φ_p of the first Rz layer, [1] writes the gradient variance as a single scalar: the pairing of the fourth moment of the two-particle action of the circuit with B ⊗ B, where B is the commutator of the gate generator with the encoded two-particle density matrix. As in the proof of [1, Claim 1], the scalar is read with the conjugation L2(W)† M L2(W) that the gradient uses, where L2(W) is the two-particle action of the circuit and M the readout (for the uniform unitary the two conjugations agree; for the butterfly they do not, since W and W† have different laws). For the uniformly distributed unitary this scalar is evaluated exactly [1, Theorem 11]: it is Θ(k³/n⁵) whenever n − 2k = Ω(n).

**Conjecture 22 of [1].** Fix 0 < γ < 1/2. There are constants 0 < c ≤ C, independent of n and k, such that for every even k with 2 ≤ k ≤ γn, every readout n_i n_j and every such parameter, the butterfly value of this scalar lies between c and C times the value for the uniform unitary.

Under this conjecture, [1, Theorem 21] gives the gradient variance Θ(k³/n⁵) for the butterfly, for k ≤ γ₀n with γ₀ small. [1] also notes that the fourth moment is out of reach of its recursion for the second moment.

## Result

**Theorem 1.** Let n = 2^K ≥ 8 and k = n/4. Take the readout n_0 n_{n/2} and the phase φ_0 of mode 0 in the first Rz layer. Then for every data input x, E[∂L/∂φ_0] = 0 and

Var[∂L/∂φ_0] = 9^K/(18n⁶) + 4·9^K/(3n⁷) − 1/(16n³) − 3/(2n⁴) = (1 + o(1)) n^{2log₂3 − 6}/18,

with 2log₂3 − 6 ≈ −2.830. For n = 8, 16, 32 the values are 17/131072, 1085/67108864 and 17255/8589934592.

**Corollary 2.** For the uniform unitary the same scalar is at least 2(k − 1)²(k/n)(1 − 2k/n)/(n²(n² − 1)) = (1 + o(1))/(64n²) [1, Theorem 11 and Claim 2]. So in Theorem 1 the ratio of the butterfly value to the uniform value is at most (32/9 + o(1)) n^{2log₂3 − 4}, with 2log₂3 − 4 ≈ −0.830, and it tends to 0. Since k = n/4 ≤ γn for every γ ≥ 1/4, Conjecture 22 does not hold for any γ in [1/4, 1/2). For this readout at k = n/4 the variance is n^{−2.83+o(1)}, far below the rate k³/n⁵ = n^{−2}/64, and for n ≥ 32 also below k⁴/n⁶ = n^{−2}/256. [1, Theorem 19] gives Ω(k⁴/n⁶) for some readout and some rotation angle, so it is consistent with this.

So the range of γ in Conjecture 22 needs γ < 1/4. [1] already expects the upper constant to fail on a range that reaches k = n/2; here the lower constant fails at k = n/4.

**Why.** The last layer rotates the pair of modes (i, i + n/2), and n_i n_j is invariant under every unitary on these two modes. So L depends only on the rows x and y of mode i in the two half-size butterflies. At 2k = n/2 the spread input puts every particle in the even combination of the two halves, so ⟨n(x)⟩ = ⟨n(y)⟩ = 1/4 for all angles, including φ_0. The one-particle part of the signal, which carries the rate Θ(k³/n⁵) for the uniform unitary, therefore vanishes for this readout. In the closed form the leading base is 9/64 = (3/8)², the square of E[cos⁴θ], a fourth moment of the rotation entries along the paths of the butterfly.

**Other cases (exact values, n up to 32768).** The recursion below also evaluates the scalar exactly for other readouts and fillings. With p = 0, i = 0 and j ∈ {1, n/4, n/2, n/2 + 1}, the ratio to the uniform value converges in all tested cases except the one of Theorem 1: it tends to 1 for k = 2 (0.973 to 0.980 at n = 32768, above 0.997 at n = 2^24), to 0.334 to 0.584 for k = n/8, and to 0.500 for k = n/4 with j ≠ n/2. These values are consistent with Conjecture 22 for γ < 1/4.

## Method: an exact recursion for the fourth moment

Write W for the single-particle matrix of the butterfly, with the first Rz layer included, and a_m = conj(W_{im}), b_m = conj(W_{jm}). Then

∂L/∂φ_p = Σ conj(W_{iα}) conj(W_{jβ}) W_{jγ} W_{iδ} D_{αβγδ},  D_{αβγδ} = i(χ_α + χ_β − χ_γ − χ_δ) E_{αβγδ},

where E_{αβγδ} = ⟨c†_α c†_β c_γ c_δ⟩ in the spread input and χ is the indicator of mode p. So (∂L/∂φ_p)² is a sum over 8 mode indices of 4 entries of W, 4 entries of conj W and D ⊗ D.

1. **Paths.** An entry W_{a,m} is a product over the layers: layer ℓ contributes the rotation entry (output bit a_{ℓ−1}, input bit m_{ℓ−1}) of the gate whose pair is labelled by the bits of a below ℓ − 1 and the bits of m above ℓ − 1, and the phase of R_ℓ at the mode whose bits below ℓ − 1 are those of a and whose other bits are those of m.
2. **Averages.** Layers, gates within a layer, and phases are independent. A phase average is 1 if the modes of the 4 entries of W and of the 4 entries of conj W agree as multisets, and 0 otherwise. A gate average is a moment E[cos^a θ sin^b θ] = (a − 1)!!(b − 1)!!/(a + b)!! (0 unless a, b are even), and it depends only on which of the 8 slots share the gate.
3. **Bits.** Process the bits of the input indices from K − 1 down to 0. At layer ℓ, which slots share a gate and which phases must match depend on the input bits above ℓ − 1 only through the partition of the 8 slots by equality of those bits. The rows i, j fix the other bits.
4. **Input.** The sign transform is a product over bits; the projector onto the active modes is a product over bits when 2k is a power of 2; and the block correction to the pairing formula lives on bits 0 and 1, with equality of all other bits. So D ⊗ D is a sum of products of tensors on single bits, joined on bits 0 and 1.

Hence E[(∂L/∂φ_p)²] is a sum, over the product terms, of products of K matrices acting on functions of the partition. At most 4140 partitions occur, and in practice about 130. The recursion takes O(log n) steps for any i, j, p when 2k is a power of 2.

**Proof of Theorem 1 (computer-assisted).** The data phases are diagonal in the modes, so they commute with n_p and are absorbed into the uniform phases of the first Rz layer; the law of the circuit, and hence the variance, does not depend on x. E[∂L/∂φ_0] = 0 because the derivative of a periodic function in φ_0 averages to 0. For the readout (0, n/2), p = 0 and k = n/4, the bit types are fixed: the top bit has empty modes and i, j differ there; the middle bits K − 2, …, 2 all have the same type; bits 1 and 0 carry the blocks. So

Var = −Σ_τ w_τ^T M_τ^{K−3} u_τ

for each product term τ, with fixed rational matrices M_τ (one middle bit), start vectors u_τ (top bit) and end vectors w_τ (bits 1 and 0). In exact rational arithmetic:

- every u_τ is annihilated by G(M_τ), where G has the 20 simple roots 3/8, 5/16, 9/32, 35/128, 1/4, 3/16, 5/32, 9/64, 35/256, 1/8, 3/32, 5/64, 9/128, 35/512, 1/16, 3/64, 5/128, 9/256, 1/32, 3/128;
- so the sequence satisfies the linear recurrence with characteristic polynomial G;
- the closed form is a combination of (9/64)^K, (9/128)^K, (1/8)^K and (1/16)^K, so it satisfies the same recurrence;
- the two agree exactly for K = 3, …, 23, more than the 20 values that determine a solution, so they agree for all K ≥ 3.

The coefficients of the larger roots 3/8, …, 5/32 vanish. The reduction of the variance to the recursion is the argument of the Method section; the exact arithmetic certifies the evaluation of the recursion.

## Scope

- Theorem 1 is for the readout (0, n/2) and the phase of mode 0 in the first Rz layer. By the recursion, the value is the same for i ∈ {0, 5} with j = i + n/2 (mod n) and for p ∈ {0, 7, …, 63} at n = 64; the general case is not proved here.
- The recursion needs 2k to be a power of 2. Fillings between n/8 and n/4 are not covered.
- [1, Theorem 21] is stated for k ≤ γ₀n with γ₀ small, and is not contradicted. For γ < 1/4 the conjecture remains open; the exact values above are consistent with it.

## Check

- `sim/butterfly.py` (numpy): the sampling estimator, the recursion and the closed form for the uniform unitary.
  1. It compares the recursion with 10⁶ samples of the gradient at n = 8, 32, 64, and the uniform value with samples of the uniform unitary.
  2. It checks the closed form |B|² = (k(k + 2)n/2 − k³ + 3k²/2 − 3k)/n² against its definition.
  3. It prints the ratio table and the independence of i and p at n = 64.
- `sim/proof.py` (exact fractions, about a minute): the exact proof of Theorem 1.

Output of `sim/proof.py`:

```
reachable partitions: 131
roots (value: multiplicity): {'3/8': 1, '5/16': 1, '9/32': 1, '35/128': 1, '1/4': 1, '3/16': 1, '5/32': 1, '9/64': 1, '35/256': 1, '1/8': 1, '3/32': 1, '5/64': 1, '9/128': 1, '35/512': 1, '1/16': 1, '3/64': 1, '5/128': 1, '9/256': 1, '1/32': 1, '3/128': 1}
degree of G: 20
closed form equals s(K) exactly for K = 3 .. 23
the four roots of the closed form are roots of G, so both sides satisfy the same recurrence: formula holds for all K >= 3
```

Output of `sim/butterfly.py`:

```
1. recursion against sampling (mean of (dL/dphi_p)^2, 10^6 samples), and the uniform value against sampling
   n=  8 k= 2 (i,j)=(0, 1) p=0: recursion 4.4274e-04, sampled 4.3903e-04 +- 1e-06; uniform 4.3403e-04, sampled 4.3361e-04 +- 9e-07
   n=  8 k= 2 (i,j)=(0, 4) p=0: recursion 1.2970e-04, sampled 1.3042e-04 +- 3e-07; uniform 4.3403e-04, sampled 4.3361e-04 +- 9e-07
   n= 32 k= 8 (i,j)=(0,16) p=0: recursion 2.0087e-06, sampled 2.0139e-06 +- 1e-08; uniform 1.4826e-05, sampled 1.4846e-05 +- 3e-08
   n= 64 k=16 (i,j)=(0,32) p=0: recursion 2.6293e-07, sampled 2.6061e-07 +- 2e-09; uniform 3.6712e-06, sampled 3.6766e-06 +- 7e-09
   n= 64 k=16 (i,j)=(0, 1) p=0: recursion 1.9694e-06, sampled 1.9806e-06 +- 2e-08; uniform 3.6712e-06, sampled 3.6800e-06 +- 7e-09
2. closed form of |B|^2 equals its definition at (n, k) = (8, 2), (16, 2), (32, 2), (64, 2), (16, 4), (32, 8), (64, 16), (128, 32)
3. ratio of the butterfly value to the uniform value, i = 0, p = 0
   k=2    n=    64: j=1 0.8641, j=n/4 0.7064, j=n/2 0.677788, j=n/2+1 0.8641
   k=2    n=   512: j=1 0.9071, j=n/4 0.8669, j=n/2 0.854701, j=n/2+1 0.9071
   k=2    n=  4096: j=1 0.9550, j=n/4 0.9423, j=n/2 0.937079, j=n/2+1 0.9550
   k=2    n= 32768: j=1 0.9802, j=n/4 0.9754, j=n/2 0.973209, j=n/2+1 0.9802
   k=n/8  n=    64: j=1 0.6345, j=n/4 0.4568, j=n/2 0.384713, j=n/2+1 0.6345
   k=n/8  n=   512: j=1 0.5882, j=n/4 0.4230, j=n/2 0.341498, j=n/2+1 0.5882
   k=n/8  n=  4096: j=1 0.5842, j=n/4 0.4180, j=n/2 0.334990, j=n/2+1 0.5842
   k=n/8  n= 32768: j=1 0.5835, j=n/4 0.4169, j=n/2 0.333665, j=n/2+1 0.5835
   k=n/4  n=    64: j=1 0.5364, j=n/4 0.5379, j=n/2 0.071618, j=n/2+1 0.5364
   k=n/4  n=   512: j=1 0.5046, j=n/4 0.5053, j=n/2 0.012902, j=n/2+1 0.5046
   k=n/4  n=  4096: j=1 0.5008, j=n/4 0.5009, j=n/2 0.002609, j=n/2+1 0.5008
   k=n/4  n= 32768: j=1 0.5002, j=n/4 0.5002, j=n/2 0.000513, j=n/2+1 0.5002
4. n = 64, k = 16, readout (i, i + 32): the same value for i in {0, 5} and p in {0, 7, ..., 63}
```

In step 1 the sampled value for n = 8, (i, j) = (0, 1) lies 3.2 standard errors from the exact value 4.42743e-4 for this seed; with other seeds the deviation is below 0.4 standard errors. The heavy tails of (∂L/∂φ_p)² make the printed error estimates unreliable at this level.

## References

1. I. Kerenidis. Scalable Quantum Machine Learning: Trainability, Expressivity and Efficiency. arXiv:2607.24014v3 (2026).
