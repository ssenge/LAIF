# T gates needed for an informationally complete single-setting measurement

2026-11-12

## Problem

An n-qubit state is measured by a single setting: stabilizer ancillas are added, a Clifford circuit with t T gates acts on all qubits, and the qubits are read out in a stabilizer basis. The effective measurement is informationally complete (IC) if its effects span all operators on the n qubits. In [1] it is shown that t ≥ 2n/log₂3 ≈ 1.26n T gates are necessary [1, Theorem 4] and t = 2n are sufficient [1, Theorem 5]. It is conjectured that 2n are also necessary [1, Conjecture 2], and this is verified there for n ≤ 3.

## Results

**Theorem 1.** In the model of [1, Section V], with any number of stabilizer ancillas, an IC measurement needs t ≥ (3 − log₂3) n ≈ 1.415 n T gates. Previous best bound: 2n/log₂3 ≈ 1.262 n [1, Theorem 4].

| n | 3 | 5 | 10 | 100 | 1000 |
|---|---|---|---|---|---|
| smallest t allowed by Theorem 1 | 5 | 8 | 15 | 142 | 1416 |
| smallest t allowed by [1, Theorem 4] | 4 | 7 | 13 | 127 | 1262 |
| t of the construction in [1, Theorem 5] | 6 | 10 | 20 | 200 | 2000 |

The improvement comes from a sharper count of Z-free Pauli strings in a subspace.

**Lemma 2.** Identify t-qubit Pauli strings up to phase with (F₂²)^t, and call a string Z-free if none of its coordinates is Z. A coset of a D-dimensional subspace of (F₂²)^t contains at most 3^{D−t} 2^{2t−D} Z-free strings if D ≥ t, and at most 2^D if D ≤ t. Both bounds are attained.

Lemma 2 is in effect a sharp upper bound for the exact count of Z-free strings in a centralizer given in [1, eq. (C1)].

## Proofs

*Lemma 2.* For D ≤ t the bound is the size of the coset. For D ≥ t, use induction on t, with the induction hypothesis for both regimes; for t = 1 the bound is 1, 2 or 3 for D = 0, 1, 2. Project the coset onto the last coordinate. The image is a coset of a subspace of F₂² of dimension r ∈ {0, 1, 2}, and it contains at most 1, 2 or 3 Z-free values. The fibre over each value is a coset of a subspace of dimension D − r on the other t − 1 coordinates.

- r = 0: then D ≤ 2t − 2, and the fibre bound 3^{D−t+1} 2^{2t−2−D} is 3/4 of the claim.
- r = 1: 2 · 3^{D−t} 2^{2t−D−1} equals the claim.
- r = 2 and D ≥ t + 1: 3 · 3^{D−t−1} 2^{2t−D} equals the claim.
- r = 2 and D = t: 3 · 2^{t−2} is below 2^t.

For D ≥ t, the subspace spanned by X and Y on D − t coordinates and by X alone on the other 2t − D attains the bound, and for D ≤ t, the subspace spanned by X on D coordinates does. ∎

*Theorem 1.* The measurement acts on N = n + m + t qubits: the n data qubits, m stabilizer ancillas in a state |ψ⟩ with stabilizer group R, and t gadget qubits in the magic state |T⟩, followed by a Clifford circuit and readout in a stabilizer basis [1, Section V]. The projector of each outcome is 2^{−N} Σ_{g∈S} ±g, with the same group S of Pauli strings for every outcome. Write π_n, π_m and π_t for the restrictions of a string to the three registers. The effect of an outcome is then a combination of the operators π_n(g) ⟨ψ|π_m(g)|ψ⟩ ⟨T^{⊗t}|π_t(g)|T^{⊗t}⟩. The middle factor vanishes unless π_m(g) ∈ ±R, and the last vanishes unless π_t(g) is Z-free, since ⟨T|Z|T⟩ = 0.

Let K be the set of restrictions of the strings g ∈ S with π_m(g) ∈ ±R to the data and gadget qubits. It is a subspace of (F₂²)^{n+t}. Its elements commute, since those of S and of R do, so dim K ≤ n + t. The effects span only operators π_n(k) with k ∈ K and π_t(k) Z-free, and IC needs all 4ⁿ data strings among them. An element of K with trivial gadget part commutes with all of K through its data part alone, and these data parts include every data string, so it is trivial. Hence π_t is injective on K. The image π_t(K) is a subspace of dimension D ≤ n + t that contains at least 4ⁿ Z-free strings. Lemma 2 bounds this number by 3^{D−t} 2^{2t−D} for D ≥ t and by 2^D for D < t; in both cases this gives 4ⁿ 2ⁿ ≤ 3ⁿ 2^t (Theorem 3 below), that is t ≥ n log₂(8/3) = (3 − log₂3) n. ∎

The proof of [1, Theorem 4] counts all 3^t Z-free strings on the gadget qubits. Lemma 2 counts only those in the subspace π_t(K), which has dimension at most n + t.

## Check

`sim/zfree.py` checks Lemma 2 with asserts: exhaustively over all subspaces and all cosets for t ≤ 4, where the maximum equals the bound for every D, on random cosets for t = 5 to 8, and on the extremal subspaces, which attain the bound. It also computes the table above. Output in `sim/zfree_out.txt`.

## Lean

The folder [lean/](lean/) checks Lemma 2 and the counting step of Theorem 1 in Lean 4 with Mathlib, with no `sorry` and only the standard axioms. Build it with `lake build`. Running `lake env lean ZFreeCount/Axioms.lean` prints the axioms of each theorem (output in `lean/axioms.txt`). Strings are vectors `Fin t → ZMod 2 × ZMod 2`, Z is (0, 1), and a subspace of dimension D is an additive subgroup with 2^D elements.

**Checked** (`ZFreeCount/Basic.lean`):

- **Lemma 2** (`zfree_count_le`): a coset of a subgroup with 2^D elements contains at most 2^D Z-free strings, and for D ≥ t their number c satisfies c · 2^D · 3^t ≤ 3^D · 4^t.
- **Theorem 3** (`zfree_tcount`): if a coset of a subgroup with 2^D elements, D ≤ n + t, contains at least 4ⁿ Z-free strings, then 4ⁿ 2ⁿ ≤ 3ⁿ 2^t.

**Not formalized:** the reduction in the proof of Theorem 1 from the measurement to the subspace π_t(K), and the extremal subspaces of Lemma 2.

## Scope

- Theorem 1 holds for every number m of stabilizer ancillas and every stabilizer readout in the model of [1, Section V] (stabilizer ancilla state, Clifford circuit with t T gates realized by magic state gadgets, a single measurement setting).
- At n = 1 Theorem 1 gives the conjectured value t = 2, and at n = 2 it gives the bound 3 of [1, Theorem 4]; the gain starts at n = 3.
- Written proof of Theorem 1, with Lemma 2 and its counting step (Theorem 3) checked in Lean.
- The bound 2n of [1, Conjecture 2] stays open for n ≥ 4.

## References

[1] G. Lo Monaco, S. Lorenzo, A. Ferraro, M. Paternostro, G. M. Palma, L. Innocenti. The non-stabilizerness cost of quantum state estimation. arXiv:2510.00157.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
