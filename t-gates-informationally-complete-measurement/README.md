# T gates needed for an informationally complete single-setting measurement

2026-11-12

## Problem

An n-qubit state is measured by a single setting: stabilizer ancillas are added, a Clifford circuit with t T gates acts on all qubits, and the qubits are read out in a stabilizer basis. The effective measurement is informationally complete (IC) if its effects span all operators on the n qubits. In [1] it is shown that t ≥ 2n/log₂3 ≈ 1.26n T gates are necessary [1, Theorem 4] and t = 2n are sufficient [1, Theorem 5]. It is conjectured that 2n are also necessary [1, Conjecture 2], and this is verified there for n ≤ 3.

## Results

**Theorem 1.** In the setting of [1, Theorem 4], an IC measurement needs t ≥ (3 − log₂3) n ≈ 1.415 n T gates. Previous best bound: 2n/log₂3 ≈ 1.262 n [1, Theorem 4].

| n | 3 | 5 | 10 | 100 | 1000 |
|---|---|---|---|---|---|
| smallest t allowed by Theorem 1 | 5 | 8 | 15 | 142 | 1416 |
| smallest t allowed by [1, Theorem 4] | 4 | 7 | 13 | 127 | 1262 |
| t of the construction in [1, Theorem 5] | 6 | 10 | 20 | 200 | 2000 |

The improvement comes from a sharper count of Z-free Pauli strings in a subspace.

**Lemma 2.** Identify t-qubit Pauli strings up to phase with (F₂²)^t, and call a string Z-free if none of its coordinates is Z. A coset of a D-dimensional subspace of (F₂²)^t contains at most 3^{D−t} 2^{2t−D} Z-free strings if D ≥ t, and at most 2^D if D ≤ t. Both bounds are attained.

## Proofs

*Lemma 2.* For D ≤ t the bound is the size of the coset. For D ≥ t, use induction on t; for t = 1 the bound is 1, 2 or 3 for D = 0, 1, 2. Project the coset onto the last coordinate. The image is a coset of a subspace of F₂² of dimension r ∈ {0, 1, 2}, and it contains at most 1, 2 or 3 Z-free values. The fibre over each value is a coset of a subspace of dimension D − r on the other t − 1 coordinates.

- r = 0: then D ≤ 2t − 2, and the fibre bound 3^{D−t+1} 2^{2t−2−D} is 3/4 of the claim.
- r = 1: 2 · 3^{D−t} 2^{2t−D−1} equals the claim.
- r = 2 and D ≥ t + 1: 3 · 3^{D−t−1} 2^{2t−D} equals the claim.
- r = 2 and D = t: 3 · 2^{t−2} is below 2^t.

Subspaces spanned by X and Y on some coordinates and by X alone on the others attain the bound. ∎

*Theorem 1.* The proof of [1, Theorem 4] in its second form reduces IC to the following condition. There is a stabilizer group S on n + t qubits with |S| = 2^{n+t}, whose subgroup S_t acting only on the t gadget qubits has 2^{t−n} elements, and whose projection π_t onto the gadget qubits is injective on S. In addition, each of the 4ⁿ cosets of S_t in S must contain an element g with π_t(g) Z-free [1, eq. (22)], because ⟨T|Z|T⟩ = 0 for the magic state |T⟩. The image π_t(S) is a subspace of (F₂²)^t of dimension n + t ≥ t. By Lemma 2 it contains at most 3^{n} 2^{t−n} Z-free strings. The cosets of π_t(S_t) in π_t(S) are disjoint, and each needs one of these strings, so 3ⁿ 2^{t−n} ≥ 4ⁿ, that is t ≥ n + n log₂(4/3) = (3 − log₂3) n. ∎

## Check

`sim/zfree.py` checks Lemma 2 with asserts, exhaustively over all subspaces and all cosets for t ≤ 3, where the maximum equals the bound for every D, and on random cosets for t = 4 to 8. It also computes the table above. Output in `sim/zfree_out.txt`.

## Scope

- **Assuming:** the reduction of [1, Section V] to stabilizer groups on n + t qubits with maximal entanglement between the data and the gadget qubits, under the same assumptions as [1, Theorem 4] (in particular, the projection of the stabilizer ancillas leaves an (n + t)-qubit stabilizer measurement).
- **Not formalized:** the results have no Lean proof.
- The bound 2n of [1, Conjecture 2] stays open for n ≥ 4.

## References

[1] G. Lo Monaco, S. Lorenzo, A. Ferraro, M. Paternostro, G. M. Palma, L. Innocenti. The non-stabilizerness cost of quantum state estimation. arXiv:2510.00157.

## Use of AI

The result, proofs and scripts were developed with Claude Opus 5.5 (Anthropic).
