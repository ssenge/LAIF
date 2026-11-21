# Exact ground states of six lattice protein-folding instances on 46 to 61 qubits

_21 November 2026_

In [1], six peptides with 14 to 16 residues are encoded in the dense tetrahedral-lattice Hamiltonian of [2] (main chain only, contact energies of [3]), which needs 46 to 61 qubits and has terms of up to five spins. Bias-field digitized counterdiabatic optimization runs on a 64-qubit trapped-ion system, and its samples seed classical post-processing. The reference energies E_ref of [1, Table II] come from a classical genetic algorithm run until convergence. Quantum-seeded consensus post-processing reaches E_ref on 4 of the 6 sequences and random-seeded on 1; on the two 61-qubit sequences neither reaches it.

## Result

The ground state of the same Hamiltonian, computed exactly. For a fixed backbone (the turn qubits), the Hamiltonian is a sum of terms q_ij B_ij with one contact qubit q_ij each, so the best contact qubits are q_ij = [B_ij < 0]. The ground state is then the minimum over all 2^(2N−7) assignments of the free turn qubits, 2.1 · 10⁶ at N = 14 and 3.4 · 10⁷ at N = 16, which are enumerated.

| Sequence | Qubits | Exact ground state | Ground states | E_ref [1] | Best, quantum-seeded [1] | Best, random-seeded [1] | Time (s) |
|---|---|---|---|---|---|---|---|
| IDWKKLLDAAKQIL | 46 | **−8.698** | 2 | −8.698 | −8.698 | −8.698 | 1.1 |
| RGKWTYNGITYEGR | 46 | **−5.162** | 2 | −5.162 | −5.162 | −5.042 | 0.8 |
| KWKLFKKIGAVLKVL | 53 | **−9.321** | 3 | −9.321 | −9.321 | −9.321 | 4.3 |
| LEPFSGKALCSWSIC | 53 | **−8.463** | 3 | −8.463 | −8.463 | −8.159 | 3.0 |
| MRWQEMGYIFYPRKLR | 61 | **−9.598** | 1 | −9.598 | −8.819 | −9.010 | 14.1 |
| VARGWKRKCPLFGKGG | 61 | **−8.155** | 1 | −8.155 | −7.793 | −7.450 | 13.0 |

"Best" is the lower of the two post-processing pipelines of [1, Table II]. The times are wall-clock times on one core of an Apple M4 Pro laptop (Python with numba).

On all six sequences the exact ground state equals E_ref to the printed digits, so the reference energies of [1] are the optima of these instances. Every ground state is a self-avoiding backbone with no backtracking turns and five contacts. The exhaustive search certifies the optimum in at most 14 s on one core, including the two 61-qubit instances. This hints at a possible gap in reading the hit rate against E_ref as a sign that these instances are hard: an exact classical enumeration of the backbones solves each of them.

## Hamiltonian

The Hamiltonian is rebuilt term by term from the implementation of [2] in qiskit-nature 0.4.5 (`ProteinFoldingProblem`, main chain only). Turn t_k ∈ {0, 1, 2, 3} after bead k uses two qubits. The first two turns and one qubit of the third are fixed by symmetry, so 2N − 7 turn qubits remain. One contact qubit is used per pair of beads i < j with j − i odd and at least 5, which gives 25, 30 and 36 contact qubits at N = 14, 15 and 16; the qubit counts agree with [1, Table I]. With P_m = Σ_{k≤m} (−1)^k e_{t_{k−1}} ∈ ℤ⁴ and x(i, j) = |P_{j−1} − P_{i−1}|²,

H = λ_b Σ_k [t_k = t_{k+1}] + Σ_{ij} q_ij B_ij,

B_ij = λ₀(x(i, j) − 1) + 0.1 ε_ij + Σ_{(k,l)} (λ₁(2 − x(k, l)) + 0.1 ε_kl),

where (k, l) runs over the pairs (i ± 1, j) and (i, j ± 1) inside the chain, λ₀ = 7(j − i + 1)λ₁, and ε is the residue contact energy of [3].

[1] does not state its penalty constants λ_b and λ₁. The ground states and their energies are the same for λ_b = λ₁ = 5, 10, 15 and 100 (`data/penalties.jsonl`). The agreement of the exact minima with E_ref on all six sequences also checks the rebuilt Hamiltonian, since nothing is fitted.

## Scope

- **Exact within the encoding.** The minimum is over every assignment of the free turn and contact qubits of the Hamiltonian above, including backbones that backtrack or overlap. The reduction to the turn qubits is checked against a joint brute force over all turn and contact qubits for random sequences with N = 8 and 9.
- **Not run.** The quantum circuits and the post-processing of [1]. The values of [1] are those printed in its Table II.
- **Not formalized.** The search is a numerical computation.

## Files

- `sim/fold_exact.py`: the Hamiltonian and the exhaustive search. `python -I fold_exact.py SEQ [λ_b λ₁]` prints the ground state; `python -I fold_exact.py test` checks the qubit counts of [1, Table I], the reduction against the joint brute force, and the lattice positions.
- `sim/mj_matrix.txt`: the contact energies of [3] as shipped with qiskit-nature 0.4.5, unchanged (Apache License 2.0, `sim/LICENSE-mj_matrix.txt`).
- `data/ground_states.jsonl`: per sequence the energy, the turns of one ground state, its contacts, the number of ground states and the time; `data/penalties.jsonl`: the same for other penalty constants.

## References

1. A. Gomez Cadavid, P. Nikačević, P. Chandarana, S. V. Romero, E. Solano, N. N. Hegade, M. A. Lopez-Ruiz, C. Girotto, H. Linn, H. Doga, E. Epifanovsky, P. Kl. Barkoutsos, A. Kaushik, M. Roetteler. Protein folding on a 64 qubit trapped-ion hardware via counterdiabatic quantum optimization. arXiv:2604.26861.
2. A. Robert, P. Kl. Barkoutsos, S. Woerner, I. Tavernelli. Resource-efficient quantum algorithm for protein folding. npj Quantum Information 7, 38 (2021). arXiv:1908.02163.
3. S. Miyazawa, R. L. Jernigan. Residue-residue potentials with a favorable contact pair term and an unfavorable high packing density term, for simulation and threading. Journal of Molecular Biology 256(3), 623–644, 1996.
