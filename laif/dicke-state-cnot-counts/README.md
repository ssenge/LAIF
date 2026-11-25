# Fewer CNOT gates for small symmetric weight-k states

2026-11-25

The symmetric weight-k state D(n, k) is the uniform superposition of all n-qubit basis states of Hamming weight k (called a Dicke state in [1]); D(n, 1) is the W state. The task is exact preparation from |0…0⟩ with arbitrary single-qubit gates and CNOT gates between any two qubits, counting CNOT gates. This is the model of the comparison in [1, Table IV], whose best counts are 7 for D(4, 1), 6 for D(4, 2) and 16 for D(5, 2).

## Results

| State | Previous best bound | Result |
|---|---|---|
| D(4, 2) | 6 CNOT gates [1, Table IV] | 5 CNOT gates |
| D(5, 2) | 16 CNOT gates [1, Table IV] | 9 CNOT gates |
| D(n, 1), n ≥ 3 | 3n − 5 CNOT gates [1, Table IV]; 2n − 2 implied by [2] | 2n − 3 CNOT gates (5 for n = 4) |

**Theorem 1.** D(4, 2) can be prepared exactly with 5 CNOT gates and real single-qubit rotations.

**Proposition 2.** For n ≥ 3, the W state on n qubits can be prepared exactly with 2n − 3 CNOT gates.

**Theorem 3.** D(5, 2) can be prepared exactly with 9 CNOT gates and real single-qubit rotations.

## Circuits

Conventions: qubit 0 is the leftmost tensor factor, R_y(θ) = exp(−iθY/2), and CNOT(a → b) has control a and target b.

**Theorem 1.** Let t = arccos √(2/3), so cos t = √(2/3) and sin t = 1/√3. First apply R_y(π/2) to qubit 0 and R_y(t) to qubit 1. Then apply five CNOT gates, each followed by a rotation on its control and one on its target:

| CNOT | Rotation on the control | Rotation on the target |
|---|---|---|
| 0 → 1 | none | R_y(t + 3π/2) on qubit 1 |
| 0 → 2 | R_y(π/2) on qubit 0 | none |
| 0 → 3 | R_y(t + π/2) on qubit 0 | R_y(2t + 2π) on qubit 3 |
| 0 → 1 | R_y(t + 3π/2) on qubit 0 | none |
| 1 → 2 | R_y(t + π) on qubit 1 | R_y(t − π) on qubit 2 |

The output is D(4, 2) exactly. All amplitudes are real.

**Proposition 2.** This is the linear circuit of [2] with its first block shortened. Apply R_y(a) to qubit 0 with sin(a/2) = 1/√n, then CNOT(0 → 1) and X on qubit 1. The state is now √((n−1)/n) |01⟩ + (1/√n) |10⟩ on the first two qubits. For i = 1, …, n − 2, let sin(φ_i/2) = 1/√(n − i), and apply R_y(φ_i/2) on qubit i + 1, CNOT(i → i + 1), R_y(−φ_i/2) on qubit i + 1 and CNOT(i + 1 → i). Qubit i + 1 is still |0⟩ when its step starts, so the first three gates act as a rotation of qubit i + 1 controlled by qubit i. The step maps |10⟩ to sin(φ_i/2) |10⟩ + cos(φ_i/2) |01⟩ on qubits i, i + 1, and fixes |00⟩. The first block costs 1 CNOT and each later step costs 2, which gives 2n − 3 in total.

**Theorem 3.** Let a = arccos √(3/5), b = arccos(1/√3) and c = arccos(1/√5). First apply R_y(−3π/2) to qubits 0 and 2, R_y(−a − 2π) to qubit 1, R_y(b) to qubit 3 and R_y(−c − 2π) to qubit 4. Then apply nine CNOT gates, each followed by a rotation on its control and one on its target:

| CNOT | Rotation on the control | Rotation on the target |
|---|---|---|
| 0 → 1 | R_y(−2π) | R_y(−a − 3π/2) |
| 0 → 4 | R_y(−3π/2) | R_y(c − 3π/4) |
| 3 → 1 | R_y(b − 2π) | R_y(−3π/2) |
| 0 → 1 | R_y(−7π/4) | R_y(3π/4) |
| 2 → 0 | R_y(−3π/2) | R_y(−2π) |
| 3 → 4 | R_y(−3π/2) | R_y(−π/4) |
| 0 → 4 | R_y(−3π/2) | R_y(−3π/2) |
| 3 → 4 | R_y(−2π) | R_y(−2π) |
| 1 → 0 | R_y(−2π) | R_y(−π) |

Here R_y(−2π) = −I changes only the global sign; the angles are listed as checked. The output is D(5, 2) exactly.

## Scope

- **Exact checks.** Theorems 1 and 3 are checked by exact symbolic elimination. Every half-angle cosine and sine is a polynomial in a few algebraic numbers: cos(t/2), sin(t/2), 1/√2 and 1/√3 for Theorem 1, and the half-angle cosines and sines of a, b, c and π/4 together with √2, √3 and √5 for Theorem 3. Each amplitude minus its target value reduces to zero modulo relations that hold at these numbers. Proposition 2 is checked exactly for n = 3 to 7: the difference of every amplitude and its target has minimal polynomial x.
- **Not formalized.** No part is in Lean. Minimality is not claimed: the counts are upper bounds.

## Files

- `sim/exact_d42.py`: the exact check of Theorem 1, and a floating-point cross-check (`python exact_d42.py`, needs sympy).
- `sim/exact_d52.py`: the exact check of Theorem 3 (`python exact_d52.py`, needs sympy).
- `sim/w_chain.py`: the exact check of Proposition 2 for n = 3 to 7 (`python -I w_chain.py`).
- `sim/search.py`: numerical search over CNOT placements with real rotations and an exact gradient. It found the circuits of Theorems 1 and 3 (`python search.py 4 2 5 6`; for five qubits it samples placements, `python search.py 5 2 9 4 4000 6`).

## Use of AI

The circuits, checks and text were produced with Claude Opus 5.5.

## References

1. H. Wang, B. Tan, J. Cong, G. De Micheli. Quantum state preparation using an exact CNOT synthesis formulation. arXiv:2401.01009.
2. D. Cruz, R. Fournier, F. Gremion, A. Jeannerot, K. Komagata, T. Tosic, J. Thiesbrummel, C. L. Chan, N. Macris, M.-A. Dupertuis, C. Javerzac-Galy. Efficient quantum algorithms for GHZ and W states, and implementation on the IBM quantum computer. Adv. Quantum Technol. 1900015 (2019). arXiv:1807.05572.
