# Fewer CNOT gates for small symmetric weight-k states

2026-11-25

The symmetric weight-k state D(n, k) is the uniform superposition of all n-qubit basis states of Hamming weight k. The task is exact preparation from |0…0⟩ with arbitrary single-qubit gates and CNOT gates between any two qubits, counting CNOT gates. This is the model of the comparison in [1, Table IV], whose best counts are 6 for D(4, 2), 16 for D(5, 2), 22 for D(6, 2) and 25 for D(6, 3). The counts of [1] are optimal within the gate library used there, which builds a state from single-target rotations controlled by basis states; the circuits below use CNOT placements outside that library. A later method of the same line reports about 33 CNOT gates for D(6, 3) [2, Fig. 3e, read from the plot]. For D(8, 2), an explicit circuit with 27 CNOT gates is given in [3, Fig. 6], and one with 31 CNOT gates on a 2 × 4 grid of qubits, where CNOT gates act only between neighbours, in [3, Fig. 7].

## Results

| State | Previous best bound | Result |
|---|---|---|
| D(4, 2) | 6 CNOT gates [1, Table IV] | 5 CNOT gates |
| D(5, 2) | 16 CNOT gates [1, Table IV] | 9 CNOT gates |
| D(6, 2) | 22 CNOT gates [1, Table IV] | 14 CNOT gates |
| D(6, 3) | 25 CNOT gates [1, Table IV] | 14 CNOT gates |
| D(8, 2) | 27 CNOT gates [3, Fig. 6] | 25 CNOT gates, fidelity above 1 − 10⁻⁷⁷ |
| D(8, 2), 2 × 4 grid | 31 CNOT gates [3, Fig. 7] | 27 CNOT gates, fidelity above 1 − 10⁻⁷⁷ |

**Theorem 1.** D(4, 2) can be prepared exactly with 5 CNOT gates and real single-qubit rotations.

**Theorem 2.** D(5, 2) can be prepared exactly with 9 CNOT gates and real single-qubit rotations.

**Theorem 3.** D(6, 2) and D(6, 3) can each be prepared exactly with 14 CNOT gates and real single-qubit rotations.

**Theorem 4.** There is a circuit with 25 CNOT gates and real single-qubit rotations whose output, for the 40-digit angles listed in `sim/hp_8_2.txt`, has fidelity above 1 − 10⁻⁷⁷ with D(8, 2).

**Theorem 5.** On the 2 × 4 grid with rows 0, 1, 2, 3 and 4, 5, 6, 7 (CNOT gates allowed on the pairs {0, 1}, {1, 2}, {2, 3}, {4, 5}, {5, 6}, {6, 7}, {0, 4}, {1, 5}, {2, 6}, {3, 7} in either direction), there is a circuit with 27 CNOT gates and real single-qubit rotations whose output, for the 40-digit angles listed in `sim/hp_g8_2.txt`, has fidelity above 1 − 10⁻⁷⁷ with D(8, 2).

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

**Theorem 2.** Let a = arccos √(3/5), b = arccos(1/√3) and c = arccos(1/√5). First apply R_y(−3π/2) to qubits 0 and 2, R_y(−a − 2π) to qubit 1, R_y(b) to qubit 3 and R_y(−c − 2π) to qubit 4. Then apply nine CNOT gates, each followed by a rotation on its control and one on its target:

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

**Theorem 3, D(6, 2).** Let a = arccos √(3/67), b = arccos √(8/75), c = arccos √(32/201), d = arccos √(1/3).
First apply R_y(−3π/2) to qubit 0, R_y(b + π) to qubit 1, R_y(−3π/2) to qubit 2, R_y(−2π) to qubit 3, R_y(−π/2) to qubit 4, R_y(−d + 2π) to qubit 5.

| CNOT | Rotation on the control | Rotation on the target |
|---|---|---|
| 0 → 1 | R_y(a − π/2) | R_y(−c − 2π) |
| 0 → 5 | R_y(−2π) | R_y(−2π) |
| 3 → 5 | R_y(−π/2) | R_y(−d − 2π) |
| 2 → 1 | R_y(−3π/2) | R_y(−2π) |
| 4 → 5 | R_y(5π/4) | R_y(−π/4) |
| 3 → 0 | R_y(−3π/2) | R_y(−2π) |
| 1 → 3 | R_y(−π/4) | R_y(7π/4) |
| 0 → 2 | R_y(−5π/4) | R_y(−5π/4) |
| 5 → 0 | R_y(−3π/2) | R_y(−3π/4) |
| 1 → 2 | R_y(−3π/2) | R_y(−2π) |
| 4 → 3 | R_y(−2π) | R_y(−7π/4) |
| 5 → 4 | R_y(3π/4) | R_y(−7π/4) |
| 3 → 5 | R_y(−3π/2) | R_y(−2π) |
| 0 → 4 | R_y(−3π/2) | R_y(−2π) |

**Theorem 3, D(6, 3).** Let a = arccos √(1/16), b = arccos √(5/32), c = arccos √(1/5), d = arccos √(1/4), e = arccos √(1/3), f = arccos √(9/25), g = arccos √(2/5).
First apply R_y(−3π/2) to qubit 0, R_y(−f − π/2) to qubit 1, R_y(−2π) to qubit 2, R_y(−3π/2) to qubit 3, R_y(a − 2π) to qubit 4, R_y(−2π) to qubit 5.

| CNOT | Rotation on the control | Rotation on the target |
|---|---|---|
| 0 → 1 | R_y(−2π) | R_y(−2π) |
| 4 → 1 | R_y(b − π/2) | R_y(−2π) |
| 2 → 0 | R_y(−3π/2) | R_y(−2π) |
| 3 → 4 | R_y(−c − 3π/2) | R_y(−g + 3π/2) |
| 4 → 3 | R_y(d) | R_y(−7π/4) |
| 2 → 4 | R_y(e − π/2) | R_y(e − π) |
| 4 → 2 | R_y(3π/4) | R_y(−π/4) |
| 4 → 0 | R_y(−2π) | R_y(−2π) |
| 1 → 2 | R_y(−2π) | R_y(−2π) |
| 2 → 5 | R_y(−3π/2) | R_y(−2π) |
| 2 → 4 | R_y(−3π/2) | R_y(−3π/2) |
| 1 → 4 | R_y(−2π) | R_y(−2π) |
| 3 → 5 | R_y(−2π) | R_y(−2π) |
| 0 → 3 | R_y(−2π) | R_y(−π) |

In both circuits each CNOT is followed by the two rotations of its row, as above.

**Theorem 4.** The CNOT gates are, in order, 1 → 7, 6 → 7, 1 → 3, 1 → 4, 7 → 6, 5 → 7, 1 → 0, 1 → 2, 1 → 7, 2 → 5, 3 → 4, 6 → 3, 6 → 3, 7 → 0, 0 → 1, 4 → 7, 1 → 5, 4 → 3, 5 → 7, 5 → 7, 7 → 2, 2 → 1, 7 → 2, 6 → 4, 6 → 4. As above, R_y rotations act on all eight qubits first and on the control and target after each CNOT; the 66 angles are listed to 40 digits in `sim/hp_8_2.txt`. Four of them have closed forms: −arccos √(2/3), −2 arccos √(1/3) − 2π, arccos √(1/12) − 2π and −3π/2 (angles 8, 9, 17 and 20 in the file, counted from 0).

**Theorem 5.** The CNOT gates are, in order, 3 → 2, 2 → 1, 2 → 3, 1 → 0, 5 → 1, 1 → 5, 0 → 1, 6 → 5, 6 → 2, 0 → 4, 6 → 7, 3 → 2, 1 → 0, 1 → 5, 4 → 0, 7 → 3, 0 → 1, 7 → 3, 6 → 7, 4 → 5, 6 → 2, 6 → 5, 3 → 7, 0 → 1, 5 → 4, 2 → 6, 5 → 6, all between grid neighbours. The rotations follow the same pattern; the 62 angles are listed to 40 digits in `sim/hp_g8_2.txt`. Five of them have closed forms: −arccos √(3/8) − 2π, arccos √(5/11) − π/2, −arccos √(5/11) − π/2, arccos √(1/5) − 3π/4 and 2π (angles 9, 11, 17, 34 and 56).

## Scope

- **Exact checks.** Theorems 1 to 3 are checked by exact symbolic elimination. Every half-angle cosine and sine is a polynomial in a few algebraic numbers: cos(t/2), sin(t/2), 1/√2 and 1/√3 for Theorem 1, and the half-angle cosines and sines of a, b, c and π/4 together with √2, √3 and √5 for Theorem 2, and in the same way for Theorem 3 with the square roots of the primes that occur. Each amplitude minus its target value reduces to zero modulo relations that hold at these numbers. For Theorem 3 the check shows that the amplitudes off weight k vanish, that all amplitudes of weight k are equal, and that the square of one of them is 1/C(6, k); this fixes the state up to its global sign.
- **Theorems 4 and 5 are numerical certificates.** With the closed-form angles fixed, least-squares refinement with exact derivatives at 80 digits converges quadratically (residual norms 10⁻¹⁶, 10⁻³¹, 10⁻⁶¹, 10⁻⁸¹), and a separate simulation of the listed 40-digit angles at 100 digits gives 1 − fidelity = 1.3 · 10⁻⁷⁸ (Theorem 4) and 9.2 · 10⁻⁷⁹ (Theorem 5); the check of Theorem 5 also confirms that every CNOT acts on a grid pair. This indicates exact solutions nearby; closed forms for the other angles are not given.
- **Not formalized.** No part is in Lean. Minimality is not claimed: the counts are upper bounds.

## Files

- `sim/exact_d42.py`: the exact check of Theorem 1, and a floating-point cross-check (`python exact_d42.py`, needs sympy).
- `sim/exact_d52.py`: the exact check of Theorem 2 (`python exact_d52.py`, needs sympy).
- `sim/certify.py`: closed-form angles and the exact check for a circuit found by `search.py`; `sim/cert_6_2.txt` and `sim/cert_6_3.txt` hold the certified circuits of Theorem 3 (`python certify.py --check cert_6_3.txt` repeats the exact check from a certificate). `sim/tables.py` prints the circuit tables above from a certificate, and `sim/check_tables.py` simulates the printed tables again in floating point (`python tables.py cert_6_3.txt | python check_tables.py 6 3`).
- `sim/hp_cert.py`: the high-precision refinement and the check of Theorem 4 (`python hp_cert.py --check hp_8_2.txt`, needs mpmath), and of Theorem 5 (`python hp_cert.py --check hp_g8_2.txt`). `sim/anneal.py` is the local search over CNOT placements that found the circuits of Theorems 4 and 5 (the grid via `EDGES=0-1,1-2,2-3,4-5,5-6,6-7,0-4,1-5,2-6,3-7`), and `sim/nullgauge.py` and `sim/polish.py` fix its free directions and polish it to double precision before the refinement.
- `sim/search.py`: numerical search over CNOT placements with real rotations and an exact gradient. It found the circuits of Theorems 1 to 3 (`python search.py 4 2 5 6`; for five and six qubits it samples placements, for example `python search.py 5 2 9 4 4000 6` or `python search.py 6 3 14 3 1500 23`).

## Use of AI

The circuits, checks and text were produced with Claude Opus 5.5.

## References

1. H. Wang, B. Tan, J. Cong, G. De Micheli. Quantum state preparation using an exact CNOT synthesis formulation. arXiv:2401.01009.
2. H. Wang, D. B. Tan, J. Cong. Quantum state preparation circuit optimization exploiting don't cares. ICCAD 2024. arXiv:2409.01418.
3. A. Bärtschi, S. Eidenbenz. Short-depth circuits for Dicke state preparation. IEEE International Conference on Quantum Computing and Engineering (QCE), 2022, pp. 87–96. arXiv:2207.09998.
