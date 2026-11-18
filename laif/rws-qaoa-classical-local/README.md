# A classical radius-6 rule on the warm start of regularized warm-started QAOA for Max-Cut

_18 November 2026_

In [1], regularized warm-started QAOA (RWS-QAOA) is applied to Max-Cut on random 3-regular graphs. The warm start maximizes, over a product state with Pr[x_i = 1] = p_i,

L(p) = E[cut] + 4λ Σᵢ pᵢ(1 − pᵢ),  λ = 0.6,

over p in the unit cube, best of 100 random starts [1, Eq. (11)]. A depth-6 QAOA with fixed angles [1, Table I] then acts on this state, with the mixer of qubit i chosen so that its initial state is an eigenstate. By tensor-network contraction, [1] reports an average expected cut fraction of 0.917 at N = 2000 and 0.9167 at N = 10 000. Under the stated matched restrictions (no local-search post-processing and no iterative refinement), this is above the classical heuristics compared there; for example, restricted Burer-Monteiro reaches 0.909 at N = 2000.

A depth-p QAOA is a local algorithm: the expected value on an edge depends only on the radius-p neighbourhood of the edge. The matched classical competitor is therefore a classical rule of radius at most 6 applied to the same warm start.

## Result

**Lemma (frozen qubits).** If pᵢ ∈ {0, 1}, qubit i starts in a computational basis state, its mixer term is ±Zᵢ, and the cost is diagonal. Every layer therefore maps (basis state of i) ⊗ (rest) to the same basis state of i times a new rest. Hence the expected cut of the warm-started QAOA at any depth is at most the maximum cut with these spins fixed to their warm-start values.

Lean (`lean/FrozenQubit/Basic.lean`, standard axioms only, `lean/axioms.txt`) proves the lemma for amplitude vectors on the computational basis of n qubits. The layers may be diagonal matrices, single-qubit matrices on unpolarized qubits, and diagonal single-qubit matrices. From a product state in which every qubit of a set F is a basis state, any product of such layers gives:

- `frozen`: a state that vanishes on every basis state disagreeing with the warm start on F;
- `expected_le_ceiling`: if the state is normalized, an expected objective at most any bound on the objective over the basis states that agree with the warm start on F.

The identification of the circuit with these layers is not formalized: the cost unitary is diagonal, and the mixer of a polarized qubit is exp(∓iβZ).

The maximum cut with the polarized spins fixed is computed exactly by variable elimination on the free spins; the elimination width is 3 to 5 here. The classical rule rounds the warm start, sᵢ = sign(1 − 2pᵢ). It then applies three rounds of parallel improving flips. In each round, every vertex whose flip increases the cut, and whose random priority is the largest among such vertices within distance 1, flips. One round reads the radius-2 neighbourhood, so three rounds have radius 6.

The warm start is computed by coordinate ascent to a fixed point (L is concave in each pᵢ), best of 100 random starts. About 65% of the spins end fully polarized. Cut fractions, averaged over random 3-regular graphs:

| N | Graphs | Product state, expected cut (warm start of [1]: Fig. 3A) | Rounded warm start | Radius-6 rule (minimum) | Ceiling for warm-started QAOA at any depth | RWS-QAOA, p = 6, in [1] |
|---|---|---|---|---|---|---|
| 2 000 | 10 | 0.8675 (about 0.866) | 0.9157 | **0.9193** (0.9177) | 0.9193 | 0.917 |
| 10 000 | 6 | 0.8643 (about 0.863) | 0.9135 | **0.9175** (0.9168) | 0.9176 | 0.9167 |

On every graph, the radius-6 rule is at or above the depth-6 values reported in [1]. On the warm starts here, the rule lies within 10⁻⁴ of the frozen-qubit ceiling, so a warm-started QAOA of any depth on the same warm start can exceed it by at most that much. Most of the gain comes from the first round (radius 2).

At N = 100 000 (three graphs), the radius-6 rule gives 0.91645, 0.9167 and 0.91677, against the target 0.9167 that [1] holds fixed for N > 10 000.

## Without restrictions

Simulated annealing from a uniformly random state on one laptop core (T from 1.5 to 0.05; the smallest sweep count of a doubling ladder that reaches the target) reaches the cut fraction 0.9167 in:

| N | 10³ | 3 · 10³ | 10⁴ | 3 · 10⁴ | 10⁵ |
|---|---|---|---|---|---|
| Time (s), three graphs | 0.2 to 0.4 | 0.2 to 0.3 | 0.4 to 0.7 | 3.9 to 4.8 | 8.3 to 16.3 |

At N = 100 000, [1, Fig. 3C] gives about 5 s for the estimated fault-tolerant runtime of RWS-QAOA and about 50 s for a parallel Burer-Monteiro solver on 96 virtual CPUs to reach the same target.

## Scope

- **Instances.** The graphs of [1] are not published. The graphs here are networkx random 3-regular graphs with seeds 0 to 9.
- **Warm start.** In [1], the warm start is computed by gradient descent or Adam for a fixed number of steps. Here it is solved to a fixed point. The expected cut of the product state agrees with the RWS curve of [1, Fig. 3A] to about 0.0015. The ceiling is computed on the warm starts here; for spins that are polarized only up to a numerical tolerance, it holds up to a correction of the order of that tolerance.
- **Not simulated.** RWS-QAOA itself is not simulated here. On these warm starts, the depth-6 light cones of the free qubits reach 87 qubits. The comparison uses the values reported in [1].
- **Runtimes.** The times are wall-clock times on one core with numba. The quantum runtimes are estimates from [1], with no measurement here.

## Files

- `sim/rws_local.py`: the graphs, the warm start by coordinate ascent, the cut and the flip rule.
- `sim/frozen_ceiling.py`: the exact maximum cut with polarized spins fixed. It uses `hubo.py` of [heavy-hex-hubo-exact-sampling](../heavy-hex-hubo-exact-sampling/).
- `sim/test_frozen.py`: a statevector check of the lemma on 20 random cases (12 qubits, depths 1 to 6, random angles): polarized qubits never flip, and the expected cut stays below the ceiling.
- `lean/`: the Lean files. Build with `lake exe cache get` and then `lake build`; `lake env lean Axioms.lean` prints the axioms.
- `sim/rws_main.py`: the table (`data/rws_2000.jsonl`, `data/rws_10000.jsonl`).
- `sim/ttt.py`: the times to the target and the N = 100 000 values (`data/ttt.jsonl`).

## References

1. Z. He, A. Apte, B. Augustino, A. Babakhani, A. Khan, S. Omanakuttan, R. Shaydulin. Regularized warm-started quantum approximate optimization and conditions for surpassing classical solvers on the Max-Cut problem. arXiv:2603.10191.
