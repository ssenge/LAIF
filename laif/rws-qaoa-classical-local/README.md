# A classical radius-6 rule on the warm start of regularized warm-started QAOA for Max-Cut

_18 November 2026, updated 19 November 2026_

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

## Exact solve on the same warm start

The algorithm X computes the warm start, fixes the polarized spins to their values and maximizes the cut over the free spins exactly, by variable elimination on each connected component of the free spins (the components interact only through fixed spins). By the lemma, on every graph and its warm start, the expected cut of warm-started QAOA at any depth is at most the cut of X, and X attains this bound.

With the warm start by coordinate ascent (best of 100 starts), X at each N of [1, Fig. 3A]:

| N | Graphs | X, mean | X, minimum | Radius-6 rule, mean | RWS-QAOA, p = 6, [1, Fig. 3A] | Graphs with X below that value | Largest free component | Time of X (s) |
|---|---|---|---|---|---|---|---|---|
| 1 000 | 6 | 0.9188 | 0.9147 | 0.9186 | 0.9169 | 1 | 197 | 0.1 |
| 2 000 | 10 | 0.9193 | 0.9177 | 0.9193 | 0.9171 | 0 | 300 | 0.1 |
| 3 000 | 6 | 0.9192 | 0.9176 | 0.9191 | 0.9177 | 1 | 516 | 0.9 |
| 4 000 | 6 | 0.9189 | 0.9183 | 0.9189 | 0.9177 | 0 | 573 | 0.4 |
| 5 000 | 6 | 0.9187 | 0.9176 | 0.9186 | 0.9177 | 1 | 575 | 0.3 |
| 6 000 | 6 | 0.9187 | 0.9182 | 0.9186 | 0.9161 | 0 | 503 | 0.3 |
| 7 000 | 6 | 0.9183 | 0.9177 | 0.9182 | 0.9171 | 0 | 600 | 0.5 |
| 8 000 | 6 | 0.9183 | 0.9180 | 0.9182 | 0.9162 | 0 | 916 | 0.5 |
| 9 000 | 6 | 0.9181 | 0.9176 | 0.9180 | 0.9158 | 0 | 1 255 | 1.6 |
| 10 000 | 6 | 0.9176 | 0.9169 | 0.9175 | 0.9169 | 0 | 1 474 | 2.0 |

The values of [1] are read from Fig. 3A to about ±0.0003 and are averages over six graphs per N; the text of [1] gives 0.917 at N = 2000 and 0.9167 at N = 10 000. The comparison is therefore between averages, and per graph against an average. About 35% of the spins are free. The elimination width is 3 to 5, so the time of X is small although the free components are long (diameter up to 213).

With a warm start by Adam (learning rate 0.01, 30 000 steps, θᵢ uniform in [0, π), best of 100 starts), with the spins of min(pᵢ, 1 − pᵢ) < 10⁻⁶ fixed, X gives 0.92000 at N = 2000 (graph seed 4) and 0.91807 at N = 10 000 (seed 1). These fixed spins are polarized only up to the tolerance, and the bound holds up to the leakage term below: 8.4 · 10⁻⁵ and 7.9 · 10⁻⁵ of the edges.

**Claim (leakage bound).** Let the fixed spins have δᵢ = 2 arcsin √min(pᵢ, 1 − pᵢ). The expected cut of warm-started QAOA of depth p with mixer angles β₁, …, β_p is at most the maximum cut with the fixed spins at their rounded values plus c_p Σᵢ Dᵢ δᵢ², where Dᵢ is the number of edges whose radius-p light cone contains i, B = Σₜ |βₜ| and c_p = (B + 2(1/2 + B)²)/2. For the schedule of [1, Table I] at p = 6, c₆ = 9.37. Sketch: conjugation by Zᵢ shows that each edge term is even in the angle of qubit i, for any values of the other angles; its second derivative in that angle is bounded by B + 2(1/2 + B)²; and an edge term depends only on the qubits in its light cone. With coordinate ascent every fixed spin is exactly polarized, the term vanishes and the bound is exact.

## Time to the target of [1] at N = 3000 and N = 10 000

In the runtime comparison of [1, Sec. II E], the target for N ≤ 10 000 is the RWS-QAOA cut fraction of Fig. 3A. The quantum runtime there is a per-shot estimate for fault-tolerant hardware and does not include the warm start. With the warm start given, the radius-6 rule reaches the target in:

| N | Target | Radius-6 rule after the warm start | RWS-QAOA, one shot, estimate of [1, Fig. 3C] |
|---|---|---|---|
| 3 000 | 0.917 (4127 of 4500 edges) | 0.2 ms, 25 of 25 runs | about 0.2 s |
| 10 000 | 0.9167 (13 751 of 15 000 edges) | 0.6 ms, 6 of 6 runs | about 0.6 s |

At N = 3000 the value of Fig. 3A is about 0.9177 (4130 edges); the rule after the warm start reaches it on 23 of 25 runs.

From a random start on one core (medians, range in brackets; 5 graphs with 5 runs each at N = 3000, 3 graphs with 2 runs each at N = 10 000; every run reached the target):

| N | Warm start, best of 100 | One warm start and the rule, repeated until the target | Annealing | MQLib, BURER2002 [2] |
|---|---|---|---|---|
| 3 000 | 1.0 s (0.6 to 2.1) | 0.07 s (0.007 to 0.35) | 0.5 s (0.24 to 1.5) | 0.54 s (0.10 to 2.0) |
| 10 000 | 11 s (9.4 to 12.5) | 1.0 s (0.06 to 2.4) | 2.0 s (1.8 to 4.1) | 2.7 s (1.5 to 3.0) |

Annealing is timed as in the next section (the run of the doubling ladder that first reaches the target). For MQLib the time is that of the first entry of its history at or above the target. In [1, Fig. 3C], a parallel Burer-Monteiro solver on 96 virtual CPUs reaches the target in about 0.2 s (N = 3000) and 1 s (N = 10 000).

## Without restrictions

Simulated annealing from a uniformly random state on one laptop core (T from 1.5 to 0.05; the smallest sweep count of a doubling ladder that reaches the target) reaches the cut fraction 0.9167 in:

| N | 10³ | 3 · 10³ | 10⁴ | 3 · 10⁴ | 10⁵ |
|---|---|---|---|---|---|
| Time (s), three graphs | 0.2 to 0.4 | 0.2 to 0.3 | 0.4 to 0.7 | 3.9 to 4.8 | 8.3 to 16.3 |

At N = 100 000, [1, Fig. 3C] gives about 5 s for the estimated fault-tolerant runtime of RWS-QAOA and about 50 s for a parallel Burer-Monteiro solver on 96 virtual CPUs to reach the same target.

## Scope

- **Instances.** The graphs of [1] are not published. The graphs here are networkx random 3-regular graphs with seeds 0 to 9.
- **Warm start.** In [1], the warm start is computed by gradient descent or Adam for a fixed number of steps. Here it is solved to a fixed point. The expected cut of the product state agrees with the RWS curve of [1, Fig. 3A] to about 0.0015. The ceiling is computed on the warm starts here. With coordinate ascent the fixed spins are exactly polarized; with Adam the ceiling holds up to the leakage bound.
- **Not simulated.** RWS-QAOA itself is not simulated here. On these warm starts, the depth-6 light cones of the free qubits reach 87 qubits. The comparison uses the values reported in [1].
- **Runtimes.** The times are wall-clock times on one core of an Apple M4 Pro laptop (Python with numba; MQLib compiled with clang -O2), measured while other jobs ran on the same machine, so they are upper bounds. The quantum runtimes are estimates of [1], read from Fig. 3C, with no measurement here.
- **Not formalized.** The identification of the circuit with the layers of the Lean lemma, and the leakage bound (Claim).

## Files

- `sim/rws_local.py`: the graphs, the warm start by coordinate ascent, the cut and the flip rule.
- `sim/frozen_ceiling.py`: the exact maximum cut with polarized spins fixed. It uses `hubo.py` of [heavy-hex-hubo-exact-sampling](../heavy-hex-hubo-exact-sampling/).
- `sim/test_frozen.py`: a statevector check of the lemma on 20 random cases (12 qubits, depths 1 to 6, random angles): polarized qubits never flip, and the expected cut stays below the ceiling.
- `lean/`: the Lean files. Build with `lake exe cache get` and then `lake build`; `lake env lean Axioms.lean` prints the axioms.
- `sim/rws_main.py`: the table (`data/rws_2000.jsonl`, `data/rws_10000.jsonl`).
- `sim/ttt.py`: the times to the target and the N = 100 000 values (`data/ttt.jsonl`).
- `sim/c2_x.py`: X, the free components, the elimination width and the leakage bound (`data/x_ca.jsonl`, `data/x_adam.jsonl`); `python -I c2_x.py test` checks X against brute force at n = 20.
- `sim/rws_adam.py`: the warm start by Adam.
- `sim/ttt3000.py`: the times to the target of [1] (`data/ttt3000.jsonl`, `data/ttt10000.jsonl`). It calls an MQLib binary [2] given by its path.

## References

1. Z. He, A. Apte, B. Augustino, A. Babakhani, A. Khan, S. Omanakuttan, R. Shaydulin. Regularized warm-started quantum approximate optimization and conditions for surpassing classical solvers on the Max-Cut problem. arXiv:2603.10191.
2. I. Dunning, S. Gupta, J. Silberholz. What works best when? A systematic evaluation of heuristics for Max-Cut and QUBO. INFORMS Journal on Computing 30(3), 2018. Code: https://github.com/MQLib/MQLib.
