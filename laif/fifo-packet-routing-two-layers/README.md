# Price of anarchy of FIFO packet routing games on two-layer networks

Posted 2026-11-21.

## Result

| Graph class | Previous best bound | Our bound | Status |
|---|---|---|---|
| Linear multigraphs with two layers, UFR equilibria, makespan | PoA ≤ 2, for every linear multigraph [1] | PoA = 7/5 exactly: 3C ≤ 4·OPT + 1 for every instance and every UFR equilibrium, and an instance with C = 7, OPT = 5 | Lean |

## Model

The packet routing game with FIFO of [1]. A linear multigraph with two layers has nodes s, v₁, d, a set of parallel
edges from s to v₁ with integer transit times a_e ≥ 1, and a set of parallel edges from v₁ to d with integer transit
times b_f ≥ 1. All n unit packets (players) start at s at time 0. Each edge lets at most one packet leave per time
step. A packet that reaches the tail of an edge at time t leaves at max(t, previous departure + 1) and reaches the head
after the transit time. Packets are served in the order of their arrival at the tail, ties broken by the smaller
player index.

A state assigns a path to every player. It is a uniformly fastest route (UFR) equilibrium if no player reaches a node
of her path earlier by a unilateral change of path. C(S) is the makespan of state S, OPT the minimum makespan over
all states, and the price of anarchy is the largest ratio C(S)/OPT over all UFR equilibria S. In [1] it is proved
that the price of anarchy is at most 2 on every linear multigraph, and that the price of stability tends to at least
e/(e − 1) on a family with a growing number of layers.

## Theorem

Let a₁ and b₁ be the shortest transit times of the two layers. For every two-layer instance and every UFR equilibrium S,

  OPT ≥ ⌊(3 C(S) + a₁ + b₁)/4⌋,  hence 3 C(S) ≤ 4 OPT + 1 and C(S) ≤ (7/5) OPT.

All three bounds are attained by the instance a = (1, 1, 1, 1, 1), b = (1, 1, 4, 4, 4), n = 11: it has a UFR
equilibrium with C = 7, and OPT = 5. So the price of anarchy of two-layer instances is exactly 7/5.

The fluid analogue of this game, equilibrium flows over time, has makespan ratio at most 4/3 on two-layer networks of equal
capacities [2]. In the packet model the integrality of packets adds exactly the +1 in 3C ≤ 4·OPT + 1.

## Proof sketch

1. **Optimum.** With a₍p₎ and b₍p₎ the sorted transit times and K the smaller layer size, at most
   F(T) = Σ_{p ≤ K} (T + 1 − a₍p₎ − b₍p₎)⁺ packets arrive by time T, and F(T) is attained by sending packets along the
   disjoint paths (a₍p₎, b₍p₎). The upper bound is a cut at an integer time y between the layers, with an explicit
   minimizing y. Hence OPT is the least T with F(T) ≥ n.
2. **Equilibria.** In a UFR equilibrium each player reaches v₁ as early as the players before her allow, so the
   arrival times at v₁ are the n smallest values of the multiset {a_e + r : r ≥ 0}, and in layer 2 every player picks
   an edge of minimum level, where the level of an edge is its transit time plus its current queue. The levels of the
   backlogged edges differ by at most 1, so the latency of a player is a function μ(B) of the total backlog B.
3. **Worst case.** The backlog evolves as B(t + 1) ≤ g(B(t) + c_t), with c_t the number of layer-1 edges of transit
   time at most t and g nondecreasing, so a worst-case backlog process B̂ dominates every equilibrium, and the makespan
   is at most Ĉ = t* + μ(B̂(t*) + R), with t* the arrival time of the last player at v₁.
4. **Potential.** For every k, the potential Ψ(B) = Σ_{p ≤ k}(ν(B) − b₍p₎)⁺, with ν the inverse of
   Φ(y) = Σ_f (y − b_f)⁺, grows in one step by at most (c − k)⁺ + (k/4)(1 + Δν). The proof is two applications of
   (x − 2m)² ≥ 0, the discrete form of the bound m(c − m) ≤ c²/4.
5. **Summation.** Telescoping over the steps and comparing with the partial sums of F gives
   Σ_{p ≤ k}(M − a₍p₎ − b₍p₎) ≤ n − 1 for M = (3Ĉ + a₁ + b₁)/4 and every k, so OPT ≥ ⌊M⌋ by step 1.
6. **Ratio.** As a₁ + b₁ ≥ 2, this gives 4·OPT ≥ 3C − 1, so C/OPT ≤ 7/5 for OPT ≥ 5. For OPT = 2 every
   player reaches v₁ at time 1 on an edge of transit time 1, and the latency in layer 2 is 1, so C = 2. OPT = 3 and 4
   give C ≤ 4 and C ≤ 5.

Remark: 3C ≤ 4·OPT holds whenever C ≢ 3 (mod 4) or a₁ + b₁ ≥ 3. The family a = 1^(2j+1), b = 1^j (2j)^(j+1),
n = 4j² − 2j − 1 has OPT = 3j − 1, and for j ≤ 7 a UFR equilibrium with C = 4j − 1 = (4·OPT + 1)/3 was found numerically.

## Checks

- **Lean** (`lean/`, Lean v4.36.0-rc1, Mathlib d875a8de5222, only the standard axioms, output in `lean/axioms.txt`).
  The model is stated once, in `PacketTwoLayer/Instance.lean`: the loading of a two-layer state, the UFR condition
  (every player, every alternative path, arrival at v₁ and at d) and the makespan, as computable functions. All
  theorems below are about these functions.
  - `Instance.lean`: the instance above has a UFR equilibrium of makespan 7 and a state of makespan 5, by `decide`
    (`poa_ge_seven_fifths`).
  - `Loading.lean`: arrival times under the FIFO rule when the processing order is the index order.
  - `Opt.lean`: the cut bound of step 1 for every state (`opt_cut`).
  - `Equilibrium.lean`: every UFR equilibrium is a sequential best response in both layers (`eqm_of_UFR`).
  - `Backlog.lean`: levels, the backlog invariant and the domination by the worst-case backlog (steps 2 and 3).
  - `Potential.lean`: the one-step potential inequality and its sum over the loading (steps 4 and 5).
  - `Main.lean`: `opt_ge`, OPT ≥ ⌊(3C + a₁ + b₁)/4⌋ for every UFR equilibrium and every state with the same number
    of players, and `three_mul_makespan_le`, 3C ≤ 4·OPT + 1 when all transit times are at least 1.
  - `Tight.lean`: every state of the instance above has makespan at least 5, so OPT = 5 and the ratio 7/5 is attained
    (`poa_eq_seven_fifths`).
- **Scripts** (`sim/`): `pr.py` is the exact simulator (loading, UFR test, worst equilibrium over all tie choices,
  optimum by successive shortest paths and by a time-expanded maximum flow). `proof2_check.py` tests every step of the
  proof with asserts in exact arithmetic: the cut formula for OPT on 300 instances, the structure of equilibria by
  brute force over all states of 40 small instances, the one-step inequality on 4000 random cases, the level and
  backlog lemmas and the theorem on every tie choice of 250 small instances and on 1500 random instances with
  n ≤ 100, and the family above for j = 2 to 7.
- **Not formalized:** the family of the remark, which is checked numerically for j ≤ 7.

## Files

- `lean/`: Lean 4 project with Mathlib (`lake exe cache get`, then `lake build`).
- `sim/pr.py`, `sim/proof2_check.py`: run with `python proof2_check.py [seed]` (Python 3, networkx).

## References

1. D. Schmand, T. Schürenberg, M. Strehler. On the price of anarchy in packet routing games with FIFO. arXiv:2502.04811, 2025.
2. J. Correa, A. Cristi, T. Oosterwijk. On the price of anarchy for flows over time. Mathematics of Operations Research, 2022.

## Use of AI

Claude Opus 5.5 was used to develop the proofs, write the code and the Lean files, and draft this text.
