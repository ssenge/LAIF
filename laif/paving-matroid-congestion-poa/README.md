# Price of anarchy of symmetric paving matroid congestion games

Posted 2026-11-22.

## Result

| Problem | Previous best bound | Our bound | Status |
|---|---|---|---|
| Price of anarchy of symmetric paving matroid congestion games with affine delays | 13/9 ≈ 1.4444 ≤ PoA ≤ 17/7 ≈ 2.4286 [1] | PoA ≥ 16/11 ≈ 1.4545, by a rank-2 instance with 5 resources and 3 players | Lean |
| The same, restricted to rank 2 and 3 players | at most 17/7 ≈ 2.4286 [1] | Exactly 16/11 ≈ 1.4545 | Claim (exact certificates for every case); Lean for steps 1 and 2 of the proof |

## Model

The model of [1]. A matroid on a finite set R of resources has rank r. It is paving if every circuit has r or r + 1
elements. Each of the N players picks a basis, and all players have the same matroid (symmetric game). Resource e has
the delay d_e(x) = a_e x + b_e with a_e, b_e ≥ 0, where x is the number of players using e. A player pays the sum of
the delays of the resources in its basis, and the social cost of a profile is the sum of all players' costs,
Σ_e x_e d_e(x_e). A profile is a pure equilibrium if no player lowers its cost by switching alone to another basis.
The price of anarchy is the largest ratio between the cost of a pure equilibrium and the minimum social cost,
taken over all games of the class.

## Theorem 1

The price of anarchy of symmetric paving matroid congestion games with affine delays is at least 16/11.

Resources 0, ..., 4 form the parallel classes {0, 1}, {2, 3} and {4}. The bases are the pairs of resources from
different classes, so the matroid has rank 2. It has no loops, hence every circuit has 2 elements (a parallel pair)
or 3 elements, and the matroid is paving. Three players, with delays

| resource | 0 | 1 | 2 | 3 | 4 |
|---|---|---|---|---|---|
| a_e | 2 | 2 | 1 | 0 | 2 |
| b_e | 0 | 0 | 0 | 2 | 0 |

The profile {0, 2}, {0, 2}, {1, 4} is a pure equilibrium of cost 16. The two players on {0, 2} pay 4 + 2 = 6
each, and every other basis would cost them at least 6; the player on {1, 4} pays 2 + 2 = 4, and every other basis
would cost at least 4. The profile {0, 2}, {1, 3}, {3, 4} costs 11, and no profile costs less. The same matroid is
the graphic matroid of a triangle with two of its edges doubled.

## Theorem 2

Every symmetric rank-2 paving matroid congestion game with 3 players and affine delays has price of anarchy at
most 16/11. With the instance above, the value for this class is exactly 16/11.

For rank 2, paving means loopless: the resources split into parallel classes, and the bases are the pairs of
resources from different classes. Fix an equilibrium F and an optimum H.

1. **Deletion.** Remove every resource that neither F nor H uses. The rest is again a loopless rank-2 matroid, F
   stays an equilibrium (its conditions are a subset of the old ones), and H stays optimal. So at most 12 resources
   remain.
2. **Merging classes.** If no basis of F or H meets both of two classes, merging the two classes keeps F and H as
   profiles and only removes bases, so the equilibrium conditions only become weaker. It suffices to treat
   partitions in which every two classes are joined by a basis of F or H, so there are at most 4 classes.
3. **Certificates.** What remains is a finite list of types, each given by the six bases of F and H and the
   partition: 4,267,104 types before removing symmetric copies. For a fixed type, the equilibrium conditions and
   both costs are linear in the delay coefficients (a, b), so the largest ratio cost(F)/cost(H) is a linear
   program. For every type, an exact rational dual solution shows that this value is at most 16/11. The bound is
   attained by 768 of the types.

## Checks

- `sim/paving.py`: exact rational check. It tests the basis exchange axiom, enumerates all circuits to test that the
  matroid is paving, checks every unilateral deviation of every player, and finds the minimum social cost by
  enumerating all profiles. For a fixed equilibrium profile and comparison profile, the equilibrium conditions are linear in
  the delay coefficients, and `lp_pair` maximizes the equilibrium cost by a linear program; this is how the delays
  above were found. Run with `python paving.py` (Python 3, numpy, scipy).
- **Lean** (`lean/`, Lean v4.36.0-rc1, only the standard axioms, output in `lean/axioms.txt`; `PavingCert` uses the
  core library only, `PavingReduction` uses Mathlib d875a8de5222):
  `PavingCert/Basic.lean` defines the bases, the delays, the loads, the social cost and the equilibrium condition against
  every basis, all in natural numbers. Proved by `decide`: `bases_norm` and `exchange`, the basis exchange axiom
  (so the bases are those of a matroid); `rank_two`, every basis has 2 elements; `paving`, every resource lies in a
  basis, so there are no loops and every circuit has at least 2 elements, which for rank 2 is the definition of
  paving; `ne_isNE`, the profile above is a pure equilibrium; `ne_cost`, its cost is 16;
  `opt_cost` and `opt_ge`, the minimum social cost over all 512 ordered profiles is 11; `ratio_gt`, 16/11 > 13/9.
- `PavingReduction/Basic.lean` states the game for every loopless rank-2 matroid, given by its parallel classes,
  with N players, affine delays with rational coefficients, the social cost and the equilibrium condition against
  every basis. `reduction` proves steps 1 and 2 of Theorem 2: if cost(F) ≤ r cost(H) holds for every equilibrium F
  and every profile H of every game in which each resource is used by F or H and each two classes are joined by a
  basis of F or H, then it holds for every game. `card_le` (at most 4N resources), `choose_classes_le` (C(k, 2) ≤ 2N
  for k classes) and `classes_le_four` (k ≤ 4 for N = 3) give the sizes of the remaining games.
  `PavingReduction/Instance.lean`: the instance of Theorem 1 is an equilibrium of cost 16 in this model, against a
  profile of cost 11, so no bound below 16/11 holds for three players (`not_bound`).
- `sim/types2.py` lists the types of Theorem 2. It introduces resources and classes in their order of first
  appearance, and the bases of F and of H in sorted order. `sim/certN.py` solves the dual linear program of each
  type, rounds the dual solution to rationals, and checks in exact arithmetic that the dual is feasible and its
  value is at most the target. When rounding loses feasibility, it solves exactly on the support. Run with
  `python certN.py 3 16/11 fails.jsonl` (about 50 minutes on one core, numpy and scipy). The output ends with
  `fails 0` and `worst certified 16/11`.

Not formalized: step 3 of Theorem 2. The certificates and the completeness of the list of types are checked by
script.

## References

1. B. Hao, C. Michini. Price of anarchy in paving matroid congestion games. ACM Transactions on Economics and Computation, 2025. Preprint: https://optimization-online.org/?p=24681.

## Use of AI

Claude Opus 5.5 was used to find the instance, write the code and draft this text.
