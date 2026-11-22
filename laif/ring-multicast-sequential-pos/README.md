# Myopic sequential price of stability of the multicast game on a ring

Posted 2026-11-22.

## Result

| Problem | Previous best bound | Our bound | Status |
|---|---|---|---|
| Myopic sequential price of stability of the multicast network design game on a ring, equal cost sharing | 4/3 ≤ PoS ≤ 26/19 ≈ 1.3684 [1], conjectured 4/3 [1, Conj. 5.5] | Exactly 4/3: one of two fixed arrival orders always ends within 4/3 of the optimum, with ties broken in the worst way | Claim |

The lower bound 4/3 is the instance of [1, Fig. 3].

## Model

The model of [1]. A ring consists of a target t and sources 0, ..., n − 1, one player per source, with edge costs
a_0, ..., a_n ≥ 0 counter-clockwise from t, so that player i sits between edge i and edge i + 1. Player i has two
paths to t: left (edges 0, ..., i) or right (edges i + 1, ..., n). The cost of each used edge is shared equally among
its users. In myopic sequential play, the players arrive one by one in an order π, and each picks a cheapest path in
the game of the players present so far, which never changes afterwards. The network cost is the sum of the costs of
the used edges. The optimum uses every edge except one of maximum cost a_o, so OPT = T − a_o with T = Σ a_k. The
myopic sequential price of stability is the supremum, over all instances, of the cost reached by the best order,
divided by OPT.

## Theorem

Orient the ring so that the edges after o cost at most as much in total as the edges before o, and let
A = (n − 1, ..., o, 0, 1, ..., o − 1) and B = (n − 1, n − 2, ..., 0). For every instance, the network reached by A
or the one reached by B costs at most (4/3) OPT, for every way of breaking ties. Hence the myopic sequential price
of stability on rings is exactly 4/3.

Order A is the order of [1, Thm 5.4].

## Proof sketch

Normalize OPT = 1 and write s = a_o.

1. **Structure of the two orders.** Players o, ..., n − 1 go right in both orders. In A, let p be the first of
   0, 1, ..., o − 1 to go right; every later player of that range also goes right, so edge p stays unused and
   cost_A ≤ T − a_p (if there is no such p, cost_A = OPT). In B, let q be the first of o − 1, ..., 0 to go left (q = −1
   if none); every later player also goes left, so edge q + 1 stays unused and cost_B ≤ T − a_{q+1}. In both
   arguments the later players' choices are strict, so ties do not matter. It remains to show
   z = min(s − a_p, s − a_{q+1}) ≤ 1/3.
2. **Best-response conditions.** The choices of p (and of p − 1) in A and of q and of the players between q and o in B
   give linear inequalities in the edge costs, together with a_k ≤ s.
3. **Relaxations free of o and n.** All mass after p except a_o is bounded by Q = 1 − Σ_{k≤p} a_k, and every
   coefficient is weakened in the safe direction. The cases are split by d = p − q. For d ≥ 4 only the four edges
   p, p − 1, p − 2, p − 3 are kept, and the remaining mass to their left is merged into one variable. That gives a
   single linear program that does not depend on d.
4. **Certificates.** Each case is a small linear program max z, and an exact rational dual solution bounds it:

| Case | Bound on z |
|---|---|
| q ≥ p | 1/5 |
| q + 1 = p | 1/3 |
| d = 2 | 5/17 (1/3 if q = −1) |
| d = 3 | 110/333 |
| d ≥ 4 | 2792/8461 |

All bounds are at most 1/3.

## Checks

- `sim/proof_certs.py` builds every case's linear program from the relaxed inequalities and verifies its dual
  certificate in exact rational arithmetic.
- `sim/ring.py` is an exact simulator of myopic sequential play. It checks every tie choice and returns the worst
  outcome of an order.
- `sim/checkrelax.py` plays A and B exactly on random instances with up to 31 edges. On each instance it reads off p
  and q, maps the instance to the variables of its case, and asserts every relaxed inequality.
- `sim/crosscheck.py` asserts that the better of A and B is within 4/3 of OPT on random instances with up to 41 edges.

Run with `python proof_certs.py`, `python checkrelax.py 2000` and `python crosscheck.py 2000` (Python 3, standard
library only).

Not formalized: the structure lemma and the relaxation steps are a written proof. The certificates are checked by
script.

## References

1. A. Mamageishvili, M. Mihalák. Multicast network design game on a ring. arXiv:1507.04222, 2015.

## Use of AI

Claude Opus 5.5 was used to find the proof and the certificates, write the code and draft this text.
