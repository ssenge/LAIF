# Price of stability of Shapley network design games with three players

Posted 2026-11-21.

## Result

| Problem | Previous best bound | Our bound | Status |
|---|---|---|---|
| Price of stability of undirected Shapley network design games with 3 players | 1769/1126 ≈ 1.57105 ≤ PoS(3) ≤ 286/175 ≈ 1.63429 [1, 2] | PoS(3) ≥ 1451/922 ≈ 1.57375 | Claim, computer-assisted, exact rational arithmetic |

## Model

The game of [1]. An undirected graph has positive edge costs c_e. Each of the k players has a source s_i and a
target t_i (terminals may coincide) and picks a simple s_i–t_i path. The cost of an edge is shared equally among the
players that use it. A profile is a Nash equilibrium if no player has a strictly cheaper path, given the others. The
price of stability of a game is the cost of its cheapest Nash equilibrium divided by the minimum cost of a profile,
and PoS(k) is the supremum over all games with k players.

## Theorem

PoS(3) ≥ 1451/922.

The instance has the topology of [1, Fig. 2(b)]: vertices T = t₁ = t₃, t₂, s₁, s₂, s₃ and seven edges with costs
w₀ + ε·d,

| edge | w₀ | d |
|---|---|---|
| T–t₂ | 260 | +48 |
| T–s₁ | 450 | −768 |
| T–s₃ | 545 | −2098 |
| t₂–s₂ | 456 | −852 |
| t₂–s₃ | 342 | +744 |
| s₁–s₂ | 92 | +556 |
| s₂–s₃ | 228 | −1348 |

For ε = 10⁻⁴, 10⁻⁵, 10⁻⁶ and 10⁻⁹, enumeration of every profile in exact arithmetic gives the minimum cost 922 (the
tree T–t₂–s₃–s₂–s₁, on which d sums to 0) and exactly one Nash equilibrium, the three direct edges s₁–T, s₂–t₂ and
s₃–T, of cost 1451 − 3718ε. So the price of stability is (1451 − 3718ε)/922, which tends to 1451/922 as ε → 0. At
ε = 0 cheaper profiles become equilibria by ties, so the bound is a supremum.

A single instance with integer costs (ε = 10⁻⁴, costs times 10⁴): T–t₂ 2600048, T–s₁ 4499232, T–s₃ 5447902,
t₂–s₂ 4559148, t₂–s₃ 3420744, s₁–s₂ 920556, s₂–s₃ 2278652. It has a unique Nash equilibrium and price of stability
exactly 7253141/4610000 ≈ 1.57335 > 1769/1126.

The upper bound 286/175 of [2] is tight for the price of stability restricted to potential minimizers [1, Theorem 5],
so the remaining gap concerns equilibria that do not minimize the potential.

## Checks

- `sim/game.py`: exact game, all simple paths of each player, all profiles, Nash test against every simple path in
  `fractions.Fraction`. It reproduces the instance of [1, Fig. 2(b)] with unique equilibrium cost 1769 and minimum
  cost 1126.
- `sim/cert_1451_922.py`: the asserts for the theorem above, for the four values of ε and the integer instance.
  Run with `python cert_1451_922.py` (Python 3, numpy).
- **Not formalized:** the enumeration is not in Lean.

## References

1. Y. Disser, A. E. Feldmann, M. Klimm, M. Mihalák. Improving the H_k-bound on the price of stability in undirected Shapley network design games. Theoretical Computer Science 562, 2015. arXiv:1211.2090.
2. V. Bilò, R. Bove. Bounds on the price of stability of undirected network design games with three players. Journal of Interconnection Networks 12, 2011.

## Use of AI

Claude Opus 5.5 was used to find the instance, write the code and draft this text.
