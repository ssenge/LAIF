# Classical baseline for quantum-enhanced Markov chain Monte Carlo on maximum independent set

_18 November 2026_

In [1], replica-exchange Markov chain Monte Carlo with proposals drawn from QAOA-type circuits on IBM Heron processors finds maximum independent sets (MIS) of animal interaction networks with 17 to 117 nodes. For the 117-node instance, the optimum (49) is reached after 114 and 151 iterations on hardware, with 10,000 shots per iteration (1.14 and 1.51 million cost evaluations [1, Table IV]). The classical reference in [1] is the same replica-exchange scheme with uniform proposals of up to five bit flips, where the fastest replica needs a median of 6,293 iterations with one sample per iteration and 5,051 iterations with 10,000 samples per iteration [1, Table II].

## Result

A classical replica-exchange chain with a standard structure-aware MIS move reaches the optimum on the four identified instances of [1] after a median of 60 to 2,145 cost evaluations. On the 117-node instance this is about 500 times fewer cost evaluations than the hardware runs of [1].

The chain uses the same five replicas, the same temperature ladder (0.01, 0.11, 0.21, 0.51, 1.01) and exchanges between neighbouring temperatures every 10 iterations, with energy −|I|. It stays on independent sets: a proposal picks a uniformly random vertex v, removes v if it is in the set, and otherwise adds v and removes its neighbours from the set. Each replica makes one proposal per iteration, so one iteration costs 5 evaluations. Every run starts from the empty set, and the optimum is certified with CP-SAT.

| Instance | Nodes | Edges | MIS | Iterations, median (95th percentile) | Cost evaluations, median | Hardware in [1]: iterations, cost evaluations |
|---|---|---|---|---|---|---|
| mammalia-kangaroo-interactions | 17 | 91 | 4 | 12 (24) | 60 | 32 and 160; 2 and 20,000 |
| insecta-ant-trophallaxis-colony2 | 39 | 245 | 12 | 127 (272) | 635 | 12 and 120,000 |
| aves-sparrow-social | 52 | 454 | 13 | 115 (198) | 575 | 22 and 220,000 |
| aves-songbird-social | 117 | 1,027 | 49 | 429 (601) | 2,145 | 151 and 1,510,000; 114 and 1,140,000 |

Each row is 1,000 independent runs, and all of them reach the optimum (at most 1,020 iterations on the 117-node instance). One run on the 117-node instance takes 0.14 ms on one laptop core.

Scope:

- The comparison is in cost evaluations. In iterations, the hardware runs are shorter on the larger instances, since each of their iterations draws 10,000 samples.
- The instances are matched by size. The 117-node instance is aves-songbird-social with its seven isolated node identifiers kept: it has 1,027 distinct edges, while [1] lists 1,028, and its MIS of 49 is the optimum stated there. The 39-node instance has 245 distinct edges after merging repeated interactions. The 80-node instance of [1] is not identified.
- The proposal is a standard local move for independent sets, as used in classical MIS local search. It was not tuned on these instances.

## Files

- `sim/mis_mcmc.py`: the chain, the exact optimum by CP-SAT, and an assert that every state reaching the optimum is an independent set.
- `sim/mis_mcmc.txt`: the output for the table.

The graphs are those of QOBLIB [2] (kangaroo, sparrow) and Network Repository [3] (ant trophallaxis colony 2, songbird).

## References

1. K. V. Marshall, D. J. Egger, M. Garn, F. Schiavello, S. Brandhofer, C. Zoufal, S. Woerner. Quantum-enhanced Markov chain Monte Carlo for combinatorial optimization. arXiv:2602.06171.
2. T. Koch et al. Quantum optimization benchmarking library: the intractable decathlon. arXiv:2504.03832.
3. R. A. Rossi, N. K. Ahmed. The network data repository with interactive graph analytics and visualization. AAAI 2015.
