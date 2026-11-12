# Monte Carlo derivative pricing: break-even clock rates against randomized quasi-Monte Carlo

_12 November 2026_

Amplitude estimation prices a derivative with O(1/ε) calls to a circuit that loads the paths and the payoff, against O(1/ε²) paths for plain Monte Carlo. Whether this pays depends on the logical clock rate of a fault-tolerant machine. A resource study of two path-dependent contracts [1] puts the threshold for an advantage at T gates executed at about 10 MHz, for pricing a basket autocallable in about one second.

This folder computes the break-even logical T rate for the same autocallable against randomized quasi-Monte Carlo (RQMC) at the same accuracy, with the quantum cost taken from [1]. It also gives the measured RQMC error exponents for six standard payoffs, since the quantum speedup over RQMC depends on that exponent.

## Result

The contract of [1]: three underlyings, worst-of, 20 time steps of 1/20 year, five autocall dates with binary strike return 1.1 and payments 2, 4, ..., 10, and a knock-in put with barrier 0.7, put strike 1 and notional 18. The errors are normalized by the payoff range 28, as in [1]. The quantum cost is the total T-depth of [1, Table 1] for the re-parameterization method, 5.4 · 10⁷ at normalized error 2 · 10⁻³, scaled as 1/ε. The classical cost is the time of RQMC on one CPU core in NumPy at the smallest power of two of paths whose measured root mean square error meets the target. The break-even rate is the quantum T-depth divided by that time.

| Normalized error | Absolute error | RQMC paths | Classical time, one CPU core | Quantum T-depth [1] | Break-even logical T rate |
|---|---|---|---|---|---|
| 0.002 | 0.0560 | 4 096 | 8.5 ms | 5.4 · 10⁷ | **6.4 GHz** |
| 0.001 | 0.0280 | 8 192 | 17.1 ms | 1.1 · 10⁸ | **6.3 GHz** |
| 0.0003 | 0.0084 | 65 536 | 125.0 ms | 3.6 · 10⁸ | **2.9 GHz** |
| 0.0001 | 0.0028 | 524 288 | 1.02 s | 1.1 · 10⁹ | **1.1 GHz** |

At the accuracy target of [1], about 4 000 RQMC paths suffice, and they take under 10 ms on one core. Matching that time takes a logical T rate of about 6 GHz. The threshold of about 10 MHz in [1] compares with a classical Monte Carlo run of five to ten seconds with at least 40 000 paths, as described in [1, Appendix A.4]. This hints that at matched accuracy the threshold lies several hundred times higher. Since RQMC converges at about N^(−0.62) on this contract, the break-even rate falls only slowly with the target error, roughly as ε^0.6.

Previous best bound: a break-even T rate of about 10 MHz [1].

## Error exponents of RQMC

Root mean square error of RQMC (Owen-scrambled Sobol' points, Brownian bridge) against N paths, fitted on N = 2¹⁰ to 2¹⁶ with 32 independent scramblings, under geometric Brownian motion with spot 100, rate 0.05 and volatility 0.2 (`data/rqmc_rates.jsonl`). The autocallable of [1] is fitted on 16 scramblings.

| Payoff | Dimension | RQMC error exponent | Plain MC error exponent |
|---|---|---|---|
| European call | 1 | 0.90 | 0.50 |
| Digital call | 1 | 0.87 | 0.50 |
| Arithmetic Asian call, 16 dates | 16 | 0.77 | 0.50 |
| Down-and-out call, 16 monitoring dates | 16 | 0.54 | 0.50 |
| Digital on a basket of 5 | 5 | 0.58 | 0.50 |
| Autocallable, 4 dates | 4 | 0.64 | 0.52 |
| Basket autocallable of [1] | 60 | 0.62 | 0.50 |

Amplitude estimation has error exponent 1 in the number of oracle calls. Smooth payoffs leave RQMC close to that, so the quantum speedup is then a constant factor at best. Payoffs with discontinuities in many dimensions, such as barriers, basket digitals and autocallables, keep RQMC near N^(−0.55) to N^(−0.65). These are the instruments where the speedup is close to quadratic.

## Assumptions

- The quantum T-depth is that of [1] and is not recomputed here. Improvements in path loading or payoff evaluation lower the break-even rate in proportion.
- The classical time is one CPU core with NumPy, Sobol' generation included. A GPU or compiled code is faster, which raises the break-even rate.
- The comparison matches the root mean square error of RQMC with the error of amplitude estimation at confidence 0.68, the convention of [1].
- RQMC uses Owen scrambling and the Brownian bridge for the single-asset payoffs, and plain time ordering for the autocallable.

## Not covered

- The second contract of [1], a target accrual redemption forward.
- Classical refinements beyond RQMC: multilevel Monte Carlo, conditional Monte Carlo and other smoothing, and importance sampling.
- Many-instrument and nested risk calculations, where the classical cost per sample is larger.

## Files

- `sim/rqmc_rates.py`: the error exponents of the six payoffs.
- `sim/autocall_2012.py`: the autocallable of [1], its standard deviation and RQMC exponent (`data/autocall_2012.json`).
- `sim/breakeven.py`: the table above (`data/breakeven.jsonl`). The timing depends on the machine.

## References

1. S. Chakrabarti, R. Krishnakumar, G. Mazzola, N. Stamatopoulos, S. Woerner, W. J. Zeng. A threshold for quantum advantage in derivative pricing. Quantum 5, 463 (2021). arXiv:2012.03819.
