"""Random-state step: N |<u|psi>|^2 for uniformly random psi does not concentrate (law -> Exp(1)),
so a 'no' instance passes a fixed weight threshold with constant probability per trial.
The purified maximally mixed input gives the weight tr f(A)^2 / N exactly."""
import numpy as np

rng = np.random.default_rng(7)


def overlaps(N, trials):
    z = rng.normal(size=(trials, N)) + 1j * rng.normal(size=(trials, N))
    return N * np.abs(z[:, 0]) ** 2 / np.sum(np.abs(z) ** 2, axis=1)   # u = e_0 by invariance


def main():
    for N in [2 ** 6, 2 ** 10, 2 ** 14]:
        r = overlaps(N, 20000)
        for k in [0.1, 0.5]:
            p = np.mean(r >= 1 - k)
            assert abs(p - np.exp(-(1 - k))) < 0.03, (N, k, p)
            print(f"N = {N:6d}: Pr(N|<u|psi>|^2 >= {1 - k:.1f}) = {p:.3f}  (limit e^-{1 - k:.1f} = {np.exp(-(1 - k)):.3f})")
        # 'no' weight f1^2 r_1 vs 'yes' weight f1^2 r_1 + f2^2 r_2 with f1 = 1, f2 = 1/4, as in the random-state test
        r1, r2 = r, overlaps(N, 20000)
        for f2, lo in [(1 / 16, 0.4), (1.0, 0.15)]:
            q = np.quantile(r1 + f2 * r2, 0.5)    # a threshold that accepts half of the 'yes' runs
            fp = np.mean(r1 > q)
            assert fp > lo
            print(f"          f(sigma_2)^2 = {f2:.4f}: a threshold accepting half of the 'yes' runs accepts {fp:.2f} of the 'no' runs")
    print("overlap: all asserts passed")


if __name__ == "__main__":
    main()
