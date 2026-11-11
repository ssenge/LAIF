# Lemma E: unbiased phase-shifted amplitude estimation, boosted over 2m+1 runs (shortest arc holding m+1 estimates).
# Checks (a) E Y = p (with lambda from phi = 0), (b) P(|Y - p| > 4/M) <= exp(-m/4), (c) 1 - lambda <= 18/M^2 + 2 exp(-m/4).
import numpy as np

TWO_PI = 2 * np.pi


def fejer_sample(M, size, rng):
    """errors with density M sinc^2(Mx/2) / (2 pi sinc^2(x/2)) on (-pi, pi]: phase estimation after a uniform phase shift."""
    # shifted phase estimation: output grid point 2 pi y/M minus a uniform shift; equivalently sample the exact law
    out = np.empty(0)
    while out.size < size:
        x = rng.uniform(-np.pi, np.pi, 4 * size)
        with np.errstate(invalid="ignore", divide="ignore"):
            f = np.where(np.abs(x) < 1e-12, M / TWO_PI, np.sin(M * x / 2) ** 2 / (TWO_PI * M * np.sin(x / 2) ** 2))
        keep = rng.uniform(0, M / TWO_PI, x.size) < f
        out = np.concatenate([out, x[keep]])
    return out[:size]


def boosted(phi, M, m, rng, reps):
    """reps outputs of Algorithm 2 of [2] for true phase phi (in chunks to keep memory small)."""
    if reps > 20000:
        return np.concatenate([boosted(phi, M, m, rng, min(20000, reps - k)) for k in range(0, reps, 20000)])
    est = (phi + fejer_sample(M, reps * (2 * m + 1), rng)).reshape(reps, 2 * m + 1) % TWO_PI
    est.sort(axis=1)
    ext = np.concatenate([est, est + TWO_PI], axis=1)            # arcs of m+1 consecutive points, wrapping
    lens = ext[:, m:m + 2 * m + 1] - ext[:, :2 * m + 1]
    j = lens.argmin(axis=1)
    a = ext[np.arange(reps), j]; b = ext[np.arange(reps), j + m]
    return ((a + b) / 2) % TWO_PI


def estimator(p, M, m, lam, rng, reps):
    th = np.arcsin(np.sqrt(p))
    sign = rng.choice([1, -1], reps)                              # Grover iterate eigenphase +-2 theta, prob 1/2 each
    ph = np.where(sign > 0, boosted(2 * th, M, m, rng, reps), boosted(-2 * th % TWO_PI, M, m, rng, reps))
    return 0.5 - np.cos(ph) / (2 * lam)


if __name__ == "__main__":
    rng = np.random.default_rng(3)
    for M, m in [(16, 12), (32, 12), (64, 16), (128, 20)]:
        lam = np.cos(boosted(0.0, M, m, rng, 200000)).mean()      # lambda(M, m) = E cos(error)
        assert 1 - lam <= 18 / M ** 2 + 2 * np.exp(-m / 4)
        worst_bias, worst_tail = 0, 0
        for p in [0.0, 0.01, 0.1, 0.3, 0.5, 0.77, 0.99, 1.0]:
            Y = estimator(p, M, m, lam, rng, 60000)
            se = Y.std() / np.sqrt(Y.size)
            worst_bias = max(worst_bias, abs(Y.mean() - p) / max(se, 1e-12))
            tail = np.mean(np.abs(Y - p) > 4 / M)
            worst_tail = max(worst_tail, tail)
            assert np.abs(Y).max() <= 2
        assert worst_bias < 5 and worst_tail <= np.exp(-m / 4)
        print(f"M={M:4d} m={m:3d}: 1-lambda={1 - lam:.2e}, max |bias|/se={worst_bias:.2f}, max P(|Y-p|>4/M)={worst_tail:.1e} <= e^-m/4={np.exp(-m / 4):.1e}", flush=True)
    print("Lemma E checks: ok")
