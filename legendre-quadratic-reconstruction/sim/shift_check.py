"""Reduction of a squarefree monic quadratic f(x) = (x + s)^2 - D (D != 0) to a hidden shift with injective
functions. For random offsets a_1, ..., a_m, f0(x) = (chi(f(x + a_i)))_i and f1(x) = (chi(f(-x - a_i)))_i.
Claims:
(1) f1(x) = f0(x - 2s);
(2) f0 is injective for m about 2 log2 p random offsets (the README bounds the failure probability by
p^2 (1/2 + 2/sqrt(p))^m via the Weil bound);
(3) the coset state of a measured value v = f0(x0) is (|0, x0> + |1, x0 + 2s>)/sqrt 2, so after the Fourier
transform the label k is uniform and the qubit is |0> + e^{2 pi i k 2s/p}|1> (an identity check)."""
import numpy as np

rng = np.random.default_rng(2)


def chi_table(p):
    chi = np.full(p, -1, dtype=np.int64)
    chi[(np.arange(1, p) ** 2) % p] = 1
    chi[0] = 0
    return chi


def V(p, chi, s, D, A, xs):
    f = lambda z: ((z + s) ** 2 - D) % p
    return np.stack([chi[f((xs + a) % p)] for a in A], axis=1)


def injective(rows):
    return len({r.tobytes() for r in rows}) == len(rows)


if __name__ == "__main__":
    for p in [1009, 7919, 65537]:
        chi = chi_table(p)
        xs = np.arange(p)
        print(f"p = {p}, m with p^2 (1/2 + 2/sqrt p)^m < 1/2: "
              f"{int(np.ceil(np.log(2 * p * p) / -np.log(0.5 + 2 / np.sqrt(p))))}")
        for m in [8, 16, 24, 32, int(np.ceil(2 * np.log2(p))), int(np.ceil(3 * np.log2(p)))]:
            ok = 0
            trials = 20
            for _ in range(trials):
                s, D = int(rng.integers(p)), int(rng.integers(1, p))
                A = rng.integers(0, p, size=m)
                ok += injective(V(p, chi, s, D, A, xs))
            print(f"   m = {m:3d}: f0 injective in {ok}/{trials} random instances")
        # (1) and (3) on one instance with m = 3 log2 p
        m = int(np.ceil(3 * np.log2(p)))
        s, D = int(rng.integers(p)), int(rng.integers(1, p))
        A = rng.integers(0, p, size=m)
        f0 = V(p, chi, s, D, A, xs)
        f1 = V(p, chi, s, D, (-A) % p, (-xs) % p)                    # chi(f(-x - a_i))
        assert np.array_equal(f1, f0[(xs - 2 * s) % p]), "hidden shift identity"
        assert injective(f0)
        # coset state for a random value v = f0(x0): (|0, x0> + |1, x0 + 2s>)/sqrt 2; Fourier transform on x
        x0 = int(rng.integers(p))
        x1 = int(np.flatnonzero((f1 == f0[x0]).all(axis=1))[0])
        k = np.arange(p)
        amp0 = np.exp(2j * np.pi * k * x0 / p) / np.sqrt(2 * p)
        amp1 = np.exp(2j * np.pi * k * x1 / p) / np.sqrt(2 * p)
        pk = np.abs(amp0) ** 2 + np.abs(amp1) ** 2
        rel = amp1 / amp0
        assert np.allclose(pk, 1 / p) and np.allclose(rel, np.exp(2j * np.pi * k * (2 * s) / p))
        print(f"   instance s = {s}, D = {D}: f1(x) = f0(x - 2s) for all x, f0 injective, labels uniform, "
              f"qubit phase 2 pi k (2s)/p: ok")
    print("all checks passed")
