"""Label-level simulation of a Kuperberg-type sieve on Z_p, followed by iterative phase estimation.

Each coset state of the hidden shift f1(x) = f0(x - t), t = 2s, is a qubit |0> + w^{k t}|1> (w = e^{2 pi i/p})
with a uniform label k (shift_check.py checks this exactly). Combining two qubits by a CNOT and measuring the
target gives label k1 + k2 or k1 - k2 with probability 1/2 each, independently of t, so the sieve below is
simulated exactly by classical randomness on labels; only the final single-qubit measurements depend on t,
and their outcome probabilities are computed from the true t.

Sieve: sort the labels (as integers in (-p/2, p/2)), pair neighbours, keep the differences; repeat until the
labels are small, then keep the qubits with label +-1. Rescaling the oracle input by 2^{-j} turns the hidden
shift t into 2^j t, so a label-1 qubit of that instance has phase 2 pi 2^j t / p. Iterative phase estimation
(X and Y measurements, Kitaev's halving) then gives t, hence s = t/2. The binomial step (dstep_check.py)
(not simulated here) then recovers D. A label -1 qubit is the conjugate of a label 1 qubit, which the X and Y
measurements below account for by a sign flip of the Y outcome; the simulation treats both as label 1, which
gives the same statistics after that correction. The hidden t is drawn at random; f itself is not built here
(shift_check.py checks the coset states on actual quadratics)."""
import sys
import numpy as np

rng = np.random.default_rng(int(sys.argv[2]) if len(sys.argv) > 2 else 5)


def centred(k, p):
    k = k % p
    return np.where(k > p // 2, k - p, k)


def sieve_once(p, n0):
    lab = centred(rng.integers(1, p, size=n0), p)
    ones = 0
    while len(lab) > 1:
        ones += int(np.sum(np.abs(lab) == 1))
        lab = lab[np.abs(lab) > 1]
        if len(lab) < 2 or np.max(np.abs(lab)) < 2:
            break
        lab = np.sort(lab)
        diff = lab[1::2] - lab[0:-1:2]
        keep = rng.random(len(diff)) < 0.5                     # measurement gave the difference
        lab = diff[keep & (diff != 0)]
    return ones


def label_one_qubits(p, need, n0):
    got, used = 0, 0
    while got < need:
        got += sieve_once(p, n0)
        used += n0
    return got, used


def estimate_angle(theta, reps):
    """reps X and reps Y measurements of |0> + e^{2 pi i theta}|1>; returns the estimated theta mod 1."""
    phi = 2 * np.pi * theta
    cx = 2 * rng.binomial(reps, (1 + np.cos(phi)) / 2) / reps - 1
    cy = 2 * rng.binomial(reps, (1 + np.sin(phi)) / 2) / reps - 1
    return (np.arctan2(cy, cx) / (2 * np.pi)) % 1


def recover(p, n0, reps=12):
    t = int(rng.integers(1, p))
    n = p.bit_length() + 2
    states = 0
    est = []
    for j in range(n):
        _, used = label_one_qubits(p, 2 * reps, n0)
        states += used
        est.append(estimate_angle((pow(2, j, p) * t % p) / p, reps))
    th = est[-1]
    for j in range(n - 2, -1, -1):
        c = np.array([th / 2, th / 2 + 0.5])
        d = np.abs(((c - est[j]) + 0.5) % 1 - 0.5)
        th = c[np.argmin(d)]
    return t, int(round(th * p)) % p, states


if __name__ == "__main__":
    bits = [int(b) for b in sys.argv[1].split(",")] if len(sys.argv) > 1 else [16, 20, 24, 28]
    primes = {16: 65521, 20: 1048573, 24: 16777213, 28: 268435399, 32: 4294967291}
    print("p, sieve pool, coset states used, oracle queries (m per state, m offsets with p^2 (1/2 + 2/sqrt p)^m < 1/2), sqrt(p), t found")
    for b in bits:
        p = primes[b]
        n0 = 1 << int(np.ceil(np.sqrt(2 * b) * 1.6 + 4))
        ok = 0
        for trial in range(3):
            t, t_hat, states = recover(p, n0)
            m = int(np.ceil(np.log(2.0 * p * p) / -np.log(0.5 + 2 / np.sqrt(float(p)))))
            ok += t == t_hat
            print(f"p = {p:11d} (2^{b}), pool {n0:8d}, states {states:11d}, queries {m * states:.2e}, "
                  f"sqrt(p) = {np.sqrt(p):.2e}, t recovered: {t == t_hat}")
        assert ok == 3
    print("all recovered")
