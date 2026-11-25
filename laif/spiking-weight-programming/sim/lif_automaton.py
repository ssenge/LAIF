"""Any finite automaton on one recurrent layer of LIF neurons with hard reset, at every decay.

Neuron model as in al.py: v[t] = decay * v[t-1] * (1 - y[t-1]) + input[t], y[t] = (v[t] > 0.5).
For states Q, symbols A, transition delta and start state q0 the layer has one gate per pair (q, a) and one
marker neuron with bias 1. Gate (q, a) has drive 0.75 * (2 - [state is q] - [input is a]); "state is q'" is the
number of silent gates (q, a) of the previous step with delta(q, a) = q', corrected at the first step by the
marker. The linear readout for state q' sums the silent gates with delta(q, a) = q'.

The check draws random automata, random words and decays (also negative and above 1) and asserts that the
readout equals the state of the automaton after every step, in 32-bit floating point.

usage: lif_automaton.py [N_AUTOMATA] [SEED]
"""
import json, sys
import numpy as np

W, THR = np.float32(0.75), np.float32(0.5)


def network(delta, q0):
    """delta: (nq, na) int array. Returns input weights, recurrent weights, bias, readout of the nq*na+1 neurons."""
    nq, na = delta.shape
    n = nq * na + 1                                   # last neuron: marker
    w_in, w_rec, b = np.zeros((n, na), np.float32), np.zeros((n, n), np.float32), np.zeros(n, np.float32)
    read = np.zeros((nq, n), np.float32)
    count = np.bincount(delta.ravel(), minlength=nq)  # gates that lead to each state
    for q in range(nq):
        for a in range(na):
            read[delta[q, a], q * na + a] = -1.0      # silent gate: 1 - y
    for q in range(nq):
        for a in range(na):
            m = q * na + a
            # drive = W * (2 - state(q) - x[a]), state(q) = sum(1 - y[src]) - (count[q] - [q = q0]) * (1 - y[marker])
            b[m] = W * (2 - (1 if q == q0 else 0))
            w_in[m, a] = -W
            src = np.where(delta.ravel() == q)[0]
            w_rec[m, src] += W
            w_rec[m, n - 1] -= W * (count[q] - (1 if q == q0 else 0))
    b[n - 1] = 1.0
    return w_in, w_rec, b, read, count.astype(np.float32)


def run(delta, q0, word, decay):
    nq, na = delta.shape
    w_in, w_rec, b, read, count = network(delta, q0)
    n = len(b)
    v, y, q = np.zeros(n, np.float32), np.zeros(n, np.float32), q0
    decay = np.float32(decay)
    for a in word:
        x = np.zeros(na, np.float32); x[a] = 1.0
        v = decay * v * (1 - y) + w_in @ x + w_rec @ y + b
        y = (v > THR).astype(np.float32)
        q = delta[q, a]
        out = read @ y + count                        # number of silent gates that lead to each state
        assert out.argmax() == q and out[q] == 1.0 and out.sum() == 1.0, (delta, word, decay)
        assert y[:-1].sum() == n - 2 and y[-1] == 1.0
    return q


if __name__ == "__main__":
    a = sys.argv[1:]
    n_auto, seed = (int(a[0]) if a else 300), (int(a[1]) if len(a) > 1 else 0)
    rng = np.random.default_rng(seed)
    steps, largest = 0, 0
    for _ in range(n_auto):
        nq, na = int(rng.integers(1, 13)), int(rng.integers(1, 6))
        delta = rng.integers(0, nq, size=(nq, na))
        for decay in (0.0, 0.3, 0.5, 0.9, 1.0, float(rng.uniform(-2, 3))):
            word = rng.integers(0, na, size=200)
            run(delta, int(rng.integers(0, nq)), word, decay)
            steps += len(word)
        largest = max(largest, nq * na + 1)
    print(json.dumps(dict(check="readout equals automaton state after every step", automata=n_auto, steps=steps,
                          decays="0, 0.3, 0.5, 0.9, 1 and one random value in [-2, 3] per automaton",
                          largest_network=largest, seed=seed)))
