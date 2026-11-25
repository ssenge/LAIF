"""One-dimensional STORE-RECALL task and LIF network of the spike-frequency-adaptation paper
(eLife 2021, e65459), ported to numpy/torch from its public reference code
(github.com/IGITUGraz/Spike-Frequency-Adaptation-Supports-Network-Computations, MIT licence,
files bin/tutorial_storerecall_utils.py, bin/tutorial_storerecall_with_LSNN.py, lsnn/spiking_models.py).

Task: a sequence of seq_len symbols, each shown for tau_char ms. 40 input neurons in 4 groups of 10
(value 0, value 1, STORE, RECALL) fire random spikes at 50 Hz while their group is active.
At a STORE step the value to remember is shown together with the STORE group. At a RECALL step only
the RECALL group is active and the network has to report the last stored value.
Network: LIF, tau_m = 20 ms, threshold 0.01, reset by subtraction, 3 ms refractory, 1 ms delay, dt = 1 ms.
Readout: linear on the spikes filtered with 20 ms, averaged over each symbol step, argmax of two outputs.
"""
import numpy as np
import torch

N_IN, F0, TAU, THR, N_REF = 40, 0.05, 20.0, 0.01, 3
STORE, RECALL = 2, 3
# Table 1 of the paper: expected delay -> (seq_len, tau_char, seq_delay). The sequence lengths and step
# durations are from the paper; seq_delay = expected delay / tau_char is the flag of the reference code
# ("Expected delay in character steps", STORE and RECALL each drawn with probability 1 / (1 + seq_delay)).
# The delays that occur are shorter than this nominal value, because sequences are cut at seq_len:
# the mean STORE-to-RECALL distance is about 0.2, 1.4, 2.5, 4.6 and 7.3 s in the five settings.
TABLE1 = {"200 ms": (12, 50, 4), "2 s": (20, 200, 10), "4 s": (40, 200, 20), "8 s": (80, 200, 40), "16 s": (120, 200, 80)}


def valid(seq):
    """Port of validity_test."""
    st, rc = np.where(seq == STORE)[0], np.where(seq == RECALL)[0]
    if len(st) == 0 or len(rc) == 0 or not (seq < STORE).any():
        return False
    if rc[0] < st[0] or rc[-1] < st[-1]:
        return False
    for t in st:
        if t == len(seq) - 1 or seq[t + 1] >= STORE:
            return False
    for a, b in zip(rc[:-1], rc[1:]):
        if not ((a < st) & (st < b)).any():
            return False
    for a, b in zip(st[:-1], st[1:]):
        if not ((a < rc) & (rc < b)).any():
            return False
    return True


def symbols(batch, seq_len, seq_delay, rng):
    """Port of generate_input_with_prob with prob = 1 / (1 + seq_delay)."""
    p = 1.0 / (1 + seq_delay)
    out = np.zeros((batch, seq_len), dtype=int)
    for b in range(batch):
        last = RECALL
        while True:
            seq = rng.integers(0, 2, size=seq_len)
            for t in range(seq_len):
                if last == RECALL and rng.random() < p:
                    seq[t] = last = STORE
                elif last == STORE and rng.random() < p:
                    seq[t] = last = RECALL
            if valid(seq):
                break
        out[b] = seq
    return out


def make_batch(batch, seq_len, tau_char, seq_delay, seed):
    """Returns spikes (T, B, 40) float32, symbols (B, seq_len), targets (B, seq_len) valid at RECALL steps,
    and the delay in steps of each RECALL (same shape, 0 elsewhere)."""
    rng = np.random.default_rng(seed)
    sym = symbols(batch, seq_len, seq_delay, rng)
    chan = np.stack([(sym == c) for c in range(4)]).astype(np.float32)        # (4, B, L)
    target = np.zeros_like(sym)
    delay = np.zeros_like(sym)
    for b in range(batch):
        stored, t_store = 0, 0
        for t in range(seq_len):
            if sym[b, t] == STORE:
                stored, t_store = sym[b, t + 1], t
                chan[stored, b, t] = 1                       # value shown together with STORE
                if rng.random() < 0.5:                       # the following symbol is flipped at random
                    chan[0, b, t + 1], chan[1, b, t + 1] = chan[1, b, t + 1], chan[0, b, t + 1]
            elif sym[b, t] == RECALL:
                target[b, t], delay[b, t] = stored, t - t_store
    rates = np.repeat(np.repeat(chan, N_IN // 4, axis=0), tau_char, axis=2) * F0   # (40, B, T)
    spikes = (rng.random(rates.shape, dtype=np.float32) < rates).astype(np.float32)
    return torch.from_numpy(spikes).permute(2, 1, 0).contiguous(), sym, target, delay


@torch.no_grad()
def run(x, W_in, W_rec, thr=THR):
    """Port of LIF.__call__ / LIF_dynamic with n_delay = 1. x: (T, B, 40); W_in: (n, 40); W_rec: (n, n).
    Returns spikes (T, B, n)."""
    T, B, _ = x.shape
    n = W_in.shape[0]
    assert not W_rec.diagonal().any(), "the reference network has no self-connections"
    decay = float(np.exp(-1.0 / TAU))
    v = torch.zeros(B, n)
    z = torch.zeros(B, n)
    ref = torch.zeros(B, n)                       # steps since which the neuron may fire again
    out = torch.empty(T, B, n)
    for t in range(T):
        i_t = x[t] @ W_in.T + z @ W_rec.T
        new_z = ((v > thr) & (ref <= 0)).float()  # the spike is read from the voltage before the update
        v = decay * v + (1 - decay) * i_t - z * thr
        ref = torch.where(new_z > 0, torch.full_like(ref, N_REF), ref - 1)
        z = new_z
        out[t] = z
    return out


@torch.no_grad()
def recall_accuracy(spk, W_out, sym, target, tau_char):
    """spk: (T, B, n), W_out: (n, 2). Returns the fraction of RECALL steps answered correctly, and the hits."""
    decay = float(np.exp(-1.0 / TAU))
    T, B, n = spk.shape
    psp = torch.zeros(B, n)
    acc = torch.zeros(B, T // tau_char, 2)
    for t in range(T):
        psp = decay * psp + (1 - decay) * spk[t]
        acc[:, t // tau_char] += psp @ W_out
    pred = acc.argmax(2).numpy()
    m = sym == RECALL
    hit = pred[m] == target[m]
    return hit.mean(), hit, m
