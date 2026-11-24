"""20-dimensional STORE-RECALL task of the spike-frequency-adaptation paper (eLife 2021, e65459) with a
hand-written plain-LIF circuit: 81 neurons, no adaptation, no self-connections, no training.

Task ported from the public reference code (bin/tutorial_extended_storerecall_utils.py and
tutorial_extended_storerecall_with_LSNN.py, MIT licence): 10 steps of 200 ms; 88 input neurons = 44 channels
times 2 (STORE twice, RECALL twice, 20 value bits, 20 inverted bits), 400 Hz when active; a random word is
shown at every step; STORE and RECALL alternate with probability 1/5 per step; test words come from a
dictionary of 20 words with at most 4 active bits and pairwise Hamming distance above 5.
Readout: weights times the 20 ms filtered spikes at the middle of each step, no bias, bit = 1 iff positive.
A recall counts as right when all 20 bits are right.

Circuit per bit i (weights in units of the threshold), as in sr_circuit.py:
  S_i: driven by STORE, silenced by inverted bit i   Z_i: driven by STORE, silenced by bit i
  M_i, M_i': memory latch (two neurons that excite each other), switched on by S_i and off by Z_i
plus one relay neuron for RECALL. Bit i is read as M_i minus half the relay.

usage: sr20.py [N_SEQUENCES] [SEED] [silent|shown]     (value channels during RECALL; default silent as in the paper)
"""
import json, sys
import numpy as np
import torch
from sr_protocol import THR, run, valid, STORE, RECALL

BITS, SEQ_LEN, TAU_CHAR, F0, PER = 20, 10, 200, 0.4, 2
P = dict(drive=10.0, veto=-60.0, set=60.0, kill=-60.0, self_exc=40.0, relay=10.0)
N = 4 * BITS + 1


def dictionary(rng, size=20, max_active=4, min_dist=5):
    """Port of generate_value_dicts: greedy sampling of words with at most max_active bits and pairwise Hamming
    distance above min_dist. Greedy sampling can reach a set that admits no further word; it then starts again."""
    while True:
        words, rejected = [], 0
        while len(words) < size and rejected < 20000:
            w = rng.integers(0, 2, size=BITS)
            if not 1 <= w.sum() <= max_active:
                continue
            if all((w != u).sum() > min_dist for u in words):
                words.append(w)
            else:
                rejected += 1
        if len(words) == size:
            return np.array(words)


def make_batch(batch, words, rng, recall_silent=True):
    chan = np.zeros((batch, 4 + 2 * BITS, SEQ_LEN), dtype=np.float32)
    target = np.zeros((batch, SEQ_LEN, BITS), dtype=int)
    is_recall = np.zeros((batch, SEQ_LEN), dtype=bool)
    count = 0
    for b in range(batch):
        while True:                                    # port of generate_storerecall_signals_with_prob
            seq, last = np.zeros(SEQ_LEN, dtype=int), RECALL
            for t in range(SEQ_LEN):
                if last == RECALL and rng.random() < 0.2:
                    seq[t] = last = STORE
                elif last == STORE and rng.random() < 0.2:
                    seq[t] = last = RECALL
            if valid(seq):
                break
        choice = rng.integers(0, len(words), size=SEQ_LEN)
        for t in range(SEQ_LEN - 1):                   # no word twice in a row
            while choice[t + 1] == choice[t]:
                choice[t + 1] = rng.integers(0, len(words))
        for t in np.where(seq == STORE)[0]:            # stored words cycle through the dictionary
            choice[t] = count % len(words); count += 1
        vals = words[choice].T                          # (BITS, L)
        chan[b, 0:2] = seq == STORE
        chan[b, 2:4] = seq == RECALL
        chan[b, 4:4 + BITS] = vals
        chan[b, 4 + BITS:] = 1 - vals
        stored = None
        for t in range(SEQ_LEN):
            if seq[t] == STORE:
                stored = vals[:, t]
            if seq[t] == RECALL:
                target[b, t], is_recall[b, t] = stored, True
                if recall_silent:
                    chan[b, 4:, t] = 0
    rates = np.repeat(np.repeat(chan, PER, axis=1), TAU_CHAR, axis=2) * F0          # (B, 88, T)
    spikes = (rng.random(rates.shape, dtype=np.float32) < rates).astype(np.float32)
    return torch.from_numpy(spikes).permute(2, 0, 1).contiguous(), target, is_recall


def circuit(p=P):
    W_in, W_rec, W_out = torch.zeros(N, 88), torch.zeros(N, N), torch.zeros(N, BITS)
    store, recall = slice(0, 4), slice(4, 8)
    R = 4 * BITS
    W_in[R, recall] = p["relay"]
    for i in range(BITS):
        S, Z, M, M2 = 4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3
        val = slice(8 + 2 * i, 10 + 2 * i)
        inv = slice(8 + 2 * BITS + 2 * i, 10 + 2 * BITS + 2 * i)
        W_in[S, store] = p["drive"]; W_in[S, inv] = p["veto"]
        W_in[Z, store] = p["drive"]; W_in[Z, val] = p["veto"]
        W_rec[M, S] = p["set"]; W_rec[M, M2] = W_rec[M2, M] = p["self_exc"]
        W_rec[M, Z] = W_rec[M2, Z] = p["kill"]
        W_out[M, i] = 1.0; W_out[R, i] = -0.5
    return W_in * THR, W_rec * THR, W_out


@torch.no_grad()
def evaluate(n_seq, seed, recall_silent=True, p=P, batch=128):
    rng = np.random.default_rng(seed)
    words = dictionary(rng)
    W_in, W_rec, W_out = circuit(p)
    decay = float(np.exp(-1 / 20.0))
    word_ok, bit_ok, spikes = [], [], 0.0
    for k in range(0, n_seq, batch):
        x, target, is_recall = make_batch(min(batch, n_seq - k), words, rng, recall_silent)
        spk = run(x, W_in, W_rec)
        psp, outs = torch.zeros(x.shape[1], N), []
        for t in range(x.shape[0]):
            psp = decay * psp + (1 - decay) * spk[t]
            if t % TAU_CHAR == TAU_CHAR // 2:
                outs.append(psp @ W_out)
        pred = (torch.stack(outs, 1).numpy() > 0).astype(int)        # (B, L, BITS)
        ok = pred[is_recall] == target[is_recall]
        word_ok.append(ok.all(1)); bit_ok.append(ok.mean(1)); spikes += spk.sum().item()
    word_ok, bit_ok = np.concatenate(word_ok), np.concatenate(bit_ok)
    return dict(task="20-dim STORE-RECALL", neurons=N, sequences=n_seq, seed=seed, recall_silent=recall_silent,
                recalls=len(word_ok), word_accuracy=float(word_ok.mean()), bit_accuracy=float(bit_ok.mean()),
                wrong_words=int((~word_ok).sum()), rate_hz_per_neuron=spikes / n_seq / (SEQ_LEN * TAU_CHAR / 1000) / N)


if __name__ == "__main__":
    torch.set_num_threads(1)
    a = sys.argv[1:]
    print(json.dumps(evaluate(int(a[0]) if a else 128, int(a[1]) if len(a) > 1 else 0,
                              recall_silent=(a[2] != "shown") if len(a) > 2 else True)), flush=True)
