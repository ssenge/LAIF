"""Hand-written plain-LIF circuit for the one-dimensional STORE-RECALL task: 5 neurons, no adaptation, no self-connections,
no training. Weights are in units of the threshold.

  S (set detector):   driven by STORE, silenced by value 0  ->  fires iff STORE with value 1
  Z (reset detector): driven by STORE, silenced by value 1  ->  fires iff STORE with value 0
  M, M' (memory):     two neurons that excite each other and so keep firing; switched on by S, off by Z
                      ->  on iff last stored value is 1
  O (says 0):         driven by RECALL, silenced by M  ->  fires iff RECALL and memory off
Readout: output 1 reads M, output 0 reads O.

The five weights were chosen on sequences from seeds 123 and 124 (settings "200 ms" and "2 s").

usage: sr_circuit.py            self-check and Table 1 settings, seed 0
       sr_circuit.py SEED...    Table 1 settings on the given seeds (held-out: 1 and above)
"""
import sys, json
import torch
from sr_protocol import THR, TABLE1, make_batch, run, recall_accuracy

P = dict(drive=40.0, veto=-120.0, set=60.0, kill=-60.0, self_exc=40.0)
N = 5


def circuit(p=P):
    g = slice(0, 10), slice(10, 20), slice(20, 30), slice(30, 40)     # value 0, value 1, STORE, RECALL
    S, Z, M, O, M2 = 0, 1, 2, 3, 4
    W_in, W_rec, W_out = torch.zeros(N, 40), torch.zeros(N, N), torch.zeros(N, 2)
    W_in[S, g[2]] = p["drive"]; W_in[S, g[0]] = p["veto"]
    W_in[Z, g[2]] = p["drive"]; W_in[Z, g[1]] = p["veto"]
    W_rec[M, S] = p["set"]; W_rec[M, M2] = W_rec[M2, M] = p["self_exc"]
    W_rec[M, Z] = W_rec[M2, Z] = p["kill"]
    W_in[O, g[3]] = p["drive"]; W_rec[O, M] = p["kill"]
    W_out[M, 1] = 1.0; W_out[O, 0] = 1.0
    return W_in * THR, W_rec * THR, W_out


def evaluate(cond, seed, batch=2048, p=P):
    seq_len, tau_char, seq_delay = TABLE1[cond]
    W_in, W_rec, W_out = circuit(p)
    hits, n_spk, n_seq = [], 0.0, 0
    for k in range(batch // 256):                                    # chunks keep memory small
        x, sym, target, delay = make_batch(256, seq_len, tau_char, seq_delay, seed * 1000 + k)
        spk = run(x, W_in, W_rec)
        _, hit, _ = recall_accuracy(spk, W_out, sym, target, tau_char)
        hits.append(hit); n_spk += spk.sum().item(); n_seq += 256
    hit = torch.cat([torch.from_numpy(h) for h in hits]).float()
    seconds = seq_len * tau_char / 1000
    return dict(cond=cond, seed=seed, recalls=len(hit), acc=hit.mean().item(),
                errors=int(len(hit) - hit.sum().item()), rate_hz_per_neuron=n_spk / n_seq / seconds / N)


if __name__ == "__main__":
    torch.set_num_threads(1)
    # the memory neuron holds its state with no input for 60 s
    W_in, W_rec, _ = circuit()
    x = torch.zeros(60_000, 2, 40)
    x[:200, 0, 10:30] = (torch.rand(200, 20, generator=torch.Generator().manual_seed(0)) < 0.05).float()   # STORE with value 1
    s = run(x, W_in, W_rec)
    assert s[-1000:, 0, 2].sum() > 100 and s[:, 1, 2].sum() == 0
    for seed in [int(a) for a in sys.argv[1:]] or [0]:
        for cond in TABLE1:
            print(json.dumps(evaluate(cond, seed)), flush=True)
