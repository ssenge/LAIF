"""AutoRound (sign-gradient rounding, auto-round 0.16.1) as a baseline on the same protocol as nnc.pipeline:
same model load, same WikiText-2 train calibration windows (nnc.pipeline._calib_llm), same perplexity.
Weights of the decoder linear layers are quantized, embedding and head stay 16-bit (as in the pipeline).
Bits counted as for gptq: b per weight + fp16 scale and zero point per group.

python sim/autoround_run.py qwen05 --bits 2 --group 64 --iters 50 --nsamples 128 --seqlen 2048 --out runs/qwen05_2048.jsonl"""
import argparse, json, pathlib, resource, sys, time
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
import torch
from nnc import models as M, pipeline as P, compress as C

ap = argparse.ArgumentParser()
ap.add_argument('model')
ap.add_argument('--bits', type=int, default=2)
ap.add_argument('--group', type=int, default=64)
ap.add_argument('--iters', type=int, default=50)
ap.add_argument('--nsamples', type=int, default=128)
ap.add_argument('--seqlen', type=int, default=2048)
ap.add_argument('--bs', type=int, default=8)
ap.add_argument('--evlen', type=int, default=2048)
ap.add_argument('--nwin', type=int, default=None)
ap.add_argument('--threads', type=int, default=2)
ap.add_argument('--device', default='cpu', help="'mps' only on AC power")
ap.add_argument('--out', required=True)
a = ap.parse_args()
if a.device == 'mps':  # MPS runs only on AC power
    import subprocess
    assert 'AC Power' in subprocess.run(['pmset', '-g', 'batt'], capture_output=True, text=True).stdout, 'not on AC power'
torch.set_num_threads(a.threads); torch.set_num_interop_threads(1)
torch.manual_seed(0)

model, tok = M.load_llm(a.model)
mods = P.targets(model, 'llm')
orig = {n: m.weight.data.clone() for n, m in mods.items()}
windows = [x[None] for x in P._calib_llm(tok, a.nsamples, a.seqlen)]
from auto_round import AutoRound
t0 = time.time()
ar = AutoRound(model, tokenizer=tok, scheme=f'W{a.bits}A16', bits=a.bits, group_size=a.group, sym=False, iters=a.iters,
               nsamples=a.nsamples, seqlen=a.seqlen, batch_size=a.bs, dataset=windows, device_map=a.device)
qmodel, _ = ar.quantize()
qmodel = qmodel.to('cpu').float()  # evaluation on the CPU path of the pipeline, as for every other row
t1 = time.time()
qmods = P.targets(qmodel, 'llm')
assert set(qmods) == set(mods), set(mods) ^ set(qmods)
# the weights must now be quantize-dequantized: at most 2^b distinct values per group of a row
for n, m in list(qmods.items())[:3]:
    Wg = m.weight.data.float().reshape(m.weight.shape[0], -1, a.group)
    nd = max(len(torch.unique(Wg[r, k])) for r in range(4) for k in range(Wg.shape[1]))
    assert nd <= 2 ** a.bits, (n, nd)
n = sum(m.weight.numel() for m in qmods.values())
bits = sum(m.weight.numel() * a.bits + (m.weight.numel() // a.group) * 2 * C.FP for m in qmods.values())
werr = sum(((orig[k] - m.weight.data.float()) ** 2).sum().item() for k, m in qmods.items()) / sum((w ** 2).sum().item() for w in orig.values())
ppl = M.perplexity(qmodel, M.wikitext_ids(tok, 'test'), a.evlen, a.nwin, bs=max(1, 2048 // a.evlen))
row = {'model': a.model, 'spec': f'autoround:b={a.bits},g={a.group},iters={a.iters},ns={a.nsamples},sl={a.seqlen},dev={a.device}', 'bpw': bits / n,
       'werr_plain': werr, 'ppl': ppl, 'compress_s': round(t1 - t0, 1), 'eval_s': round(time.time() - t1, 1), 'nwin': a.nwin,
       'evlen': a.evlen, 'maxrss_gb': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2 ** 30, 'time': time.strftime('%Y-%m-%d %H:%M:%S')}
print(json.dumps(row), flush=True)
with open(a.out, 'a') as f:
    f.write(json.dumps(row) + '\n')
