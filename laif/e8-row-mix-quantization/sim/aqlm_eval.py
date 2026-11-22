"""A released AQLM checkpoint (1 codebook of 2^16 entries, groups of 8 inputs, one scale per output row) on the
protocol of nnc.pipeline: the weights are decoded to dense fp32 from the safetensors file, every other tensor
of the checkpoint (norms, embedding, head) is taken from it too, and the perplexity runs on the CPU path.
Bits counted as for every other row: codes, the codebooks of each layer and the scales, all at their stored width.

python -I sim/aqlm_eval.py tinyllama runs/ext/aqlm_tinyllama --out runs/tinyllama_2048.jsonl"""
import argparse, json, pathlib, resource, sys, time
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
import torch
from safetensors import safe_open
from nnc import models as M, pipeline as P

ap = argparse.ArgumentParser()
ap.add_argument('model')
ap.add_argument('ckpt')
ap.add_argument('--out', required=True)
ap.add_argument('--evlen', type=int, default=2048)
ap.add_argument('--nwin', type=int, default=None)
ap.add_argument('--threads', type=int, default=2)
ap.add_argument('--check', type=int, default=1, help='compare the decoded weights with the aqlm kernel on one layer')
a = ap.parse_args()
torch.set_num_threads(a.threads)
cfg = json.load(open(pathlib.Path(a.ckpt) / 'config.json'))['quantization_config']
assert (cfg['quant_method'], cfg['num_codebooks'], cfg['out_group_size']) == ('aqlm', 1, 1), cfg
gi, nb = cfg['in_group_size'], cfg['nbits_per_codebook']


def decode(codes, codebooks, scales):
    """W[o, j*gi:(j+1)*gi] = codebooks[0, codes[o, j]] * scales[o]; int16 codes hold 16-bit indices (two's complement)."""
    idx = codes[..., 0].long() % (1 << nb)
    return (codebooks[0, idx, 0, :].float() * scales.float().reshape(-1, 1, 1)).reshape(codes.shape[0], -1)


model, tok = M.load_llm(a.model)
mods = P.targets(model, 'llm')
f = safe_open(str(pathlib.Path(a.ckpt) / 'model.safetensors'), 'pt')
keys = set(f.keys())
n = bits = 0
for name, m in mods.items():
    k = f'model.layers.{name}'
    W = decode(f.get_tensor(k + '.codes'), f.get_tensor(k + '.codebooks'), f.get_tensor(k + '.scales'))
    assert W.shape == m.weight.shape, (name, W.shape, m.weight.shape)
    m.weight.data = W
    n += W.numel()
    bits += f.get_tensor(k + '.codes').numel() * nb + f.get_tensor(k + '.codebooks').numel() * 16 + f.get_tensor(k + '.scales').numel() * 16
    keys -= {k + s for s in ('.codes', '.codebooks', '.scales')}
sd = model.state_dict()
for k in keys:  # norms, embedding, head of the checkpoint
    assert k in sd and list(sd[k].shape) == list(f.get_slice(k).get_shape()), k
    sd[k].copy_(f.get_tensor(k).float())
if a.check:  # the dense decode equals the aqlm layer on random inputs
    from aqlm import QuantizedLinear
    k = 'model.layers.0.self_attn.k_proj'
    W = mods['0.self_attn.k_proj'].weight.data
    ql = QuantizedLinear(W.shape[1], W.shape[0], gi, 1, 1, nb, bias=False, dtype=torch.float32)
    ql.codes.data = f.get_tensor(k + '.codes')
    ql.codebooks.data = f.get_tensor(k + '.codebooks').float()
    ql.scales.data = f.get_tensor(k + '.scales').float()
    x = torch.randn(4, W.shape[1])
    with torch.no_grad():
        y = ql(x)
    err = ((y - x @ W.T).abs().max() / y.abs().max()).item()
    assert err < 1e-4, err
    print(f'decode matches the aqlm kernel: rel err {err:.1e}', flush=True)
t1 = time.time()
ppl = M.perplexity(model, M.wikitext_ids(tok, 'test'), a.evlen, a.nwin, bs=max(1, 2048 // a.evlen))
row = {'model': a.model, 'spec': f'aqlm:{pathlib.Path(a.ckpt).name},1x{nb},g{gi}', 'bpw': bits / n, 'bpw_codes': nb / gi, 'ppl': ppl,
       'eval_s': round(time.time() - t1, 1), 'nwin': a.nwin, 'evlen': a.evlen,
       'maxrss_gb': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2 ** 30, 'time': time.strftime('%Y-%m-%d %H:%M:%S')}
print(json.dumps(row), flush=True)
with open(a.out, 'a') as fo:
    fo.write(json.dumps(row) + '\n')
