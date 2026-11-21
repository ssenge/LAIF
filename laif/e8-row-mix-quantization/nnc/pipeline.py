"""Calibrate, compress every target layer with one spec, evaluate, log a JSON line.

python -m nnc.pipeline --model smollm --specs 'rtn:b=4,g=128' 'tt:bpw=4,d=3' --out runs/smollm.jsonl
"""
import argparse, json, math, os, resource, sys, time
import torch
import torch.nn as nn
import torch.nn.functional as F
from . import compress as C
from . import models as M

CACHE = M.ROOT / 'runs' / 'cache'


def targets(model, kind):
    if kind == 'llm':
        return {n: m for n, m in model.model.layers.named_modules() if isinstance(m, nn.Linear)}
    mods = [(n, m) for n, m in model.named_modules() if isinstance(m, (nn.Linear, nn.Conv2d))]
    return dict(mods[1:-1])  # first and last layers stay dense, as usual


@torch.no_grad()
def calibrate(model, mods, batches, with_sink=False):
    """H = E[x x^T] per target layer. Layers fed the same tensor object in a row (q/k/v, gate/up) share
    one H object; the previous input is held so its memory cannot be reused by another tensor."""
    H, cnt, alias, last = {n: None for n in mods}, {n: 0 for n in mods}, {}, [None, None]

    def hook(name, m):
        def f(_, inp, __):
            x = inp[0].detach()
            if x.dim() == 3 and sink is not None and name in sink:  # first position of each sequence, kept apart
                x0 = x[:, 0].float()
                sink[name] = x0.T @ x0 if sink[name] is None else sink[name].add_(x0.T @ x0)
            if inp[0] is last[0] and not isinstance(m, nn.Conv2d):
                alias[name] = last[1]
                return
            last[0], last[1] = inp[0], name
            x = x.float()
            if isinstance(m, nn.Conv2d):
                x = F.unfold(x, m.kernel_size, m.dilation, m.padding, m.stride).transpose(1, 2)
            x = x.reshape(-1, x.shape[-1])
            h = x.T @ x
            H[name] = h if H[name] is None else H[name].add_(h)
            cnt[name] += x.shape[0]
        return f

    sink = {n: None for n in mods if 'v_proj' in n or with_sink == 'all'} if with_sink else None  # v_proj only by default: memory
    hs = [m.register_forward_hook(hook(n, m)) for n, m in mods.items()]
    for b in batches:
        model(b)
        last[0] = None
    for h in hs:
        h.remove()
    for n in mods:
        if H[n] is not None:
            H[n].div_(cnt[n])
    for n, src in alias.items():
        H[n] = H[src]
    if with_sink:
        return H, {n: sink[n].div_(len(batches)) for n in sink}
    return H


def setup(name, nsamples=32, seqlen=512, sink=(3.0, 0.02), evlen=512, need_H=True):
    """Model, target layers, cached H, evaluation closure, and the bit count of the parts left at 16 bits."""
    torch.manual_seed(0)
    if name in M.LLMS:
        model, tok = M.load_llm(name)
        kind = 'llm'
        test = M.wikitext_ids(tok, 'test')
        evaluate = lambda n=None: {'ppl': M.perplexity(model, test, evlen, n, bs=max(1, 2048 // evlen))}
        mk_batches = lambda: [ids[None] for ids in _calib_llm(tok, nsamples, seqlen)]
    else:
        model = M.load_vision(name)
        kind = 'vision'
        (xtr, _), (xte, yte) = M.vision_data(name)
        evaluate = lambda n=None: {'acc': M.accuracy(model, xte, yte)}
        mk_batches = lambda: list(xtr[torch.randperm(len(xtr))[:2048]].split(256))
    mods = targets(model, kind)
    CACHE.mkdir(parents=True, exist_ok=True)
    cf = CACHE / f'{name}_H_{nsamples}.pt'
    sf = CACHE / f'{name}_Hsink_{nsamples}.pt'
    if not need_H:  # sequential mode calibrates each layer itself; the full H of a 1.5B model is ~10 GB
        H, Hs = None, None
    elif cf.exists() and (kind != 'llm' or sf.exists()):
        H = torch.load(cf)
        Hs = torch.load(sf) if kind == 'llm' else None
    elif kind == 'llm':
        H, Hs = calibrate(model, mods, mk_batches(), with_sink=True)
        torch.save(H, cf); torch.save(Hs, sf)
    else:
        H, Hs = calibrate(model, mods, mk_batches()), None
        torch.save(H, cf)
    if Hs is not None and any(sink):
        # first-token (attention sink) statistics get extra weight: beta_v for v_proj, beta_o elsewhere
        H = {n: H[n] + (sink[0] if 'v_proj' in n else sink[1]) * Hs[n] if n in Hs else H[n] for n in mods}
    tot = sum(p.numel() for p in model.parameters())
    tgt = sum(m.weight.numel() for m in mods.values())
    return model, mods, H, evaluate, (tot - tgt) * C.FP


@torch.no_grad()
def sequential(model, mods, batches, spec, orig, sink=(3.0, 0.02)):
    """Compress decoder layer by layer. Each layer's H comes from inputs that already passed through the
    compressed earlier layers, so later layers see (and compensate) the earlier errors."""
    layers = model.model.layers
    xs, kw = [], {}

    class Stop(Exception):
        pass

    def catch(_, args, kwargs):
        xs.append(args[0] if args else kwargs.pop('hidden_states'))
        # no KV cache: repeated layer calls would otherwise attend to keys of earlier batches
        kw.update({k: v for k, v in kwargs.items() if k not in ('hidden_states', 'past_key_values', 'use_cache')})
        raise Stop

    h = layers[0].register_forward_pre_hook(catch, with_kwargs=True)
    for b in batches:
        try:
            model(b, use_cache=False)
        except Stop:
            pass
    h.remove()
    fn, fkw = C.parse(spec)
    bits, n, errs = 0, 0, []
    for li, layer in enumerate(layers):
        sub = {k: m for k, m in mods.items() if k.split('.')[0] == str(li)}
        H, Hs = calibrate(lambda x: layer(x, **kw), sub, xs, with_sink='all')
        for name, m in sub.items():
            Hn = H[name] + (sink[0] if 'v_proj' in name else sink[1]) * Hs[name]
            W = orig[name]
            Wh, b = fn(W, Hn, **fkw)
            errs.append(C.werr(W, Wh, Hn))
            m.weight.data.copy_(Wh)
            bits += b
            n += W.numel()
        xs = [layer(x, **kw) for x in xs]
    if spec == 'none':  # self-check: the layer-by-layer stream reproduces the full model
        ref = model.model(batches[0], use_cache=False).last_hidden_state
        out = model.model.norm(xs[0])
        assert torch.allclose(out, ref, atol=1e-3, rtol=1e-3), (out - ref).abs().max()
    return bits, n, sum(errs) / len(errs)


def quant_embed(model, b, g=128):
    """RTN on the input embedding (tied with the output head in SmolLM2 and Qwen2.5); returns bits saved."""
    E = model.get_input_embeddings().weight
    Eq, bits = C.rtn(E.data, None, b, g)
    E.data.copy_(Eq)
    return E.numel() * C.FP - bits


def quant_embed_mix(model, name, bpw, widths=(2, 3, 4, 5, 6, 8), g=128):
    """Per-row (per-token) widths for the tied embedding: RTN at each width, row error weighted by the
    embedding's diagonal Fisher, one slope chosen by bisection so the total bits (codes, scales, a width tag
    per row) stay within bpw per weight. Returns bits saved against 16-bit."""
    E = model.get_input_embeddings().weight
    V, d = E.shape
    F = torch.load(CACHE / f'{name}_fisher_embed_32.pt').double()  # python -m nnc.fisher <name> embed
    runs = [C.rtn(E.data, None, b, g) for b in widths]
    D = torch.stack([((E.data - Q).double() ** 2 * F).sum(1) for Q, _ in runs], 1)
    over = runs[0][1] - V * d * widths[0] + V * math.ceil(math.log2(len(widths)))
    w = torch.tensor(widths, dtype=torch.float64)
    pick = lambda lam: (D + lam * d * w).argmin(1)
    total = lambda k: over + int(w[k].sum().item()) * d
    lo, hi = 1e-30, 1.0  # a larger slope never uses more bits
    while total(pick(hi)) > bpw * V * d:
        hi *= 10
    for _ in range(100):
        mid = (lo * hi) ** 0.5
        lo, hi = (lo, mid) if total(pick(mid)) <= bpw * V * d else (mid, hi)
    k = pick(hi)
    E.data.copy_(torch.stack([Q for Q, _ in runs])[k, torch.arange(V)])
    bits = total(k)
    assert bits <= bpw * V * d
    print(json.dumps({'embed_bpw': bits / (V * d), 'widths': {b: int((k == j).sum()) for j, b in enumerate(widths)}}), flush=True)
    return E.numel() * C.FP - bits


def _calib_llm(tok, n, seqlen):
    ids = M.wikitext_ids(tok, 'train')
    g = torch.Generator().manual_seed(0)
    starts = torch.randint(0, len(ids) - seqlen, (n,), generator=g)
    return [ids[s:s + seqlen] for s in starts]


def apply(mods, H, spec, orig):
    fn, kw = C.parse(spec)
    bits, n, errs = 0, 0, []
    for name, m in mods.items():
        W = orig[name]
        W2 = W.reshape(W.shape[0], -1)
        Wh, b = fn(W2, H[name], **kw)
        errs.append(C.werr(W2, Wh, H[name]))
        m.weight.data.copy_(Wh.reshape(W.shape))
        bits += b
        n += W2.numel()
    return bits, n, sum(errs) / len(errs)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--model', required=True)
    ap.add_argument('--specs', nargs='+', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--threads', type=int, default=4)
    ap.add_argument('--nwin', type=int, default=None, help='perplexity windows (default all)')
    ap.add_argument('--nsamples', type=int, default=32)
    ap.add_argument('--embed', type=int, default=16, help='bits for the embedding/head (16 = keep)')
    ap.add_argument('--embed-bpw', type=float, default=0.0, help='Fisher-allocated per-token widths for the embedding at this bpw')
    ap.add_argument('--evlen', type=int, default=512, help='perplexity window length (2048: standard protocol)')
    ap.add_argument('--seq', action='store_true', help='sequential layer-by-layer calibration (LLMs)')
    ap.add_argument('--sink', type=float, nargs=2, default=[3.0, 0.02], help='sink weights for v_proj and other layers (0 0 = off)')
    a = ap.parse_args()
    torch.set_num_threads(a.threads); torch.set_num_interop_threads(1)
    model, mods, H, evaluate, rest_bits = setup(a.model, a.nsamples, sink=tuple(a.sink), evlen=a.evlen, need_H=not a.seq)
    if a.embed_bpw:
        rest_bits -= quant_embed_mix(model, a.model, a.embed_bpw)
    elif a.embed < 16:
        rest_bits -= quant_embed(model, a.embed)
    # one spec: the weights need no reset copy (saves a model's worth of memory)
    orig = {n: m.weight.data.clone() if len(a.specs) > 1 else m.weight.data for n, m in mods.items()}
    if a.seq:
        from transformers import AutoTokenizer
        seq_batches = [x[None] for x in _calib_llm(AutoTokenizer.from_pretrained(M.LLMS[a.model]), a.nsamples, 512)]
        H = None  # not used: each layer is calibrated on the fly
    for k, spec in enumerate(a.specs):
        t0 = time.time()
        try:
            if a.seq:
                bits, n, err = sequential(model, mods, seq_batches, spec, orig, tuple(a.sink))
            else:
                bits, n, err = apply(mods, H, spec, orig)
            from . import fisher
            fisher._F.clear()  # memory: the evaluation does not need the Fisher (next spec reloads it)
            t1 = time.time()
            res = evaluate(a.nwin)
        except Exception as e:  # one failing spec must not end a sweep
            print(json.dumps({'model': a.model, 'spec': spec, 'error': repr(e)}), flush=True)
            restart(a.specs[k + 1:])
            continue
        row = {'model': a.model, 'spec': spec, 'sink': a.sink, 'embed': a.embed, 'embed_bpw': a.embed_bpw, 'seq': a.seq, 'bpw': bits / n, 'model_mb': (bits + rest_bits) / 8e6,
               'werr': err, **res, 'compress_s': round(t1 - t0, 1), 'eval_s': round(time.time() - t1, 1),
               'nwin': a.nwin, 'evlen': a.evlen, 'maxrss_gb': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2 ** 30,
               'time': time.strftime('%Y-%m-%d %H:%M:%S')}
        print(json.dumps(row), flush=True)
        with open(a.out, 'a') as f:
            f.write(json.dumps(row) + '\n')
        if not all(math.isfinite(v) for v in res.values()) or not math.isfinite(err):  # also inf: overflowed forward
            restart(a.specs[k + 1:])  # inf/NaN in a forward pass has left later LAPACK calls failing
        for nme, m in mods.items():
            m.weight.data.copy_(orig[nme])


def restart(rest):
    """Continue the sweep in a fresh process image with the remaining specs."""
    if not rest:
        sys.exit(0)
    argv, i = sys.argv[1:], sys.argv.index('--specs')
    j = next((t for t in range(i + 1, len(sys.argv)) if sys.argv[t].startswith('--')), len(sys.argv))
    argv = sys.argv[1:i] + ['--specs', *rest] + sys.argv[j:]
    sys.stdout.flush()
    os.execv(sys.executable, [sys.executable, '-m', 'nnc.pipeline', *argv])

if __name__ == '__main__':
    main()
