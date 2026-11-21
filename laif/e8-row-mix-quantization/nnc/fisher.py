"""Diagonal empirical Fisher of the LM loss w.r.t. every target weight: the mean of squared gradients over
the calibration windows (WikiText-2 train, the windows that also give H). Cached per model, keyed by the
bytes of each weight, so a method that only sees W can look up its Fisher.
python -m nnc.fisher smollm"""
import hashlib, subprocess, sys
import torch

_F = {}


def key(W):
    return hashlib.sha1(W.detach().float().contiguous().numpy().tobytes()).hexdigest()


def compute(name, nsamples=32, seqlen=512, parts=1):
    """parts > 1: gradients of one slice of the layers per pass, result stored in bfloat16 (both: memory)."""
    import torch.nn.functional as Fn
    from . import models as M, pipeline as P
    model, tok = M.load_llm(name)
    mods = list(P.targets(model, 'llm').values())
    keys = [key(m.weight) for m in mods]
    for p in model.parameters():
        p.requires_grad_(False)
    wins = P._calib_llm(tok, nsamples, seqlen)
    out = {}
    for s in range(parts):
        part = list(range(len(mods)))[s::parts]
        for j in part:
            mods[j].weight.requires_grad_(True)
        F = {j: torch.zeros_like(mods[j].weight) for j in part}
        for x in wins:
            model.zero_grad(set_to_none=True)
            lg = model(x[None]).logits[0, :-1]
            Fn.cross_entropy(lg, x[1:]).backward()  # per-window gradient: empirical Fisher over windows
            for j in part:
                F[j] += mods[j].weight.grad ** 2 / len(wins)
        for j in part:
            mods[j].weight.requires_grad_(False)
            mods[j].weight.grad = None
        if parts == 1:
            out = {keys[j]: F[j] for j in part}
        else:  # each slice goes to disk at once, merged after the model is freed
            torch.save({keys[j]: F[j].to(torch.bfloat16) for j in part}, P.CACHE / f'{name}_fisher_{nsamples}.part{s}.pt')
        del F
    del model, mods
    if parts > 1:
        for s in range(parts):
            f = P.CACHE / f'{name}_fisher_{nsamples}.part{s}.pt'
            out.update(torch.load(f))
            f.unlink()
    torch.save(out, P.CACHE / f'{name}_fisher_{nsamples}.pt')


def compute_embed(name, nsamples=32, seqlen=512):
    """Diagonal empirical Fisher of the (tied) input embedding over the calibration windows; own cache file."""
    import torch.nn.functional as Fn
    from . import models as M, pipeline as P
    model, tok = M.load_llm(name)
    for p in model.parameters():
        p.requires_grad_(False)
    E = model.get_input_embeddings().weight
    E.requires_grad_(True)
    F = torch.zeros_like(E)
    wins = P._calib_llm(tok, nsamples, seqlen)
    for x in wins:
        model.zero_grad()
        Fn.cross_entropy(model(x[None]).logits[0, :-1], x[1:]).backward()
        F += E.grad ** 2 / len(wins)
    torch.save(F, P.CACHE / f'{name}_fisher_embed_{nsamples}.pt')


def split(name, nsamples=32):
    """Store a model's Fisher as one file per decoder layer (dir {name}_fisher_{n}.d, index key -> layer), so a
    layer-by-layer run holds one layer's Fisher instead of the whole model's.  python -m nnc.fisher qwen15 split"""
    from . import models as M, pipeline as P
    model, _ = M.load_llm(name)
    layer = {key(m.weight): n.split('.')[0] for n, m in P.targets(model, 'llm').items()}
    del model
    F = torch.load(P.CACHE / f'{name}_fisher_{nsamples}.pt')
    assert F.keys() == layer.keys()
    d = P.CACHE / f'{name}_fisher_{nsamples}.d'
    d.mkdir(exist_ok=True)
    for L in sorted(set(layer.values()), key=int):
        torch.save({k: F[k] for k in F if layer[k] == L}, d / f'{L}.pt')
    torch.save(layer, d / 'index.pt')
    (P.CACHE / f'{name}_fisher_{nsamples}.pt').unlink()


def lookup(W):
    """Fisher of W from the cache; on a miss, compute it (in a child process: memory) for each known LLM.
    Split caches (*.d) are read one layer file at a time; the previous layer's entries are dropped."""
    from . import models as M, pipeline as P
    k = key(W)
    if k not in _F:
        for d in P.CACHE.glob('*_fisher_32.d'):
            idx = torch.load(d / 'index.pt')
            if k in idx:
                _F.clear()
                _F.update(torch.load(d / f'{idx[k]}.pt'))
                return _F[k]
    if k not in _F:  # cached models first: a miss must not compute the Fisher of unrelated models
        for f in sorted(P.CACHE.glob('*_fisher_32.pt'), key=lambda f: -f.stat().st_mtime):  # newest first
            _F.update(torch.load(f))
            if k in _F:  # stop early: each file holds a whole model (GBs)
                break
    for name in M.LLMS:
        if k in _F:
            break
        f = P.CACHE / f'{name}_fisher_32.pt'
        if not f.exists():
            subprocess.run([sys.executable, '-m', 'nnc.fisher', name], check=True, cwd=M.ROOT)
        _F.update(torch.load(f))
    return _F[k]


if __name__ == '__main__':
    torch.set_num_threads(int(__import__('os').environ.get('NNC_THREADS', 1)))
    if sys.argv[2:] == ['embed']:
        compute_embed(sys.argv[1])
    elif sys.argv[2:] == ['split']:
        split(sys.argv[1])
    else:  # python -m nnc.fisher qwen15 [parts]
        compute(sys.argv[1], parts=int(sys.argv[2]) if len(sys.argv) > 2 else 1)
