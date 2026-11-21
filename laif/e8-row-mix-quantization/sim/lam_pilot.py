"""Pick the global gmix slope lam for a target bpw from a sample of decoder layers (GPTQ runs cached per
module, so every lam on the grid reuses them; so is the E8P run of e8=1).
python sim/lam_pilot.py qwen15 2.5 'refit=1'     (several targets: 2.0,2.25,2.5)"""
import sys, pathlib, math
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
import torch
from nnc import compress as C, models as M, pipeline as P


def main():
    name, targets = sys.argv[1], [float(t) for t in sys.argv[2].split(',')]
    extra = sys.argv[3] if len(sys.argv) > 3 else 'refit=1'
    torch.set_num_threads(2)
    model, tok = M.load_llm(name)
    mods = P.targets(model, 'llm')
    nl = len(model.model.layers)
    layers = sorted({0, nl // 4, nl // 2, 3 * nl // 4, nl - 1})
    sub = {k: m for k, m in mods.items() if int(k.split('.')[0]) in layers}
    batches = [x[None] for x in P._calib_llm(tok, 32, 512)]
    H, Hs = P.calibrate(model, sub, batches, with_sink=True)
    Ws = {k: m.weight.data.clone() for k, m in sub.items()}
    del model, mods, sub  # memory: the model is not needed for the GPTQ runs
    import gc; gc.collect()
    grid = [10 ** (-7 + 0.125 * k) for k in range(33)]  # 1e-7 .. 1e-3
    bits, n = [0.0] * len(grid), 0
    real, real_q = C.gptq, C.quip
    for name_, W in Ws.items():
        Hn = H[name_] + 3.0 * Hs[name_] if name_ in Hs else H[name_]  # Qwen sink weights (3.0, 0.0)
        memo = {}

        def cached(W_, H_, b, g, *a, **kw):  # gptq calls itself positionally once (rotation): own key
            k = (b, g, len(a))
            if k not in memo:
                memo[k] = real(W_, H_, b, g, *a, **kw)
            return memo[k]
        def cached_q(W_, H_, **kw):
            if 'q' not in memo:
                memo['q'] = real_q(W_, H_, **kw)
            return memo['q']
        C.gptq, C.quip = cached, cached_q
        for t, lam in enumerate(grid):
            fn, kw = C.parse(f'gmix:lam={lam:.3e},{extra}')
            bits[t] += fn(W, Hn, **kw)[1]
        C.gptq, C.quip = real, real_q
        n += W.numel()
        print(name_, flush=True)
    bpw = [b / n for b in bits]
    for lam, b in zip(grid, bpw):
        print(f'lam={lam:.3e} bpw={b:.3f}')
    assert all(x >= y - 1e-9 for x, y in zip(bpw, bpw[1:])), 'bpw must fall as lam grows'
    for target in targets:
        k = next((t for t in range(1, len(grid)) if bpw[t] <= target), None)  # log-linear interpolation
        if k is None:
            print(f'target {target}: not reached (min bpw {bpw[-1]:.3f})')
            continue
        f = (bpw[k - 1] - target) / (bpw[k - 1] - bpw[k])
        lam = 10 ** (math.log10(grid[k - 1]) + f * (math.log10(grid[k]) - math.log10(grid[k - 1])))
        print(f'target {target}: lam={lam:.3e}')


if __name__ == '__main__':
    main()
