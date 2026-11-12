import collections, json, math, os, random, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import stress_eng as eng

for n in (200, 400, 1000, 4000, 16000):
    out, chain, h, sizes = eng.ears(n)
    assert eng.planar_ok(out)
    V = set(out) | {v for vs in out.values() for v in vs}
    assert len(V) == n, (len(V), n)
    sq, sl = eng.ears_scripts(chain, h, out)
    adv = eng.Adv(k1=0, k2=0, script_q=sq, script_l=sl, check_every=1.0 if n <= 1000 else 0.05)
    st = collections.Counter()
    log = []
    rng = random.Random(1)
    res = eng.solve(out, [0], rng, st, adv, log=log, maxlevels=1)
    passes = [l for l in log if l[0] == 'pass']
    print(json.dumps({'n': n, 'T': len(chain), 'bound': round(math.log(n, 4 / 3) + 2, 2), 'passes_top_level': st['max.passes_per_level'], 'step4': st['n.step4'], 'step3': st['n.step3'],
                      'L': [p[4] for p in passes][:30], 'fails': {k: v for k, v in st.items() if k.startswith('FAIL')}}), flush=True)
    if n == 200:
        print(sorted((u, v) for u in out for v in out[u]))
