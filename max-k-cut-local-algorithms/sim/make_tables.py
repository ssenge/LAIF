"""Markdown tables for the README from lv_certified.jsonl and hybrid_params.json.
Classical lower bound: empirical Bernstein at confidence 1 - 1e-4 (Maurer-Pontil), from the sample
mean and variance of the 0/1 cut indicator. Previous values from 2609.39042, Tables 4 and 5
(QAOA and Local Vector, rounded to three digits there)."""
import json, math

# (k, d) -> {girth: (LV, QAOA)} from 2609.39042, girth = 2p + 2
PREV = {
    (3, 4): {6: (.930, .891), 8: (.944, .921), 10: (.949, .940), 12: (.954, .952), 14: (.957, .961),
             16: (.960, .968), 18: (.962, .973), 20: (.963, .977), 22: (.964, .980)},
    (3, 6): {6: (.888, .851), 8: (.902, .878), 10: (.909, .895), 12: (.915, .907), 14: (.918, .917),
             16: (.921, .924), 18: (.923, .930), 20: (.924, .934), 22: (.925, .938)},
    (3, 8): {6: (.861, .827), 8: (.875, .851), 10: (.882, .867), 12: (.887, .878), 14: (.890, .887),
             16: (.893, .894), 18: (.895, .899), 20: (.896, .904), 22: (.897, .908)},
    (4, 4): {6: (.980, .953), 8: (.986, .977), 10: (.989, .988), 12: (.991, .993), 14: (.990, .996),
             16: (.991, .998), 18: (.992, .999)},
    (4, 8): {6: (.933, .903), 8: (.943, .925), 10: (.949, .939), 12: (.952, .949), 14: (.953, .956),
             16: (.955, .961), 18: (.956, .966)},
}
L = math.log(2 / 1e-4)


def bernstein(mean, se, n):
    var = se * se * n
    return mean - math.sqrt(2 * var * L / n) - 7 * L / (3 * (n - 1))


cl = [json.loads(l) for l in open("lv_certified.jsonl")]
cl.sort(key=lambda r: (r["k"], r["d"], r["girth"]))
print("| k | d | girth | Previous best bound [1] | Local Vector + one round, lower bound | mean ± s.e. |")
print("|---|---|---|---|---|---|")
for r in cl:
    lv, qa = PREV[(r["k"], r["d"])].get(r["girth"], (None, None))
    prev = f"{max(lv, qa):.3f} ({'QAOA' if qa >= lv else 'LV'})" if lv else "not tabulated"
    lb = bernstein(r["mean"], r["se"], r["samples"])
    mark = "**" if lv and lb > max(lv, qa) else ""
    print(f"| {r['k']} | {r['d']} | {r['girth']} | {prev} | {mark}{lb:.4f}{mark} | {r['mean']:.4f} ± {r['se']:.4f} |")

print()
print("| k | d | girth | QAOA [1], depth (girth−2)/2 | QAOA, depth (girth−4)/2, plus one round |")
print("|---|---|---|---|---|")
for h in json.load(open("hybrid_params.json")):
    lv, qa = PREV[(h["k"], h["d"])][h["girth"]]
    print(f"| {h['k']} | {h['d']} | {h['girth']} | {qa:.3f} | **{h['cut']:.4f}** |")
