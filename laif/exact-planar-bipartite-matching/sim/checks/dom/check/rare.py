import sys, random, collections, time
sys.path.insert(0, sys.argv[1])
import dom
rng = random.Random(int(sys.argv[2])); st = collections.Counter(); t0 = time.time()
while time.time() - t0 < float(sys.argv[3]):
    dom.run_one(rng, st, False)
print({k: st[k] for k in ('runs','n.star_marks','n.past_marks','chk.m','max.k','max.chain','FAIL.tree')}, 'fam.jumps', st['fam.jumps'], 'fam.nest', st['fam.nest'])
