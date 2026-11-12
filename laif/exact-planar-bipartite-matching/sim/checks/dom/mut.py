"""Mutate the rules of a private copy of sim/dom.py and see which counters notice. The repo is not touched.
python3 -I -B mut.py SECS [only]"""
import json, os, shutil, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, '..', '..')
DST = os.path.join(HERE, 'simmut')
if os.path.exists(DST):
    shutil.rmtree(DST)
shutil.copytree(SRC, DST)
base = open(os.path.join(SRC, 'dom.py')).read()
M = [
 ('good_le', "if x >= c + 2 and (pb < x or mode == 'nogood'):", "if x >= c + 2 and (pb <= x or mode == 'nogood'):"),
 ('t0_le', "        if A[t] < l:\n            cur = t", "        if A[t] <= l:\n            cur = t"),
 ('first_drop_c', "elif A[t] <= c:", "elif A[t] < c:"),
 ('X_includes_j', "        X[j] = cur\n        if j in first:\n            cur = min(cur, first[j])", "        if j in first:\n            cur = min(cur, first[j])\n        X[j] = cur"),
 ('suf_gt', "if (sa >= j or mode == 'nosuf')", "if (sa > j or mode == 'nosuf')"),
 ('sufB_ge', "(x > sb or mode == 'noM')", "(x >= sb or mode == 'noM')"),
 ('sufB_incl_j', "            sa, sb = min(sa, A[j]), max(sb, B[j])\n    return m", "            sb = max(sb, B[j]); sa = min(sa, A[j])\n            if j > l + 1: pass\n    return m"),  # equivalent, a sanity control: must fire nothing
 ('chain_c2', "C = [j for j in range(l, c + 1) if m[j] > c + 1]", "C = [j for j in range(l, c + 1) if m[j] > c + 2]"),
 ('lam_c2', "if a in m and m[a] > c + 1:\n                cur = a", "if a in m and m[a] > c + 2:\n                cur = a"),
 ('after_c2', "            after[a] = cur\n            if m[a] > c + 1:", "            after[a] = cur\n            if m[a] > c + 2:"),
 ('ring_r1', "m[j0] > r or m[j0] <= m[j1]", "m[j0] > r + 1 or m[j0] <= m[j1]"),
 ('ring_rm1', "m[j0] > r or m[j0] <= m[j1]", "m[j0] >= r or m[j0] <= m[j1]"),
 ('ring_eq', "m[j0] > r or m[j0] <= m[j1]", "m[j0] > r or m[j0] < m[j1]"),
 ('ring_noX', " or t != X[j1]:\n                continue", ":\n                continue"),
 ('past_ge', "past = [j for j in C if m[j] > r]", "past = [j for j in C if m[j] >= r]"),
 ('rest_value', "marks[m[rest[0]]] = J", "marks[m[rest[0]]] = C[0]"),
 ('mark_j1', "marks[pos] = j0", "marks[pos] = j1"),
 ('delta_default', "cur = C[-1] if C else None\n        for t in range(c + 1, r + 1):", "cur = C[0] if C else None\n        for t in range(c + 1, r + 1):"),
 ('off_ab_eq', "    if a == b:\n        return a\n", ""),
 ('off_a0', "    if a == 0:\n        return None\n", ""),
 ('off_nohigher', "    lev += 1\n    while (1 << lev) < k:\n        d = dlt.get((lev, b))", "    lev += 100\n    while (1 << lev) < k:\n        d = dlt.get((lev, b))"),
 ('off_lam_only', "return max(x, y) if mode == 'maxld' else min(x, y)", "return x"),
 ('off_delta_only', "return max(x, y) if mode == 'maxld' else min(x, y)", "return y"),
 ('on_highest', "    lev = 0\n    while (1 << lev) < k:\n        d = dlt.get((lev, t))\n        if d is not None:\n            return d\n        lev += 1\n    return None", "    lev = 0\n    best = None\n    while (1 << lev) < k:\n        d = dlt.get((lev, t))\n        if d is not None:\n            best = d\n        lev += 1\n    return best"),
 ('entry_on_path_dropped', "        if R[t - 1] in E:\n            A[t], B[t] = 0, 0\n", "        pass\n"),
 ('entry_off_path_dropped', "src = [z for z in (E if i == 0 else arcs.get(R[i - 1], ())) if z in left]", "src = [z for z in (() if i == 0 else arcs.get(R[i - 1], ())) if z in left]"),
 ('allow_t1', "if pos[u] != t - 1 and pos[u] != t:", "if pos[u] != t:"),   # equivalent by the note: must fire nothing
 ('B_uses_a', "A[t], B[t] = min(A[t], a[u]), max(B[t], b[u])", "A[t], B[t] = min(A[t], a[u]), max(B[t], a[u])"),
 ('A_uses_b', "A[t], B[t] = min(A[t], a[u]), max(B[t], b[u])", "A[t], B[t] = min(A[t], b[u]), max(B[t], b[u])"),
 ('no_overwrite', "            if d is not None:\n                self.idom[y] = d\n        cls = ", "            if d is not None:\n                self.idom.setdefault(y, d)\n        cls = "),
 ('entries_only_from_R', "if v in cls and cls.get(u) != cls[v]:", "if v in cls and u not in cls:"),
 ('entries_only_from_classes', "if v in cls and cls.get(u) != cls[v]:", "if v in cls and u in cls and cls[u] != cls[v]:"),
 ('entries_forgotten', "        cls = {y: z for z, K in new for y in K}\n        for u in Q:", "        cls = {y: z for z, K in new for y in K}\n        self.ent -= Q\n        for u in Q:"),
 ('literal_outside_class', "        for u in Q:\n            for v in self.arcs.get(u, ()):\n                if v in cls and cls.get(u) != cls[v]:", "        for u in self.arcs:\n            for v in self.arcs.get(u, ()):\n                if v in cls and cls.get(u) != cls[v]:"),
 ('small_only_root', "for e in ({x} if self.mode == 'noentry' else self.ent & K):", "for e in {x}:"),
]
secs = float(sys.argv[1])
only = set(sys.argv[2:])
for name, old, new in M:
    if only and name not in only:
        continue
    if base.count(old) < 1:
        print(json.dumps({'mut': name, 'error': 'pattern missing'}), flush=True)
        continue
    text = base.replace(old, new) if name in ('xxx',) else base.replace(old, new, 1)
    open(os.path.join(DST, 'dom.py'), 'w').write(text)
    try:
        p = subprocess.run([sys.executable, '-I', '-B', os.path.join(DST, 'dom.py'), '77', str(secs)], capture_output=True, text=True, timeout=secs * 4 + 60)
    except subprocess.TimeoutExpired:
        print(json.dumps({'mut': name, 'error': 'timeout'}), flush=True)
        continue
    if p.returncode != 0:
        print(json.dumps({'mut': name, 'crash': p.stderr.strip().splitlines()[-1][:120]}), flush=True)
        continue
    d = json.loads(p.stdout.strip().splitlines()[-1])
    print(json.dumps({'mut': name, 'runs': d.get('runs'), 'fails': {k: v for k, v in d.items() if k.startswith('FAIL')}}), flush=True)
