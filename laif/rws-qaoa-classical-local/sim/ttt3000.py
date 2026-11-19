"""Single-core wall time to reach a target cut fraction FRAC (cut >= ceil(FRAC |E|)) on random 3-regular graphs, the target
of the runtime comparison of arXiv:2603.10191 Sec. II E, by three classical routes:
  warm   RWS warm start (coordinate ascent, best of M = 100 starts, as there) + radius-6 rule (3 rounds), the two times
         separate; and the restart variant: M = 1 warm start + rule, new seed per restart, until the target (cumulative time)
  SA     annealing from a random state, T from 1.5 to 0.05, doubling sweep ladder from 125; time of the first run that
         reaches the target, the cumulative ladder time, and the time at which that run first reaches it (linear in sweeps)
  X      the warm start of M = 100 with polarized spins fixed and the rest solved exactly (c2_x.X), time after the warm start
  BM     MQLib BURER2002 (bin path as argv), runtime limit LIM s; time of the first history entry at or above the target
REP repetitions per graph (seeds 0..REP-1). Wall time (perf_counter) and process CPU time (user + sys) per step; each
graph's batch starts once the 1-minute load average is below 10.
Usage: python -I ttt3000.py N graphs REP mqlib_bin LIM out.jsonl FRAC"""
import os, sys, time, json, math, subprocess, tempfile, resource
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from numba import njit
from rws_local import graph, rws_ca, rounds, cut
from c2_x import X

@njit(cache=True)
def sa_hit(nb, s, sweeps, T0, T1, seed, target):
    """rws_main.sa with the sweep index at which the cut first reaches target (-1 if never)."""
    np.random.seed(seed); s = s.copy(); N = nb.shape[0]; c = cut(nb, s); best = c; hit = -1
    for t in range(sweeps):
        T = T0 * (T1 / T0) ** (t / max(1, sweeps - 1))
        for _ in range(N):
            i = np.random.randint(N); g = 0
            for k in range(3): g += 1 if s[nb[i, k]] == s[i] else -1
            if g >= 0 or np.random.random() < np.exp(g / T):
                s[i] = -s[i]; c += g
                if c > best: best = c
        if hit < 0 and best >= target: hit = t
    return best, hit

def bm(binpath, nb, seed, lim, target):
    """MQLib BURER2002 for lim s; best cut, wall time of the first history entry at or above target (MQLib's own clock),
    and the CPU/wall ratio of the whole run (child rusage), so cpu-to-target ~ wall-to-target * ratio."""
    N = nb.shape[0]; E = [(i, j) for i in range(N) for j in nb[i] if j > i]
    with tempfile.NamedTemporaryFile("w", suffix=".txt", delete=False) as f:
        f.write(f"{N} {len(E)}\n" + "".join(f"{i + 1} {j + 1} 1\n" for i, j in E)); fn = f.name
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN); w0 = time.perf_counter()
    out = subprocess.run([binpath, "-fM", fn, "-h", "BURER2002", "-r", str(lim), "-s", str(seed)], capture_output=True, text=True).stdout
    w = time.perf_counter() - w0; r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    cpu = (r1.ru_utime - r0.ru_utime) + (r1.ru_stime - r0.ru_stime)
    os.unlink(fn); line = out.strip().splitlines()[-1]; hist = line[line.rindex("[") + 1:line.rindex("]")]
    pts = [(float(v), float(t)) for v, t in (p.split(":") for p in hist.split(";"))]
    hits = [t for v, t in pts if v >= target - 1e-9]
    return max(v for v, _ in pts), (min(hits) if hits else None), cpu / w

def clk(): return np.array([time.perf_counter(), time.process_time()])   # wall, process CPU (user + sys)

def main(N, ng, REP, binpath, lim, out, frac, maxload=10.0):
    _, nbw = graph(200, 99); s = np.ones(200, np.int64)           # compile once, untimed
    rws_ca(nbw, 0.6, 1, 0); rounds(nbw, s, 3, 0); sa_hit(nbw, s, 2, 1.5, 0.05, 0, 10 ** 9)
    with open(out, "a") as f:
        for g in range(ng):
            while os.getloadavg()[0] >= maxload: time.sleep(60)   # each graph's batch starts at 1-minute load < maxload
            load0 = os.getloadavg()[0]
            G, nb = graph(N, g); ne = G.number_of_edges(); tgt = math.ceil(frac * ne)
            for r in range(REP):
                rec = dict(N=N, graph=g, rep=r, target=tgt, edges=ne, load_start=load0)
                c0 = clk(); m, _ = rws_ca(nb, 0.6, 100, 1000 * g + r); c1 = clk()
                s0 = np.where(m > 0, 1, -1).astype(np.int64); _, h, _ = rounds(nb, s0, 3, r); c2 = clk()
                rec.update(warm100_cut=int(h[3]), warm100_hit=bool(h[3] >= tgt), t_warm100=(c1 - c0)[0], cpu_warm100=(c1 - c0)[1],
                           t_rule=(c2 - c1)[0], cpu_rule=(c2 - c1)[1])
                c3 = clk(); cx = X(G, m, 0.0)[0]; c4 = clk()
                rec.update(X_cut=int(cx), X_hit=bool(cx >= tgt), t_X=(c4 - c3)[0], cpu_X=(c4 - c3)[1])
                c0 = clk(); k = 0
                while True:
                    m, _ = rws_ca(nb, 0.6, 1, 10 ** 6 * (g + 1) + 1000 * r + k); s0 = np.where(m > 0, 1, -1).astype(np.int64)
                    _, h, _ = rounds(nb, s0, 3, k); k += 1
                    if h[3] >= tgt or k == 1000: break
                c1 = clk(); rec.update(restart_k=k, restart_hit=bool(h[3] >= tgt), t_restart=(c1 - c0)[0], cpu_restart=(c1 - c0)[1])
                s_init = np.where(np.random.default_rng(1000 * g + r).random(N) < 0.5, 1, -1).astype(np.int64); sw = 125; cum = np.zeros(2)
                while sw <= 64000:
                    c0 = clk(); b, hit = sa_hit(nb, s_init, sw, 1.5, 0.05, 1000 * g + r, tgt); d = clk() - c0; cum += d
                    if b >= tgt:
                        rec.update(SA_sweeps=sw, t_SA_run=d[0], cpu_SA_run=d[1], t_SA_cum=cum[0], cpu_SA_cum=cum[1],
                                   t_SA_first=d[0] * (hit + 1) / sw, cpu_SA_first=d[1] * (hit + 1) / sw); break
                    sw *= 2
                if binpath != "-":
                    v, th, ratio = bm(binpath, nb, r, lim, tgt)
                    rec.update(BM_best=v, t_BM=th, BM_cpu_per_wall=ratio, cpu_BM=None if th is None else th * ratio)
                rec["load_end"] = os.getloadavg()[0]
                f.write(json.dumps({k: (float(v) if isinstance(v, np.floating) else v) for k, v in rec.items()}) + "\n"); f.flush()
                print(json.dumps({k: (float(v) if isinstance(v, np.floating) else v) for k, v in rec.items()}), flush=True)

if __name__ == "__main__":
    if sys.argv[1] == "test":                                      # sa_hit agrees with rws_main.sa; MQLib reads the graph file
        from rws_main import sa
        _, nb = graph(300, 0); s = np.where(np.random.default_rng(0).random(300) < 0.5, 1, -1).astype(np.int64)
        assert sa_hit(nb, s, 200, 1.5, 0.05, 3, 10 ** 9)[0] == sa(nb, s, 200, 1.5, 0.05, 3)[0]
        if len(sys.argv) > 2:
            v, t, ratio = bm(sys.argv[2], nb, 0, 0.5, 0); assert 0 < ratio <= 1.05 and t is not None and v <= 450 and v >= 0.9 * 450, (v, t)
        print("ttt3000 self-checks passed"); sys.exit()
    main(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], float(sys.argv[5]), sys.argv[6], float(sys.argv[7]))
