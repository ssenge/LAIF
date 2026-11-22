"""Solve one MILP with SCIP (single thread, default settings) and record the branch-and-bound tree:
node number, parent, depth for every solved node, plus times. Then CP-SAT with one worker on the same LP file.
Usage: measure.py file.lp[.xz] timelimit out.jsonl"""
import sys, os, json, time, lzma, tempfile
import numpy as np
from pyscipopt import Model, Eventhdlr, SCIP_EVENTTYPE

class Tree(Eventhdlr):
    def __init__(self):
        self.rows, self.t0, self.t_root = [], None, None
    def eventinit(self):
        self.model.catchEvent(SCIP_EVENTTYPE.NODESOLVED, self)
    def eventexit(self):
        self.model.dropEvent(SCIP_EVENTTYPE.NODESOLVED, self)
    def eventexec(self, event):
        n = event.getNode()
        p = n.getParent()
        self.rows.append((n.getNumber(), p.getNumber() if p is not None else 0, n.getDepth()))
        if self.t_root is None:
            self.t_root = self.model.getSolvingTime()

def plain_lp(path):
    if path.endswith(".xz"):
        fd, tmp = tempfile.mkstemp(suffix=".lp"); os.write(fd, lzma.open(path).read()); os.close(fd)
        return tmp
    return path

def scip(lp, tl):
    m = Model(); m.hideOutput()
    m.setParam("limits/time", tl); m.setParam("parallel/maxnthreads", 1); m.setParam("lp/threads", 1)
    m.readProblem(lp)
    h = Tree(); m.includeEventhdlr(h, "tree", "records solved nodes")
    t0 = time.time(); m.optimize(); wall = time.time() - t0
    rows = np.array(h.rows, dtype=np.int64).reshape(-1, 3)
    return {"status": m.getStatus(), "obj": m.getObjVal() if m.getNSols() else None, "nodes": m.getNNodes(),
            "maxdepth": m.getMaxDepth(), "time": m.getSolvingTime(), "wall": wall, "t_root": h.t_root,
            "presolve_time": m.getPresolvingTime(), "lp_iters": m.getNLPIterations(), "nvars": m.getNVars(), "nconss": m.getNConss()}, rows

def cpsat(lp, tl):
    from ortools.linear_solver.python import model_builder as mb
    m = Model(); m.hideOutput(); m.readProblem(lp)
    fd, mps = tempfile.mkstemp(suffix=".mps"); os.close(fd); m.writeProblem(mps, verbose=False)
    mdl = mb.Model()
    if not mdl.import_from_mps_file(mps):
        return {"status": "import_failed"}
    s = mb.Solver("SAT")
    s.set_time_limit_in_seconds(tl)
    s.set_solver_specific_parameters("num_workers:1")
    t0 = time.time(); st = s.solve(mdl); wall = time.time() - t0
    os.remove(mps)
    return {"status": str(st), "obj": s.objective_value if st in (mb.SolveStatus.OPTIMAL, mb.SolveStatus.FEASIBLE) else None, "wall": wall}

def subtrees(rows, h):
    """Subtree sizes and heights below the frontier at depth h (nodes at depth h are subtree roots)."""
    num, par, dep = rows[:, 0], rows[:, 1], rows[:, 2]
    idx = {int(n): i for i, n in enumerate(num)}
    root_of = np.full(len(num), -1)
    order = np.argsort(dep, kind="stable")
    for i in order:
        if dep[i] < h:
            continue
        if dep[i] == h:
            root_of[i] = i
        else:
            j = idx.get(int(par[i]))
            root_of[i] = root_of[j] if j is not None else -1
    out = {}
    for i in np.where(root_of >= 0)[0]:
        r = int(root_of[i]); s = out.setdefault(r, [0, 0]); s[0] += 1; s[1] = max(s[1], int(dep[i]) - h)
    return [tuple(v) for v in out.values()], int((dep < h).sum())

if __name__ == "__main__":
    path, tl, outp = sys.argv[1], float(sys.argv[2]), sys.argv[3]
    lp = plain_lp(path)
    res, rows = scip(lp, tl)
    res["file"] = os.path.basename(path)
    res["solved_nodes_recorded"] = int(len(rows))
    hy = {}
    for h in [0, 2, 4, 6, 8, 10, 12]:
        st, top = subtrees(rows, h)
        if not st:
            break
        sizes = np.array([s for s, _ in st], float); heights = np.array([max(d, 1) for _, d in st], float)
        hy[h] = {"n_sub": len(st), "top_nodes": top, "sum_sqrt_Td": float(np.sqrt(sizes * heights).sum()),
                 "max_sqrt_Td": float(np.sqrt(sizes * heights).max()), "covered": int(sizes.sum())}
    res["frontier"] = hy
    res["cpsat"] = cpsat(lp, tl)
    if lp != path:
        os.remove(lp)
    with open(outp, "a") as f:
        f.write(json.dumps(res) + "\n")
    print(json.dumps({k: res[k] for k in ["file", "status", "nodes", "maxdepth", "time", "t_root"]}), res["cpsat"].get("wall"), res["cpsat"].get("status"))
