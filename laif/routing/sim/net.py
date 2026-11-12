"""TNTP network loader (github.com/bstabler/TransportationNetworks) and routing-graph helpers."""
from dataclasses import dataclass
from pathlib import Path

import numpy as np
import scipy.sparse as sp

DATA = Path(__file__).parent / "data" / "tntp"
NETS = {  # name -> net file, relative to DATA
    "SiouxFalls": "SiouxFalls/SiouxFalls_net.tntp",
    "Anaheim": "Anaheim/Anaheim_net.tntp",
    "Barcelona": "Barcelona/Barcelona_net.tntp",
    "Winnipeg": "Winnipeg/Winnipeg_net.tntp",
    "ChicagoSketch": "Chicago-Sketch/ChicagoSketch_net.tntp",
    "Austin": "Austin/Austin_net.tntp",
    "ChicagoRegional": "chicago-regional/ChicagoRegional_net.tntp",
}


@dataclass
class Net:
    name: str
    n: int  # nodes (0-based ids)
    zones: int
    ftn: int  # first thru node, 0-based: nodes < ftn may not be passed through
    tail: np.ndarray
    head: np.ndarray
    cap: np.ndarray  # veh/h
    length: np.ndarray
    fft: np.ndarray  # free-flow time (min)
    b: np.ndarray  # BPR alpha
    power: np.ndarray  # BPR beta

    @property
    def m(self):
        return len(self.tail)

    def bpr(self, x):
        """Link travel time at flow x (BPR)."""
        return self.fft * (1 + self.b * (x / self.cap) ** self.power)


def load(name: str) -> Net:
    meta, rows = {}, []
    for line in (DATA / NETS[name]).read_text().splitlines():
        s = line.strip()
        if s.startswith("<"):
            key, _, val = s[1:].partition(">")
            meta[key.strip()] = val.strip()
        elif s and not s.startswith("~"):
            rows.append([float(x) for x in s.replace(";", " ").split()[:7]])
    a = np.array(rows)
    assert len(a) == int(meta["NUMBER OF LINKS"]), name
    return Net(name, int(meta["NUMBER OF NODES"]), int(meta["NUMBER OF ZONES"]), int(meta["FIRST THRU NODE"]) - 1,
               a[:, 0].astype(np.int64) - 1, a[:, 1].astype(np.int64) - 1, a[:, 2], a[:, 3], a[:, 4], a[:, 5], a[:, 6])


def routing_graph(net: Net, w: np.ndarray):
    """Directed graph for routing with weights w per TNTP link.

    Nodes < ftn are centroids that must not be passed through: each is split into an in-copy (its original id;
    destination only, no out-links) and an out-copy (id n + c; origin only, no in-links).
    Parallel links are merged keeping the minimum weight (routing tables are indexed by next-hop node).
    Returns (N, csr matrix W with W[v,u] = weight of link v->u).
    """
    tail = np.where(net.tail < net.ftn, net.n + net.tail, net.tail)
    N = net.n + net.ftn
    W = sp.coo_matrix((w, (tail, net.head)), shape=(N, N)).tocsr()  # coo->csr sums duplicates; take min instead:
    if W.nnz != len(w):
        order = np.lexsort((w, net.head, tail))
        t, h, ww = tail[order], net.head[order], w[order]
        keep = np.r_[True, (t[1:] != t[:-1]) | (h[1:] != h[:-1])]
        W = sp.csr_matrix((ww[keep], (t[keep], h[keep])), shape=(N, N))
    return N, W
