# Simulation report

A numerical check proves nothing, and no proof uses it. The simulator runs the logic of `notes/MATCHING.md` centrally,
on decompositions that satisfy the properties in Section 2 of the note. It does not simulate rounds, messages or the
black boxes of [2].

## Main lanes (seeds 111 to 113, 121, 122; 15 minutes each)

863,003 runs: 807,500 path instances and 55,503 matching instances. No failure in any counter, no abort.

| Claim | Checks | Failures |
|---|---|---|
| Path is simple | 1,503,266 | 0 |
| Every step of the path is an arc | 1,503,266 | 0 |
| Path has the right ends | 807,500 | 0 |
| Lemma A: intervals in a bag are disjoint | 1,480,861 | 0 |
| Lemma C: repeats lie on the separator | 5,360,324 | 0 |
| Lemma B: visits of a hub at most its number of children (the check allowed the number of children; a later run tightened it to at most two, see below) | 30,160,690 | 0 |
| Requests in a bag at most hubs of the parent + 2 | 10,709,165 | 0 |
| Matching size equals an independent Hopcroft-Karp | 55,503 | 0 |
| König cover: size and coverage | 55,503 each | 0 |
| Multi-Source Lemma formula equals the true reach set | 55,503 | 0 |
| Weight equals an independent solver | 55,503 | 0 |
| Weight equals brute force (at most 18 edges) | 12,356 | 0 |
| Sum of duals equals weight | 55,503 | 0 |
| Dual feasibility, nonnegativity, tightness after every insertion | 21,310,951, 20,569,605, 7,988,756 | 0 |
| Reduced lengths nonnegative | 7,466,085 | 0 |
| Every instance is planar (networkx) | 863,003 | 0 |

Stress reached: 21,862 repeated vertices that needed erasing, up to 19 requests in one bag, up to 41 segments in one
request, and paths up to 225 vertices.

Families: grids with deletions, bipartite subgraphs of stacked triangulations, trees, even wheels with two hubs, K_{2,m},
combs, concentric even cycles, plus digraphs that orient them, directed snakes and spirals, right-and-down grids, and
Manhattan grids with alternating directions. Decompositions: components with their adjacent hubs, components with the whole
separator, and two children that hold the whole separator (the shape closest to a cycle separator). Separators are two paths
of a BFS tree; no planar embedding is used.

## Negative controls

Each is a deliberately wrong rule that has to fail.

| Variant | Runs | What fired |
|---|---|---|
| Any J path instead of least hops, path lane | 4,167 | 203,919 intervals overlap; 101 non-simple paths |
| The same, matching lane | 463 | 36,198 intervals overlap; 123 non-simple; 10 wrong sizes |
| No erasure, path lane | 6,250 | 57 non-simple paths |
| No erasure, matching lane | 523 | **nothing** |
| Neither rule, matching lane | 504 | 60,237 overlaps; 281 non-simple; 45 wrong sizes |
| One hub in seven skipped | 497 | 173 wrong sizes |
| Wrong δ | 5,137 | 668,436 negative duals; 3,134 wrong weights |
| Stops at the first free vertex | 5,225 | 199,756 slack edges; 4,289 wrong weights |

The erasure rule is therefore tested by the path lane, not by the matching lane: residual digraphs in the matching lane rarely
produce a repeat (312 in 55,503 runs).

An earlier version of the J-path control marked all successors on expansion and never fired. The reason is mathematical: any
graph search that marks all successors at once gives a path without shortcuts, and that is all Lemma A uses. The current
control takes a vertex when first entered, which does give shortcuts.

## Not covered

- Rounds, message sizes, knowledge, broadcast scheduling. All communication claims of the note are unchecked here.
- The black boxes of [2]: the BDD, Lemma 16 and the labels, in particular on the subdivided network.
- Real cycle separators and real bags of the decomposition.
- SSSP: distances here are centralized Dijkstra.
- Sizes above about 225 vertices.

## Two visits

The check in `mm.py` allows at most two visits. Short reruns, no failure: path lane 32,253 runs with 664,821 hub checks; matching lane 884
runs with 284,326 hub checks.

## Reproduce

    python3 -I sim/run.py path 111 900 big; python3 -I sim/run.py path 112 900 big; python3 -I sim/run.py path 113 900
    python3 -I sim/run.py 121 900 big; python3 -I sim/run.py 122 900
    python3 -I sim/run.py ctl 100 12

Timed lanes do not reproduce exact counts.
