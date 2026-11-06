# Distance labels from disks cut along a tree of shortest walks

This note describes the construction of the labels of the Label Hypothesis that is proved in Lean
(`labelHypothesis_of_boxes` in `lean/SsspFlow/LabelFinal.lean`). It uses one kind of bag in place of the
tiles of Lemma 14′ and the region bags of `notes/LEMMA15.md` §9: a disk cut out of a planar map along
walks up a tree of shortest walks. Every bag is drawn in a disk with its corners on the boundary, so the
crossing inequalities hold on its corners directly. No hub network, connectors or region graphs are
needed.

The proof takes three cited results as hypotheses: the realization of metrics with the crossing
inequalities by disks (G3), distance labels of planar digraphs (G5) and face identifiers (G6). The
aggregation primitive over many subgraphs that it calls is proved as well. The nodes get the rotation
lists of a planar embedding as input. Local computation is not bounded, as in the CONGEST model.

## 1. The statement

Let $G$ be a planar network with $n$ nodes and hop diameter at most $D$, with arc lengths
$\ell(a,b)\in[1,W]$ for $W=(n+2)^K$, and let $1\le e\le W$. For each $n$, $e$ and $D$ there is one
algorithm, fixed before the network, with messages of polylogarithmically many bits, that runs for
$\tilde O(De)$ rounds. Afterwards every node $v$ outputs

- its chain of bags, a list of bag names;
- for each bag of the chain, the hubs of that bag, with an estimate of the distance to each hub and one
  from it;
- for each neighbour $u$, the bags whose subgraph contains the edge $vu$.

The bags form a hierarchy of height $O(\log n)$. The subgraph of a bag has hop diameter $\tilde O(D)$,
each bag has $\tilde O(D)$ hubs, and at one depth at most two bags contain an edge. An estimate is at
least the distance in $G$ and at most $1+1/e$ times the distance along the arcs of the bag.
`LabelWitness` in `lean/SsspFlow/LabelHypothesis.lean` states all of this, and `LabelWitness.query_bound`
derives the query of Lemma V from it.

## 2. The doubled map

The doubled map $M$ has the darts $(d,b)$ for the darts $d$ of $G$ and $b\in\{0,1\}$, with
$\mathrm{rot}(d,0)=(d,1)$, $\mathrm{rot}(d,1)=(\mathrm{rot}\,d,0)$ and $\mathrm{rev}(d,b)=(\mathrm{rev}\,d,1-b)$.
Every edge of $G$ becomes two parallel edges with a face of two darts between them, a digon, and the
darts with $b=1$ trace the faces of $G$. If $G$ is planar and connected, so is $M$
(`RotSystem.double`, `double_planar`). Both copies of an edge get its length, so distances do not change.

## 3. Levels and bags

Fix a tree $T$ of shortest walks from a root $r$, of height $h\le\min(D,n)$. Of the two copies of a
tree edge from $v$ to its parent, one is marked. The two digon corners of that edge are its rails.

A corner is a dart of $M$. A level is a set $\Gamma$ of corners whose vertices are closed under the
parent in $T$, and which contains both rails of the tree edge of each of its vertices other than $r$
(`IsLevel`). The first level is $\Gamma_0=\{w_0\}$, one corner at $r$ with $b=1$.

Splitting $M$ at $\Gamma$ cuts every vertex along its corners (`RotSystem.split`). The bags of the level
are the components of the split. By the splitting identity of `lean/SsspFlow/Splice.lean`, every bag is
planar and its corners, the ports, form one cycle of $\psi$, the first return of the faces to
$\Gamma$. So a bag is a disk with its ports on the boundary in the order of $\psi$.

The cone over $\Gamma$ glues the ports of each bag to one vertex in this order (`RotSystem.cone`). It is
planar, and each of its faces has at most one corner of $\Gamma$. A vertex of a bag with no corner in
$\Gamma$ is a non-port vertex. The marked copies at the non-port vertices form a spanning forest of the
cone (`IsLevel.spanForest`), whose darts we call marks.

## 4. The cut of a bag

**Tours.** For a spanning forest $F$ of a planar map, the tour $\sigma_F$ follows the rotation and
crosses each edge of $F$. Its cycles are the components of the map (`fconnect_tour_iff`), by Euler's
formula alone, and it meets the corners of each face in the order of the face (`walk_strict`).

**Balance lemma** (`exists_balanced`). If a cycle of the tour has $m\ge4$ darts of $F$, it has two
corners $x\ne y$ of one face such that each of the two arcs between them on the tour holds at most
$(3m-2)/4$ darts of $F$.

**The rule** (`lean/SsspFlow/Select.lean`). Let a bag $X$ have $m$ marks on its tour in the cone.

- If $m=0$, then $X$ has no non-port vertex. It is a leaf.
- If $1\le m\le3$, the cut is the rail of one non-port vertex.
- If $m\ge4$, the cut is a pair $x$, $y$ as in the balance lemma, on one face of the cone.

The next level adds the cut of every bag and the rails of the walks up $T$ from the cut, each up to
the first vertex that has a corner. It is a level again (`IsLevel.next`). A walk adds at most twice the
depth of its start in corners (`card_railsUp_le`), so a bag gets at most $2+4h$ new ports per level.

**Side lemma** (`side_gcomp`). Give every dart the side of the tour arc $(x,y]$ in which it lies, but
give the dart with $b=0$ of a marked copy the side of its reverse. Every component of the split at the next level lies on one side.
So a child $Y$ of $X$ keeps the marks of one arc only, and $4m(Y)+2\le3m(X)$ (`npOf_balance`); the
small case also lowers $m$. Hence after $3k$ levels with $2n<2^k$ no bag has a non-port vertex
(`Decomp.final`). The hierarchy has height $H=3k=O(\log n)$.

## 5. The shape of the bags

The counts are in `lean/SsspFlow/Bags.lean`.

- A bag at depth $d$ has at most $1+d(2+4h)$ ports (`card_ports`). At most $1+2d$ of them are gaps,
  ports with $b=1$ (`card_gaps`), since a cut adds at most two.
- Between two gaps, consecutive ports along $\psi$ are joined inside the bag by a copy of a tree edge,
  and every vertex of a bag reaches a port in at most $h$ steps up $T$ inside the bag. So two vertices
  of a bag with at most $J$ ports and $G$ gaps are joined inside it by a walk of at most
  $(G+1)(2(h+J)+1)$ arcs (`bag_diam`). In the hierarchy this is at most
  $(2H+2)(2(h+1+H(2+4h))+1)=\tilde O(D)$ (`Decomp.span`).
- The hubs of a bag are its vertices with a corner at the next level, at most $1+(H+1)(2+4h)$ of them
  (`Decomp.hub_card`). At a leaf every vertex is a hub, and since a leaf is a simple planar graph on its
  hubs, it has $O(J)$ edges (`leaf_card`).
- An edge of $G$ has two copies in $M$, and each copy lies in one bag per level. So at one depth at most
  two bags contain an edge (`Decomp.congestion`).
- Two corners with $b=1$ on one face of $M$ lie in different bags (`not_same_of_face`). So a bag meets
  each face of $G$ at most once on its boundary, and the face identifiers of (G6) tell the faces of the
  cone apart (`fconnect_cone_face`).

The subgraph of a bag in the label is the set of its arcs. No connecting paths and no spanning trees
per bag are needed.

## 6. The values

The values are computed from the bottom up, along the levels (`Levels.lean`, `Hubs.lean`,
`Witness.lean`). Fix a unit $U$, and let $\lambda_\Gamma$ be $U$ times the distance in the split at
$\Gamma$.

**Invariant** (`LevelMetric`). For values $\delta$ on the corners of a level, every bag has a metric
$\mu$ on its ports that satisfies the crossing inequalities in the order of $\psi$, with
$\lambda_\Gamma\le\mu\le\Lambda\lambda_\Gamma$ and $\mu\le\delta\le\frac{U+4}{U}\mu$.

**Step** (`levelMetric_step`). From the values at the next level, the least total values of walks
between the ports of a bag, with free moves between corners at one vertex, give a matrix on these
ports. Any metric with the crossing inequalities between this matrix and $\frac{U+4}{U}$ times it is a
feasible point, and one exists: the disks of the children, composed along their ports, satisfy the
crossing inequalities on each cycle of ports (`hubDist_monge`, from `DiskDrawn.monge` in
`lean/SsspFlow/Crossing.lean`). The bag picks a feasible point, realizes it by (G3) as a disk with at
most $Cj^6$ vertices for $j$ ports, scales its weights, rounds them up, and labels the disk by (G5)
(`exists_bagOK`). The query of these labels gives the values of the bag, and the numbers do not grow from
level to level. The factor $\Lambda$ grows by $\left(\frac{U+4}{U}\right)^2$ per level, so the errors add
up over the levels instead of multiplying large factors (`levelMetric_seq`). With $U=8(2H+3)e$,
$\left(\frac{U+4}{U}\right)^{2H+1}\le1+1/e$ (`pow_cU_le`).

**Estimates** (`est_bounds`). The values between the hubs of each bag give estimates from every vertex of
the bag to its hubs. On a hub it is the value itself. Otherwise it is the least sum of the estimate from
the vertex to a hub $t$ of the child that contains the vertex and the value from $t$ to the hub. These
estimates keep the bounds of the values, with no growth over the levels. The output rounds them down
(`floorE`). A bag has short walks along its arcs, so the rounded values have polylogarithmically many
bits (`distR_le_of_reach`). `labelsOK_of_mem` puts the hierarchy and the estimates together into the
witness of Section 1.

## 7. The algorithm

The algorithm runs in phases on top of the message model (`Machine.lean`, `LabelProof.lean`).

- **Setup.** The face identifiers by (G6), and the tree $T$, its depths and sums over its subtrees by
  relaxations along $T$ (`NetPasses.lean`). One tour $\tau$ through all darts of $M$
  (`fconnect_tau`) gets numbers by these sums (`TourNums.lean`).
- **Levels.** The masses on the tour of each bag are differences of the numbers of $\tau$ plus an offset
  per port (`pot_spec`), so the table of the ports of a bag decides its cut (`Tables.lean`,
  `LevelT.lean`). A few aggregation calls per level, for all bags at once, gather the tables, choose the
  cuts and spread the new corners, and every dart decides from the table whether it is a new corner
  (`mem_next_iff`, `NetLevels.lean`). The names of the bags come from a flood inside the bags.
- **Values.** One aggregation call per depth, from the leaves up, gathers the records of the ports of
  each bag (`NetValues.lean`). Every node of the bag then computes the feasible point, the disk, its
  labels and the values locally.
- **Rounds and bits.** Each aggregation call has subgraphs of hop diameter $\tilde O(D)$, congestion two
  and $\tilde O(De)$ keys, so it takes $\tilde O(De)$ rounds, and there are $O(\log n)$ calls. All numbers
  are polynomial in $n$, so messages have polylogarithmically many bits, independently of $D$
  (`exp_bounds`, `bits_le`, `labelRounds_le`).

## 8. Where the proofs are

| Part | Lean |
|---|---|
| Maps from rotation lists, splitting, adding edges | `PlanarMap.lean`, `Splice.lean`, `Chord.lean` |
| Crossing inequalities of a disk | `Crossing.lean` |
| Tours and the balance lemma | `Tour.lean` |
| Cones, levels, side lemma | `Disks.lean` |
| Bags, depth, hierarchy | `Bags.lean`, `Select.lean`, `Sector.lean` |
| One bag: realization and labels | `Glue.lean`, `Compose.lean`, `Emulator.lean` |
| Values and estimates | `Levels.lean`, `Hubs.lean`, `Witness.lean` |
| Numbers on the tours | `Tau.lean`, `Potential.lean`, `TourNums.lean`, `Tables.lean`, `LevelT.lean` |
| Message passing | `Machine.lean`, `NetTree.lean`, `NetPasses.lean`, `NetAgg.lean`, `NetFlood.lean`, `LevelTab.lean`, `NetLevels.lean`, `EdgeBound.lean`, `ValueTab.lean`, `NetValues.lean` |
| Output and final theorem | `Output.lean`, `LabelProof.lean`, `LabelFinal.lean` |
| Aggregation primitive | `AggMux.lean`, `AggMerge.lean`, `AggProof.lean`, `AggFinal.lean` |

All files are in `lean/SsspFlow/`, and `lean/axioms.txt` lists the axioms of every named theorem.
