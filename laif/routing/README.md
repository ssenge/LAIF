# Price-based distance-vector routing for road traffic

_12 November 2026_

Vehicles are routed through a road network by the intersections themselves. Each node keeps a distance to every destination and splits its traffic over the next links. Nobody holds a plan or a forecast of the demand. The question is how close such a scheme gets to the dynamic system optimum, the least total travel time any routing can reach, and how it compares with central methods that know the demand.

The routing protocol is APDV (anchored periodic distance vector). Each destination starts a wave of advertisements once per period, and every node relaxes and relays it upstream, as in the destination-triggered update cycles of [11]. Here the advertised link costs are local prices. Each link prices its capacity with a virtual queue [4], so traffic moves away from a link before a real queue forms there.

## Results

All results are numerical. Traffic is modelled by a destination-based cell transmission model [2] with a non-FIFO node model, on the Sioux Falls, Anaheim and Chicago Sketch networks [1], and on Sioux Falls also with a strict FIFO node model. The demand is the network's origin-destination table times a factor, released at a constant rate over 60 minutes. The tables give the mean trip time divided by a lower bound.

### Sioux Falls, against the dynamic system optimum

The lower bound is the system optimum of the same cell model, solved as a linear program [3] (8.92, 9.11, 9.43, 10.82 and 13.44 minutes at 0.3 to 0.7 of the demand). It allows holding vehicles anywhere and overtaking, so no routing rule needs to reach it.

| Strategy | ×0.3 | ×0.4 | ×0.5 | ×0.6 | ×0.7 |
|---|---|---|---|---|---|
| UE routes, static | 1.27 | 1.82 | 2.50 | 3.03 | |
| APDV on travel times | 1.18 | 1.64 | 2.72 | 3.98 | |
| DUE, central, perfect foresight | 1.12 | 1.43 | 2.35 | 3.24 | |
| Price-based APDV, cold start | 1.033 | 1.046 | 1.191 | 1.875 | 2.397 |
| **Price-based APDV, learned, with origin holding** | **1.023** | **1.035** | **1.074** | **1.250** | **1.435** |

At 0.52 of the demand, the network stops having a static routing that keeps every link below capacity. Above that point, queues cannot be avoided, and the optimum holds vehicles at their origins. The learned price scheme holds vehicles at their origins too, with local information only. At ×0.6 it needs 1.25 times the optimum, where static UE routes need 3.0 times and DUE 3.2 times.

The learned rows are the runs with the profile after 30 days of learning. Up to ×0.5 the scheme has settled by then: over days 31 to 60 the results move by at most 0.01. At ×0.6 and ×0.7 the profile keeps moving, and over days 31 to 60 the results lie between 1.250 and 1.318 and between 1.435 and 1.564.

### Sioux Falls with a strict FIFO node model

In a strict FIFO node model [5], vehicles leave a link in the order they entered it. If any part of a link's outflow heads for a full link, the whole link stops. A logit split gives every next link that leads closer to the destination a positive share, however small, so a single full link can hold back all traffic on the links that feed it. The FIFO-aware price scheme therefore drops split shares below 0.05 at each node and renormalizes the rest. It also holds vehicles at their origins for the full estimated queue delay instead of half of it. Everything else is as in the learned version.

| Strategy | ×0.3 | ×0.4 | ×0.5 | ×0.6 | ×0.7 |
|---|---|---|---|---|---|
| UE routes, static | 2.653 | 2.700 | 4.292 | 20.9 (37% unfinished) | 24.5 (57% unfinished) |
| SO routes, static BPR | 1.007 | 1.419 | 2.474 | 25.1 (47% unfinished) | 23.0 (53% unfinished) |
| Capacity-feasible plan, static LP, central | **1.001** | **1.005** | **1.012** | none | none |
| **Price-based APDV, learned, FIFO-aware** | 1.028 | 1.095 | 1.562 | **2.279** | **2.588** |

The bound is the same linear program as above. It does not enforce FIFO, so it bounds the FIFO runs too. Unfinished trips count with their time up to 600 minutes. Above the limit of 0.52 no capacity-feasible static plan exists, and the static routings leave 37 to 57% of the trips unfinished after 600 minutes. The FIFO-aware price scheme completes every trip, at 2.28 and 2.59 times the bound. Below the limit the central plan builds no queue, so FIFO does not affect it, and it stays ahead, by 3 points at ×0.3 and by 55 points at ×0.5. The FIFO-aware scheme completes every trip for every threshold from 0.02 to 0.2, with results between 1.43 and 1.66 at ×0.5, 2.16 and 2.51 at ×0.6, and 2.43 and 2.88 at ×0.7. Its learned profile settles less than in the non-FIFO model: over days 31 to 60 the results lie between 1.03 and 1.12 at ×0.4, 1.34 and 1.56 at ×0.5, 2.22 and 2.71 at ×0.6, and 2.53 and 3.06 at ×0.7. In the non-FIFO model the FIFO-aware scheme gives 1.020, 1.035, 1.108, 1.216 and 1.306.

### Sioux Falls, days that differ from the plan

Every strategy is prepared for the planned day: the static plans and DUE are computed for it, and the price profile is learned on it. It then runs on a day with an incident (the busiest link at half capacity for 30 minutes), 20% more or less demand, or random noise on every origin-destination flow (lognormal, σ 0.3). The bound is the system optimum of that day, known in advance.

| Strategy | ×0.4 planned day | ×0.4 worst day | ×0.5 planned day | ×0.5 worst day |
|---|---|---|---|---|
| Capacity-feasible plan, static LP, central | **1.005** | 1.684 (+20%) | **1.012** | 2.210 (+20%) |
| SO routes, static BPR | 1.117 | 1.635 (+20%) | 1.372 | 2.213 (+20%) |
| DUE, central, planned day | 1.431 | 2.266 (+20%) | 2.355 | 3.097 (+20%) |
| **Price-based APDV, learned** | 1.035 | **1.134** (+20%) | 1.074 | **1.268** (+20%) |

A central plan is best on its own day, by 3 to 6 points. Over the four other days the price scheme has the smallest worst case: 1.134 against 1.635 at ×0.4, and 1.268 against 2.210 at ×0.5. At ×0.5 the day with 20% more demand lies above the limit of 0.52, where queues cannot be avoided.

### Anaheim and Chicago Sketch, above capacity

On these networks the system optimum is too large to solve. The bound is the mean free-flow trip, which no strategy can beat. The demand factors lie above the limit for a queue-free static routing (0.53 on Anaheim and 0.42 on Chicago Sketch), so every strategy builds queues.

| Strategy | Anaheim ×0.8 | Anaheim ×1.0 | Anaheim ×1.2 | Chicago ×0.75 | Chicago ×1.0 |
|---|---|---|---|---|---|
| UE routes, static | 1.498 | 2.192 | 2.704 | 1.234 | 1.732 |
| SO routes, static BPR | 1.272 | 1.634 | 2.118 | 1.077 | 1.298 |
| APDV on travel times | 1.291 | 1.720 | 2.210 | 1.393 | 2.581 |
| DUE, central, perfect foresight | **1.223** | 1.585 | 2.074 | 1.154 | 1.582 |
| **Price-based APDV, learned, with origin holding** | 1.243 | **1.557** | **1.938** | **1.069** | **1.217** |

The price scheme has the shortest mean trip in four of the five settings. On Anaheim at ×0.8, DUE stays ahead, by 2.0 points.

### Message cost

Prices change every minute, so APDV advertises every destination every period: at most |D| · m messages per period for |D| destinations and m links. With triggered updates, a link re-advertises only when its travel time, price or queue delay moved by more than a threshold ε since its last advertisement, and a node relays a destination only when its distance changed.

| Network, demand | ε = 0 | ε = 0.2 min | ε = 0.5 min | Mean trip change at ε = 0.2 |
|---|---|---|---|---|
| Sioux Falls ×0.4 / ×0.5 / ×0.6 | 0.61 / 0.76 / 0.84 | **0.26 / 0.47 / 0.63** | 0.17 / 0.35 / 0.54 | at most 0.1 points |
| Anaheim ×0.8 / ×1.0 | 0.64 / 0.71 | **0.36 / 0.46** | 0.32 / 0.40 | at most 0.4 points |
| Chicago Sketch ×1.0 | 0.66 | **0.26** | 0.23 | 0.1 points |

The entries are mean messages per period as a share of the periodic count (1824, 34 732 and 1 141 650). A threshold of 0.2 minutes saves 37 to 74% of the messages and changes the mean trip by at most 0.4 points. Flooding every link update to all links, as link-state routing does, sends 1.1 to 3.9 times as many messages as the triggered distance vector at ε = 0.2. On the two larger networks, the busiest period stays at 0.76 to 0.88 of the periodic count, so the saving is in volume, not in peak load.

### Per-vehicle check, Sioux Falls

The same policies run in UXsim [8], a per-vehicle simulator with FIFO lanes, platoons of 5 vehicles and steps of 5 seconds. A vehicle picks its next link at each node with probabilities equal to the split rates. The price scheme runs from a cold start, without learning and without origin holding.

| Mean trip (min) | ×0.3 | ×0.4 | ×0.5 | ×0.6 |
|---|---|---|---|---|
| UE routes, static | 16.96 | 24.58 | 55.65 | 86.25 |
| UXsim's own reactive routing (DUO, 10-minute updates) | 17.44 | 30.41 | 50.58 | 101.47 |
| **Price-based APDV, cold start** | **9.42** | **12.56** | **36.09** | **75.70** |

The price scheme is the fastest of these policies at every demand level, as in the cell model. At ×0.3 its mean trip is within 6% of the cell model's system optimum (8.92 minutes). Per vehicle, all mean trips are longer than in the non-FIFO cell model, and the difference grows with the demand (price scheme at ×0.5: 36.1 against 11.2 minutes).

## The algorithm

Once per period (1 minute), at every link a = (v, u) and node v:

1. **Price.** The link counts its offered inflow, the turn demands toward it at its tail node, and feeds it into a virtual queue served at 0.95 of its capacity. Its price is g times the delay of that queue, capped at 5 times the link's free-flow time. With a learned profile, the price adds a value per link and minute of the day. After each day, the profile takes one step toward balancing offered inflow and 0.95 of the capacity in each minute, at 1 minute per day, for 30 days.
2. **Distances.** APDV computes the distance to every destination on link cost = travel time of the vehicle now leaving the link + price.
3. **Splits.** Node v splits its traffic for destination d by logit (θ = 1 per minute on Sioux Falls, 3 on the larger networks) over the next links whose head is closer to d. Distances strictly decrease along every split, so the routing has no loops at any time.
4. **Origin holding.** Each link runs a second virtual queue at full capacity, an estimate of the real queue its traffic will cause. APDV carries the distances with and without those delays. An origin holds each vehicle until it has waited half of the difference for its destination.

The cold start uses only steps 1 to 3, with g = 3 and no profile. The learned version uses g = 0.3 on top of the profile, and origin holding. The FIFO-aware version is the learned one, with split shares below 0.05 dropped in step 3 and holding for the full difference in step 4.

All quantities are local to a link or a node. The only information exchanged is the APDV advertisement: per destination, the distance on the priced link costs and the distances with and without the estimated queue delays.

## Status and checks

The results are numerical. No part is formalized in Lean.

- **Scope:** three networks; demand released at a constant rate over 60 minutes; the cell model with origins that release at most the capacity of their out-links per step, with a non-FIFO node model, in which a blocked turn holds back only its own traffic, which waits in the last cell of the link and takes up its capacity, and on Sioux Falls also with the strict FIFO node model of [5]; on Anaheim and Chicago Sketch only the free-flow bound; the per-vehicle check on Sioux Falls only, without learning or origin holding; message counts are counted, not sent through a simulated network with delays or losses.
- **Lower bound:** `dnl.check_dso` checks that at light load the linear program gives exactly the free-flow run, and that a capacity drop raises it while the simulated run stays above it. The bounds are solved with the first-order solver of HiGHS [10], with nothing left in the network at the horizon.
- **Cell model:** `dnl.check` tests the node model on merges and diverges, and at light load the mean trip equals the free-flow mean; without congestion the prices stay at zero, learned or not; with ε = 0 the triggered run equals the exact one; after pruning, every split share is 0 or at least the threshold, and the shares at each node sum to 1.
- **Per-vehicle simulator:** `vehicles.check` gives a light-load mean trip of 8.550 minutes against a free-flow mean of 8.530 minutes. UXsim drops the last partial platoon of each origin-destination pair (under 1% of the trips), and means are over the generated trips.
- **DUE:** averaging of time-dependent shortest-path split rates with self-regulated steps [7]; relative gaps 1 to 6% on the larger networks after 20 to 30 iterations.

## Files

`sim/` holds the code and the raw output (`sim/out/`):

- `dnl.py`: the cell model, APDV on travel times, price-based APDV (`Price`), DUE, the system-optimum LP (`dso`) and the day-to-day learning (`learn`);
- `static.py`: static UE and SO by conjugate Frank-Wolfe [6]; `logit.py`: the logit split [9]; `net.py`: the network loader; `vehicles.py`: the per-vehicle runs in UXsim;
- `common.py`: the configuration of the price scheme used in every table (`fifo_aware` for the FIFO table);
- `sioux_falls.py`, `baselines.py`, `drift.py`, `fifo.py`, `scenarios.py`, `large.py`, `messages.py`, `per_vehicle.py`: one script per table, with the outputs `out/sioux_falls.txt`, `out/baselines.txt`, `out/drift.txt`, `out/fifo.txt`, `out/scen_*.txt`, `out/large_*.txt`, `out/messages_*.txt`, `out/per_vehicle.txt`; `out/dso_SiouxFalls_*.md` from `python dnl.py dso SiouxFalls 1 F` (the bound).

To run them, place the networks of [1] in `sim/data/tntp/` (for example `git clone https://github.com/bstabler/TransportationNetworks sim/data/tntp`) and install numpy, scipy, numba, highspy and uxsim.

## References

1. Transportation Networks for Research Core Team. Transportation Networks for Research. https://github.com/bstabler/TransportationNetworks.
2. C. F. Daganzo. The cell transmission model: a dynamic representation of highway traffic consistent with the hydrodynamic theory. Transportation Research Part B 28(4), 1994.
3. A. K. Ziliaskopoulos. A linear programming model for the single destination system optimum dynamic traffic assignment problem. Transportation Science 34(1), 2000.
4. R. J. Gibbens, F. P. Kelly. Resource pricing and the evolution of congestion control. Automatica 35(12), 1999.
5. C. M. J. Tampère, R. Corthout, D. Cattrysse, L. H. Immers. A generic class of first order node models for dynamic macroscopic simulation of traffic flows. Transportation Research Part B 45(1), 2011.
6. M. Mitradjieva, P. O. Lindberg. The stiff is moving: conjugate direction Frank-Wolfe methods with applications to traffic assignment. Transportation Science 47(2), 2013.
7. H. Liu, X. He, B. He. Method of successive weighted averages (MSWA) and self-regulated averaging schemes for solving stochastic user equilibrium problem. Networks and Spatial Economics 9, 2009.
8. T. Seo. UXsim: lightweight mesoscopic traffic flow simulator in pure Python. Journal of Open Source Software, 2025.
9. R. B. Dial. A probabilistic multipath traffic assignment model which obviates path enumeration. Transportation Research 5(2), 1971.
10. Q. Huangfu, J. A. J. Hall. Parallelizing the dual revised simplex method. Mathematical Programming Computation 10, 2018.
11. P. M. Merlin, A. Segall. A failsafe distributed routing protocol. IEEE Transactions on Communications 27(9), 1979.

## Use of AI

Claude Opus 5.5 was used to develop the method, write the simulation code and draft this text.
