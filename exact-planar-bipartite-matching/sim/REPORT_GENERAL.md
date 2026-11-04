# Checks of notes/GENERAL.md

Run on 3 Nov 2026 with `sim/gm.py` at the commit that holds this file. No check failed in any lane below. Timed lanes do not reproduce exact counts on another machine.

## Main lanes

Seeds and seconds: normal `gm.py 7001 1200`, big `gm.py 7002 1200 big`, region `gm.py region 7003 1200`, treewidth `gm.py tw 7004 600`. Every planar instance is checked for planarity.

| | Normal | Big | Region | Treewidth |
|---|---|---|---|---|
| Runs | 50,693 | 11,059 | 17,209 | 52,455 |
| Deficient runs | 35,989 | 8,117 | 16,249 | 46,604 |
| Vertices | 2,138,361 | 873,898 | 1,719,379 | 2,209,854 |
| Rank, against the whole matrix | 50,693 | 11,059 | 17,209 | 52,455 |
| Certificate | 50,693 | 11,059 | 17,209 | 52,455 |
| D′ of Gallai-Edmonds, against brute force | 29,500 | 3,806 | 3,647 | 26,485 |
| König | 20,683 | 4,364 | 4,515 | 17,634 |
| Rows of solves checked against the matrix | 200,060 | 200,082 | 200,010 | 200,010 |
| Search in a bag | 499,528 | 204,725 | 247,621 | 606,497 |
| Partner found | 947,996 | 390,878 | 448,606 | 798,536 |
| Retained rows | 29,371,405 | 28,874,729 | 5,436,519 | 7,647,956 |
| Filter |  |  |  | 312,695 |
| (H3), (H5) on region bags |  |  | 412,907 |  |
| Largest n | 202 | 348 | 542 | 126 |
| Largest R | 198 | 328 | 68 | 12 |
| Largest hubs | 198 | 328 | 40 | 8 |
| Largest retained set | 15 | 23 | 19 | 9 |
| Words in a bag | 2,136 | 4,193 | 2,620 | 1,485 |
| Words of one solve | 198 | 328 | 60 | 24 |
| Words of one partition | 28 | 60 | 39 | 11 |
| Solves per hub | 2.0 | 2.0 | 2.0 | 2 |

## Negative controls, `gm.py ctl 7005 <seconds>`

| Control | Rule broken | Runs | What fired |
|---|---|---|---|
| `anyedge` | the mate is any edge, not one with a nonzero entry | 4,331 | F_on_R_singular 2,799, matching_size 2,948, singular_at_bag 149 |
| `emptyA` | A′ taken empty in the certificate | 2,085 | certificate_not_tight 1,231, konig_not_cover 462, konig_size 462 |
| `nocorr` | no correction after pivots | 2,443 | F_on_R_singular 368, matching_size 419, singular_at_bag 51 |
| `noretain` | no retained rows | 2,756 | rank 1,955, rank_against_full_matrix 1,899 |
| `noschur` | no Schur complement | 2,438 | rank 1,433, rank_against_full_matrix 1,381 |
| `p3` | field of size 3 | 2,566 | certificate_not_tight 1,806, gallai_edmonds_D 889, konig_not_cover 39, konig_size 467, rank 451 |
| `p5` | field of size 5 | 2,399 | certificate_not_tight 1,404, gallai_edmonds_D 615, konig_not_cover 35, konig_size 319, rank 274 |
| `unit` | unit entries, no random a_e | 2,287 | certificate_not_tight 824, gallai_edmonds_D 510, konig_not_cover 293, konig_size 300, rank 503 |

`gm.py twctl 7006 <seconds>`, the filter of Section 6 keeps one row too few: rank wrong on 14,506 of 16,091 runs.

## Tiny primes, `gm.py tiny 7008 <seconds>`

At tiny primes wrong runs of the elimination are frequent, so this lane tests the check itself.

| | Count |
|---|---|
| Runs | 35,553 |
| Passes of the full check | 25,205 |
| Of those, right against brute force | 25,205 |
| Passes of part (a) alone | 31,645 |
| Part (a) passed with a wrong D′ | 6,440 |
| Runs whose matching was not maximum | 1,547 |

So part (a) alone certifies the size of the matching and not the Gallai-Edmonds sets, and the full check never passed a wrong answer.

## Disjoint paths and the separating set, `gm.py paths 7007 <seconds>`

12,510 runs against an independent maximum flow, κ up to 28, and 10,940 separating sets, checked for size and by an independent reachability test. Taking only vertices with both copies in the cover fails on 5,464 runs, which is why the rule also counts a_v and z_v. With the count off by one, the control fires on all 407 of its runs.

## Scale, `gm.py scale`

Grids, one run each. Words per bag grow as D²; a bound in Õ(D) is not reachable by this method, as Section 9 of the note says.

| k | n | D | Words in a bag | Words/D² | Solve words | Hubs | R | Retained |
|---|---|---|---|---|---|---|---|---|
| 6 | 36 | 9 | 253 | 3.12 | 15 | 12 | 20 | 2 |
| 10 | 100 | 15 | 863 | 3.84 | 42 | 19 | 36 | 6 |
| 14 | 196 | 20 | 2,308 | 5.77 | 51 | 34 | 62 | 6 |
| 18 | 324 | 27 | 3,426 | 4.7 | 67 | 40 | 70 | 7 |
| 24 | 576 | 35 | 5,429 | 4.43 | 94 | 36 | 66 | 14 |
| 30 | 900 | 44 | 14,267 | 7.37 | 135 | 67 | 124 | 12 |

## Limits

- No CONGEST simulation. Rounds are not measured. Words per bag are counted, and message passing is bag by bag on the bags of the simulator.
- The region lane hits forced leaves, so it does not reach O(log n) height with the leaves of (H1) at once.
- The treewidth lane has separators chosen by degree, so neither their size nor their balance is that of [4] of the note.
- Sizes stop at 900 vertices.
- The symmetric case of the Linear Algebra Lemma is not run.
