/-!
# A three-player Shapley network design game with price of stability above 1769/1126

Undirected graph on the vertices 0 = t₁ = t₃, 1 = t₂, 2 = s₁, 3 = s₂, 4 = s₃ with seven edges and integer costs.
Player `i` picks a simple path from `s_i` to `t_i`. The cost of an edge is shared equally among its users. A profile
is a Nash equilibrium if no player has a strictly cheaper simple path, given the other players.

Every share is a multiple of `c_e / 6`, since at most three players share an edge. All costs below are therefore
multiplied by 6, so that every comparison is an exact comparison of natural numbers.

* `ne_unique`: the game has exactly one Nash equilibrium, of cost 14506282.
* `opt_eq`: the minimum cost of a profile is 9220000.
* `pos_gt`: the price of stability 14506282 / 9220000 exceeds 1769 / 1126.
-/

namespace ShapleyCert

def edges : List (Nat × Nat) := [(0, 1), (0, 2), (0, 4), (1, 3), (1, 4), (2, 3), (3, 4)]

def cost : List Nat := [2600048, 4499232, 5447902, 4559148, 3420744, 920556, 2278652]

/-- Source and target of each player. -/
def pairs : List (Nat × Nat) := [(2, 0), (3, 1), (4, 0)]

/-- Neighbours of `v`, each with the index of the connecting edge. -/
def nbrs (v : Nat) : List (Nat × Nat) :=
  (List.range edges.length).filterMap fun j =>
    let e := edges.getD j (0, 0)
    if e.1 = v then some (e.2, j) else if e.2 = v then some (e.1, j) else none

/-- All simple paths from `v` to `t` that avoid `seen`, as lists of edge indices. The graph has 5 vertices, so
fuel 6 never runs out. -/
def dfs : Nat → Nat → Nat → List Nat → List Nat → List (List Nat)
  | 0, _, _, _, _ => []
  | fuel + 1, v, t, seen, used =>
    if v = t then [used.reverse]
    else (nbrs v).flatMap fun p => if p.1 ∈ seen then [] else dfs fuel p.1 t (p.1 :: seen) (p.2 :: used)

/-- The simple paths of player `i`. -/
def paths (i : Nat) : List (List Nat) :=
  let st := pairs.getD i (0, 0)
  dfs 6 st.1 st.2 [st.1] []

/-- All profiles: one simple path per player. -/
def profiles : List (List (List Nat)) :=
  (paths 0).flatMap fun p => (paths 1).flatMap fun q => (paths 2).map fun r => [p, q, r]

/-- Number of players whose path uses edge `e`. -/
def users (s : List (List Nat)) (e : Nat) : Nat := (s.filter fun p => e ∈ p).length

/-- Total cost of the edges used by the profile. -/
def total (s : List (List Nat)) : Nat :=
  ((List.range edges.length).filter fun e => 0 < users s e).foldl (fun acc e => acc + cost.getD e 0) 0

/-- Six times the cost of path `q` for a player whose current path is `p`, if she moves to `q`. -/
def dev6 (s : List (List Nat)) (p q : List Nat) : Nat :=
  q.foldl (fun acc e => acc + cost.getD e 0 * (6 / (users s e - (if e ∈ p then 1 else 0) + 1))) 0

/-- No player has a strictly cheaper simple path. For `q = p` the cost `dev6` is six times the current share. -/
def isNE (s : List (List Nat)) : Bool :=
  (List.range pairs.length).all fun i =>
    let p := s.getD i []
    (paths i).all fun q => dev6 s p p ≤ dev6 s p q

theorem shares_exact : ∀ s ∈ profiles, ∀ e < edges.length, users s e ≤ 3 := by decide +kernel

theorem ne_unique : (profiles.filter isNE).map total = [14506282] := by decide +kernel

theorem opt_eq : (∀ s ∈ profiles, 9220000 ≤ total s) ∧ ∃ s ∈ profiles, total s = 9220000 := by decide +kernel

theorem pos_gt : 1769 * 9220000 < 1126 * 14506282 := by decide +kernel

end ShapleyCert
