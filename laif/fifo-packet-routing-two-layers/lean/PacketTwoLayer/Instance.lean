import Mathlib.Tactic.NormNum

/-!
# A two-layer packet routing instance with price of anarchy 7/5

FIFO packet routing game on a linear multigraph `s → v₁ → d` with two layers of parallel edges.
Every packet starts at `s` at time 0. Each edge lets at most one packet leave per time step. A packet that
reaches the tail of an edge at time `t` leaves at `max t (previous departure + 1)` and reaches the head after the
transit time of the edge. Packets are served in the order of their arrival at the tail, ties broken by the smaller
player index.

A state is a list of paths `(e, f)`, one per player in index order, with `e` an edge of layer 1 and `f` an edge of
layer 2. A state is a uniformly fastest route (UFR) equilibrium if no player reaches `v₁` or `d` earlier by a
unilateral change of path. The makespan is the last arrival at `d`.

The instance has five layer-1 edges of transit time 1, layer-2 transit times `1, 1, 4, 4, 4`, and 11 players.
It has a UFR equilibrium with makespan 7 and a state with makespan 5, so its price of anarchy is at least 7/5.
-/

namespace PacketTwoLayer

/-- One layer: `τ` transit times, `arr` arrival times at the tail, `ch` chosen edges, both indexed by player.
Players are served in the order of `(arr i, i)`; the result is the arrival time of each player at the head. -/
def layer (τ arr ch : List ℕ) : List ℕ :=
  let n := arr.length
  let T := arr.foldl max 0
  let order := (List.range (T + 1)).flatMap fun t => (List.range n).filter fun i => arr.getD i 0 == t
  let step : List ℕ × List ℕ → ℕ → List ℕ × List ℕ := fun (nf, out) i =>
    let e := ch.getD i 0
    let dep := max (arr.getD i 0) (nf.getD e 0)
    (nf.set e (dep + 1), out.set i (dep + τ.getD e 0))
  (order.foldl step (List.replicate τ.length 0, List.replicate n 0)).2

/-- Arrival times of every player at `v₁` and at `d`. -/
def times (a b : List ℕ) (ps : List (ℕ × ℕ)) : List ℕ × List ℕ :=
  let t1 := layer a (List.replicate ps.length 0) (ps.map Prod.fst)
  (t1, layer b t1 (ps.map Prod.snd))

/-- The makespan: the last arrival at `d`. -/
def makespan (a b : List ℕ) (ps : List (ℕ × ℕ)) : ℕ := (times a b ps).2.foldl max 0

/-- UFR equilibrium: for every player `i` and every path `(e, f)`, switching player `i` to `(e, f)` does not
make her arrive earlier at `v₁` or at `d`. -/
def UFR (a b : List ℕ) (ps : List (ℕ × ℕ)) : Prop :=
  ∀ i < ps.length, ∀ e < a.length, ∀ f < b.length,
    (times a b ps).1.getD i 0 ≤ (times a b (ps.set i (e, f))).1.getD i 0 ∧
    (times a b ps).2.getD i 0 ≤ (times a b (ps.set i (e, f))).2.getD i 0

instance (a b : List ℕ) (ps : List (ℕ × ℕ)) : Decidable (UFR a b ps) := by
  unfold UFR; infer_instance

def a₀ : List ℕ := [1, 1, 1, 1, 1]
def b₀ : List ℕ := [1, 1, 4, 4, 4]

/-- The equilibrium state: ties are broken towards the busy short layer-2 edges. -/
def eq₀ : List (ℕ × ℕ) :=
  [(0, 0), (1, 1), (2, 0), (3, 1), (4, 0), (0, 1), (1, 0), (2, 1), (3, 0), (4, 1), (0, 0)]

/-- A state with makespan 5: four packets on each of the paths `(0,0)`, `(1,1)` and one on each long path. -/
def opt₀ : List (ℕ × ℕ) :=
  [(0, 0), (0, 0), (0, 0), (0, 0), (1, 1), (1, 1), (1, 1), (1, 1), (2, 2), (3, 3), (4, 4)]

theorem eq₀_valid : eq₀.length = 11 ∧ ∀ p ∈ eq₀, p.1 < a₀.length ∧ p.2 < b₀.length := by decide

theorem opt₀_valid : opt₀.length = 11 ∧ ∀ p ∈ opt₀, p.1 < a₀.length ∧ p.2 < b₀.length := by decide

theorem eq₀_ufr : UFR a₀ b₀ eq₀ := by decide

theorem eq₀_makespan : makespan a₀ b₀ eq₀ = 7 := by decide

theorem opt₀_makespan : makespan a₀ b₀ opt₀ = 5 := by decide

/-- The instance has a UFR equilibrium whose makespan is 7/5 times the makespan of another state. -/
theorem poa_ge_seven_fifths :
    ∃ S T : List (ℕ × ℕ), S.length = 11 ∧ T.length = 11 ∧ UFR a₀ b₀ S ∧
      (makespan a₀ b₀ S : ℚ) / makespan a₀ b₀ T = 7 / 5 :=
  ⟨eq₀, opt₀, rfl, rfl, eq₀_ufr, by rw [eq₀_makespan, opt₀_makespan]; norm_num⟩

end PacketTwoLayer
