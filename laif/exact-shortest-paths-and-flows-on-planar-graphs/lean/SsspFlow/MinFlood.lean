import SsspFlow.Congest

/-!
# The least number of the network in `D` rounds

Every node holds a number. In each round every node tells its neighbours its number and keeps the
least of its number and the numbers it hears. After `D` rounds on a network of diameter at most `D`,
every node holds the least number of the network.

* `minRecv`: the least of a number and the numbers received.
* `Algorithm.minFlood`: the exchange of `Algorithm.exch`, repeated with the least number as new input.
* `Algorithm.run_minFlood`: after `D` rounds every node holds the least number of the network.
-/

set_option autoImplicit false

namespace Cslib.Congest.Algorithm

variable {V : Type} [Fintype V]

/-- The least of `x` and the numbers received. -/
def minRecv (x : ℕ) (m : V → Option ℕ) : ℕ :=
  Finset.univ.fold min x fun u => (m u).getD x

theorem minRecv_le_self (x : ℕ) (m : V → Option ℕ) : minRecv x m ≤ x :=
  (Finset.fold_min_le _).2 (.inl le_rfl)

theorem minRecv_le {x y : ℕ} {m : V → Option ℕ} {u : V} (h : m u = some y) : minRecv x m ≤ y :=
  (Finset.fold_min_le _).2 (.inr ⟨u, Finset.mem_univ _, by rw [h]; rfl⟩)

theorem le_minRecv {c x : ℕ} {m : V → Option ℕ} (hx : c ≤ x) (hm : ∀ u y, m u = some y → c ≤ y) :
    c ≤ minRecv x m := by
  refine (Finset.le_fold_min _).2 ⟨hx, fun u _ => ?_⟩
  cases h : m u with
  | none => exact hx
  | some y => exact hm u y h

/-- **The min flood**: one exchange per round, and the least number heard is the new number. -/
noncomputable def minFlood (B : ℕ) : Algorithm V ℕ (ℕ × ℕ × (ℕ × (V → Option ℕ))) B :=
  (exch V B).iter 1 (fun _ x => x) (fun _ x s => minRecv x s.2)

variable (G : SimpleGraph V) [DecidableRel G.Adj] {B : ℕ} (x₀ : V → ℕ)

/-- The numbers after `k` rounds. -/
noncomputable abbrev floodVal (B : ℕ) (k : ℕ) : V → ℕ :=
  iterData (exch V B) 1 (fun _ x => x) (fun _ x s => minRecv x s.2) G x₀ k

theorem floodVal_succ (hB : ∀ v, x₀ v < 2 ^ B) (k : ℕ) (v : V) (hk : ∀ u, floodVal G x₀ B k u < 2 ^ B) :
    floodVal G x₀ B (k + 1) v =
      minRecv (floodVal G x₀ B k v) fun u => if G.Adj u v then some (floodVal G x₀ B k u) else none := by
  have := hB
  show minRecv _ ((exch V B).run G (fun v => floodVal G x₀ B k v) 1 v).2 = _
  rw [run_exch G _ hk]

theorem floodVal_le_init (hB : ∀ v, x₀ v < 2 ^ B) : ∀ k v, floodVal G x₀ B k v ≤ x₀ v
  | 0, _ => le_rfl
  | k + 1, v => by
    rw [floodVal_succ G x₀ hB k v fun u => (floodVal_le_init hB k u).trans_lt (hB u)]
    exact (minRecv_le_self _ _).trans (floodVal_le_init hB k v)

theorem floodVal_lt (hB : ∀ v, x₀ v < 2 ^ B) (k : ℕ) (v : V) : floodVal G x₀ B k v < 2 ^ B :=
  (floodVal_le_init G x₀ hB k v).trans_lt (hB v)

/-- A lower bound of all numbers stays one. -/
theorem le_floodVal (hB : ∀ v, x₀ v < 2 ^ B) {c : ℕ} (hc : ∀ u, c ≤ x₀ u) :
    ∀ k v, c ≤ floodVal G x₀ B k v
  | 0, v => hc v
  | k + 1, v => by
    rw [floodVal_succ G x₀ hB k v (floodVal_lt G x₀ hB k)]
    refine le_minRecv (le_floodVal hB hc k v) fun u y h => ?_
    split_ifs at h
    · cases h
      exact le_floodVal hB hc k u

/-- The number at a node after `k` rounds is at most the number of every node within `k` hops. -/
theorem floodVal_le_walk (hB : ∀ v, x₀ v < 2 ^ B) :
    ∀ (k : ℕ) {u v : V} (p : G.Walk v u), p.length ≤ k → floodVal G x₀ B k v ≤ x₀ u
  | 0, _, _, .nil, _ => le_rfl
  | 0, _, _, .cons _ _, h => by simp at h
  | k + 1, _, _, .nil, _ =>
    (floodVal_le_init G x₀ hB (k + 1) _)
  | k + 1, u, v, .cons (v := w) hvw p, h => by
    rw [floodVal_succ G x₀ hB k v (floodVal_lt G x₀ hB k)]
    refine (minRecv_le (u := w) (y := floodVal G x₀ B k w) ?_).trans
      (floodVal_le_walk hB k p (by simp at h; omega))
    simp [hvw.symm]

/-- **The least number of the network in `D` rounds.** On a graph in which any two nodes are joined
by a walk of length at most `D`, with numbers below `2 ^ B`, after `D` rounds of `minFlood B` every
node holds the least number `c` of the network. -/
theorem run_minFlood (hB : ∀ v, x₀ v < 2 ^ B) {D : ℕ} (hD : ∀ u v, ∃ p : G.Walk u v, p.length ≤ D)
    {c : ℕ} (hc : ∀ u, c ≤ x₀ u) (hc' : ∃ u, x₀ u = c) (v : V) :
    ((minFlood B).run G x₀ D v).1 = c := by
  have e := run_iter (exch V B) (fun _ x => x) (fun _ x s => minRecv x s.2) G x₀ Nat.one_pos D 0
    Nat.one_pos
  rw [Nat.mul_one, Nat.add_zero] at e
  show ((exch V B).iter 1 (fun _ x => x) (fun _ x s => minRecv x s.2) |>.run G x₀ D v).1 = c
  rw [e]
  obtain ⟨u, rfl⟩ := hc'
  obtain ⟨p, hp⟩ := hD v u
  exact le_antisymm (floodVal_le_walk G x₀ hB D p hp) (le_floodVal G x₀ hB hc D v)

end Cslib.Congest.Algorithm
