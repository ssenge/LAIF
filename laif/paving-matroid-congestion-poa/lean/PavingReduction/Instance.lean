import PavingReduction.Basic

/-!
# The instance of Theorem 1 in this model

Resources 0, ..., 4 with classes {0, 1}, {2, 3}, {4}, delays a = (2, 2, 1, 0, 2), b = (0, 0, 0, 2, 0), three
players. The profile (0, 2), (0, 2), (1, 4) is an equilibrium of cost 16, and the profile (0, 2), (1, 3), (3, 4)
costs 11. So `Bound 3 r` fails for every r < 16/11.
-/

namespace PavingReduction

def cls5 : Fin 5 → ℕ := ![0, 0, 1, 1, 2]
def an : Fin 5 → ℕ := ![2, 2, 1, 0, 2]
def bn : Fin 5 → ℕ := ![0, 0, 0, 2, 0]
def a5 : Fin 5 → ℚ := fun e => an e
def b5 : Fin 5 → ℚ := fun e => bn e
def F5 : Fin 3 → Fin 5 × Fin 5 := ![(0, 2), (0, 2), (1, 4)]
def H5 : Fin 3 → Fin 5 × Fin 5 := ![(0, 2), (1, 3), (3, 4)]

theorem F5_valid : Valid cls5 F5 := by unfold Valid; decide

theorem H5_valid : Valid cls5 H5 := by unfold Valid; decide

theorem F5_ne : IsNE cls5 a5 b5 F5 := by
  have key : ∀ i g h, cls5 g ≠ cls5 h →
      an (F5 i).1 * load F5 (F5 i).1 + bn (F5 i).1 + (an (F5 i).2 * load F5 (F5 i).2 + bn (F5 i).2) ≤
        an g * (load F5 g + 1 - uses (F5 i) g) + bn g + (an h * (load F5 h + 1 - uses (F5 i) h) + bn h) := by
    unfold load uses; decide
  intro i g h hgh
  unfold own dev delay a5 b5
  exact_mod_cast key i g h hgh

theorem F5_cost : cost a5 b5 F5 = 16 := by
  have key : ∑ e, load F5 e * (an e * load F5 e + bn e) = 16 := by unfold load uses; decide
  unfold cost delay a5 b5
  exact_mod_cast key

theorem H5_cost : cost a5 b5 H5 = 11 := by
  have key : ∑ e, load H5 e * (an e * load H5 e + bn e) = 11 := by unfold load uses; decide
  unfold cost delay a5 b5
  exact_mod_cast key

/-- No bound below 16/11 holds for three players. -/
theorem not_bound (r : ℚ) (hr : r < 16 / 11) : ¬ Bound 3 r := by
  intro hB
  have h := hB (Fin 5) cls5 a5 b5 F5 H5 (fun e => by unfold a5; positivity) (fun e => by unfold b5; positivity) F5_valid H5_valid F5_ne
  rw [F5_cost, H5_cost] at h
  linarith

end PavingReduction
