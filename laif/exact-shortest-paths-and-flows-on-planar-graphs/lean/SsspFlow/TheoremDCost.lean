import SsspFlow.RunDepth
import SsspFlow.GHatLevelConn

/-!
# Rounds of Theorem D in a cost model

A level of a run makes a constant number of calls of three kinds on the network of the level: exact
shortest paths from a virtual source (`RotSystem.RData.levelSssp_sim`), the labels of the components
(`RotSystem.RData.levelConn_sim`), and part-wise aggregations, together with a constant number of
rounds of local exchange. The network of a level has `n' = 21 n²` identifiers and diameter at most
`12 D + 16`, and the nodes run it round for round. Part-wise aggregation on planar networks is
classical and is taken as a hypothesis (`PartAggBox`).

* `logN_level`: `log n' ≤ 7 log n`.
* `log_levels`: a run on a cut path of length `m ≤ n²` has at most `4 log n` levels
  (`CutPath.Run.nodes_eq_nil`).
* `theoremD_cost`: for any constant numbers of calls per level, the rounds of all levels are
  `O(log^{c+1} n · D)`.

This is a count of rounds over the levels in a cost model, not one algorithm of the message model
for the whole recursion.
-/

set_option autoImplicit false

namespace SsspFlow

namespace Congest

open Cslib.Congest

/-- Part-wise aggregation on planar networks, classical: for a partition of the nodes into parts
that are connected inside, every node learns the least value of its part in `Õ(D)` rounds, by the
low-congestion shortcuts of planar networks ([9, Cor. 4.6] of the README). Values have `O(log n)`
bits. -/
def PartAggBox : Prop :=
  ∃ C c : ℕ, ∀ n D : ℕ, 1 ≤ D →
    ∃ (σ : Type) (A : Algorithm (Fin n) (Fin n × Fin (2 ^ logN n)) σ (C * logN n ^ c))
      (out : Fin n → σ → ℕ),
      ∀ N : Net (Fin n), N.toRot.Planar → N.DiamLE D →
        ∀ (part : Fin n → Fin n) (val : Fin n → Fin (2 ^ logN n)),
          (∀ u v, part u = part v →
            Nonempty (Walk (fun a b => N.G.Adj a b ∧ part a = part u ∧ part b = part u) u v)) →
          ∀ v, IsLeast {m | ∃ u, part u = part v ∧ (val u : ℕ) = m}
            (out v (A.run N.G (fun u => (part u, val u)) (C * logN n ^ c * D) v))

theorem logN_level (n : ℕ) : logN (n * (n * 21)) ≤ 7 * logN n := by
  unfold logN
  have h1 : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  set L := Nat.log 2 (n + 2) + 1 with hL
  have h2 : n * (n * 21) + 2 < 2 ^ (2 * L + 5) := by
    have h3 : n * (n * 21) + 2 ≤ 32 * ((n + 2) * (n + 2)) := by nlinarith
    have h4 : (n + 2) * (n + 2) < 2 ^ L * 2 ^ L := Nat.mul_self_lt_mul_self h1
    have h5 : 2 ^ (2 * L + 5) = 32 * (2 ^ L * 2 ^ L) := by
      rw [pow_add, two_mul, pow_add]
      ring
    omega
  have h3 := Nat.log_lt_of_lt_pow (by omega) h2
  omega

theorem log_levels (n m : ℕ) (hm : m ≤ n * n) : Nat.log 2 m + 2 ≤ 4 * logN n := by
  unfold logN
  have h1 : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  set L := Nat.log 2 (n + 2) + 1 with hL
  have h2 : (n + 2) * (n + 2) < 2 ^ (2 * L) := by
    rw [two_mul, pow_add]
    exact Nat.mul_self_lt_mul_self h1
  have h3 : Nat.log 2 m ≤ Nat.log 2 ((n + 2) * (n + 2)) := Nat.log_mono_right (by nlinarith)
  have h4 := Nat.log_lt_of_lt_pow (by positivity) h2
  omega

/-- **Rounds of Theorem D, cost model.** With `kS` calls of shortest paths or labels and `kA`
part-wise aggregations on the network of a level, each in `C log^c n' · (12 D + 16)` and
`C_A log^{c_A} n' · (12 D + 16)` rounds, and `k₀` further rounds per level, all levels of a run on a cut
path of length `m ≤ n²` take `O(log^{c + c_A + 1} n · D)` rounds. -/
theorem theoremD_cost (C c CA cA kS kA k0 : ℕ) : ∃ C' c' : ℕ, ∀ n D m : ℕ, 1 ≤ D → m ≤ n * n →
    (Nat.log 2 m + 2) * (kS * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) +
      kA * (CA * logN (n * (n * 21)) ^ cA * (12 * D + 16)) + k0) ≤ C' * logN n ^ c' * D := by
  refine ⟨4 * (28 * kS * C * 7 ^ c + 28 * kA * CA * 7 ^ cA + k0), c + cA + 1, fun n D m hD hm => ?_⟩
  set L := logN n with hLdef
  have hL : 1 ≤ L := Nat.le_add_left _ _
  have hp : ∀ e, e ≤ c + cA → logN (n * (n * 21)) ^ e ≤ 7 ^ e * L ^ (c + cA) := fun e he =>
    (Nat.pow_le_pow_left (logN_level n) e).trans (by
      rw [mul_pow]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL he))
  have hP : 1 ≤ L ^ (c + cA) := Nat.one_le_pow _ _ hL
  have hk0 : k0 ≤ k0 * L ^ (c + cA) * D := by
    calc k0 = k0 * 1 * 1 := by ring
      _ ≤ k0 * L ^ (c + cA) * D := by gcongr
  calc (Nat.log 2 m + 2) * (kS * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) +
        kA * (CA * logN (n * (n * 21)) ^ cA * (12 * D + 16)) + k0)
      ≤ (4 * L) * (kS * (C * (7 ^ c * L ^ (c + cA)) * (28 * D)) +
        kA * (CA * (7 ^ cA * L ^ (c + cA)) * (28 * D)) + k0 * L ^ (c + cA) * D) := by
        refine Nat.mul_le_mul (log_levels n m hm) (Nat.add_le_add (Nat.add_le_add ?_ ?_) hk0)
        · gcongr
          · exact hp c (by omega)
          · omega
        · gcongr
          · exact hp cA (by omega)
          · omega
    _ = 4 * (28 * kS * C * 7 ^ c + 28 * kA * CA * 7 ^ cA + k0) * L ^ (c + cA + 1) * D := by ring

end Congest

end SsspFlow
