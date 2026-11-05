import Mathlib.Tactic

/-!
# The table of bases

Each quantum base of the table, squared, is at least the classical base. All the inequalities are
strict. `quantum_le_classical` collects them.
-/

namespace QuantumBranching

theorem table_vc_randomized : (1.25281 : ℝ) < (1.1193 : ℝ) ^ 2 := by norm_num
theorem table_vc_deterministic : (1.25284 : ℝ) < (1.1194 : ℝ) ^ 2 := by norm_num
theorem table_deg3_randomized : (1.13132 : ℝ) < (1.0637 : ℝ) ^ 2 := by norm_num
theorem table_deg3_deterministic : (1.14416 : ℝ) < (1.0697 : ℝ) ^ 2 := by norm_num
theorem table_deg4_randomized : (1.21103 : ℝ) < (1.1005 : ℝ) ^ 2 := by norm_num
theorem table_deg4_deterministic : (1.21131 : ℝ) < (1.1006 : ℝ) ^ 2 := by norm_num
theorem table_deg5_randomized : (1.24382 : ℝ) < (1.1153 : ℝ) ^ 2 := by norm_num
theorem table_deg5_deterministic : (1.24394 : ℝ) < (1.1154 : ℝ) ^ 2 := by norm_num
theorem table_deg6_randomized : (1.25210 : ℝ) < (1.1190 : ℝ) ^ 2 := by norm_num
theorem table_deg6_deterministic : (1.25214 : ℝ) < (1.1190 : ℝ) ^ 2 := by norm_num
theorem table_mis : (1.19951 : ℝ) < (1.0953 : ℝ) ^ 2 := by norm_num
theorem table_mis3_randomized : (1.07625 : ℝ) < (1.0375 : ℝ) ^ 2 := by norm_num
theorem table_mis3_deterministic : (1.083506 : ℝ) < (1.0410 : ℝ) ^ 2 := by norm_num
theorem table_mis4_randomized : (1.13735 : ℝ) < (1.0665 : ℝ) ^ 2 := by norm_num
theorem table_mis4_deterministic : (1.13760 : ℝ) < (1.0666 : ℝ) ^ 2 := by norm_num
theorem table_above_lp : (2.3146 : ℝ) < (1.5214 : ℝ) ^ 2 := by norm_num

/-- The bases of the table, in order, as pairs of the quantum base and the classical base. -/
def tableEntries : List (ℚ × ℚ) :=
  [(1.1193, 1.25281), (1.1194, 1.25284), (1.0637, 1.13132), (1.0697, 1.14416), (1.1005, 1.21103),
   (1.1006, 1.21131), (1.1153, 1.24382), (1.1154, 1.24394), (1.1190, 1.25210), (1.1190, 1.25214),
   (1.0953, 1.19951), (1.0375, 1.07625), (1.0410, 1.083506), (1.0665, 1.13735), (1.0666, 1.13760),
   (1.5214, 2.3146)]

/-- Every entry of the table has square above the classical base. -/
theorem quantum_le_classical : ∀ e ∈ tableEntries, e.2 < e.1 ^ 2 := by
  intro e he
  simp only [tableEntries, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl <;> norm_num

/-- The base `1.1006` is the least with four decimals for `1.21131`: one unit less fails. -/
theorem table_tight_deg4 : (1.1005 : ℝ) ^ 2 < 1.21131 := by norm_num

/-- The base `1.0666` is the least with four decimals for `1.13760`: one unit less fails. -/
theorem table_tight_mis4 : (1.0665 : ℝ) ^ 2 < 1.13760 := by norm_num

end QuantumBranching
