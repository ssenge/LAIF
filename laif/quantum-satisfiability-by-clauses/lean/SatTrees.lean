import Mathlib

/-!
Node counts of search trees, and the numeric certificates of the quantum bounds for satisfiability.

A search tree carries a label at every node (the instance) and lists its children. Two counting
principles bound the number of nodes:

* a potential `Φ` with `1 ≤ Φ` at a leaf and `1 + ∑ Φ(child) ≤ Φ` at a node bounds the size by
  `Φ(root)`;
* a measure `μ ≥ 0` with `∑ c ^ μ(child) ≤ c ^ μ` at every node, and a height `h` that drops by one
  from a node to each child, bound the size by `(h(root) + 1) c ^ μ(root)`; with attachment
  nodes, whose subtrees have at most `p c ^ μ` nodes, the bound is `(h(root) + 1) p c ^ μ(root)`.

The amortized count for SAT in terms of the number `m` of clauses uses the first principle with
`Φ = c₁ g ^ m - 1` for good and `Φ = c₂ g ^ m - 1` for bad formulas, `g = 1.2226`, `c₁ = 2` and
`c₂ = c₁ / 0.9136`. The branching patterns are hypotheses: the case analysis that produces them
is not formalized.

The self-reduction fixes the variables of an assignment one at a time, each to a value that keeps
the optimum of a function `f` over the completions, and ends with an optimal assignment.
-/

namespace SatTrees

/-- A search tree with labels in `α`: a node with label `a` and `k` children. A leaf has `k = 0`. -/
inductive Tree (α : Type) where
  | node (a : α) (k : ℕ) (c : Fin k → Tree α) : Tree α

namespace Tree

variable {α : Type}

/-- The label of the root. -/
def label : Tree α → α
  | node a _ _ => a

/-- Number of nodes. -/
def size : Tree α → ℕ
  | node _ _ c => 1 + ∑ i, (c i).size

/-- Every node pays for itself and its subtrees through the potential `Φ`. -/
def Pays (Φ : α → ℝ) : Tree α → Prop
  | node a _ c => (1 + ∑ i, Φ (c i).label ≤ Φ a) ∧ ∀ i, Pays Φ (c i)

theorem size_le_of_pays (Φ : α → ℝ) : ∀ t : Tree α, Pays Φ t → (t.size : ℝ) ≤ Φ t.label
  | node a k c, ⟨h, hc⟩ => by
    have ih : ∀ i, ((c i).size : ℝ) ≤ Φ (c i).label := fun i => size_le_of_pays Φ (c i) (hc i)
    show ((1 + ∑ i, (c i).size : ℕ) : ℝ) ≤ Φ a
    push_cast
    linarith [Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ih i)]

/-- Branching with measure `μ` and height `h`: at every node `∑ c ^ μ(child) ≤ c ^ μ`, the measure
is nonnegative, and the height drops by at least one to each child. -/
def Branches (c : ℝ) (μ h : α → ℝ) : Tree α → Prop
  | node a _ cs => 0 ≤ μ a ∧ 0 ≤ h a ∧ (∑ i, c ^ μ (cs i).label ≤ c ^ μ a) ∧
      ∀ i, h (cs i).label + 1 ≤ h a ∧ Branches c μ h (cs i)

theorem pays_of_branches (c : ℝ) (hc : 1 ≤ c) (μ h : α → ℝ) :
    ∀ t : Tree α, Branches c μ h t → Pays (fun a => (h a + 1) * c ^ μ a) t
  | node a k cs, ⟨hμ, hh, hsum, hcs⟩ => by
    refine ⟨?_, fun i => pays_of_branches c hc μ h (cs i) (hcs i).2⟩
    show 1 + ∑ i, (h (cs i).label + 1) * c ^ μ (cs i).label ≤ (h a + 1) * c ^ μ a
    have hpos : ∀ i, 0 ≤ c ^ μ (cs i).label := fun i => by positivity
    have hstep : ∀ i, (h (cs i).label + 1) * c ^ μ (cs i).label ≤ h a * c ^ μ (cs i).label :=
      fun i => mul_le_mul_of_nonneg_right (hcs i).1 (hpos i)
    have h1 : (1 : ℝ) ≤ c ^ μ a := Real.one_le_rpow hc hμ
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hstep i)
    rw [← Finset.mul_sum] at hs
    have : h a * ∑ i, c ^ μ (cs i).label ≤ h a * c ^ μ a := mul_le_mul_of_nonneg_left hsum hh
    have e : (h a + 1) * c ^ μ a = h a * c ^ μ a + c ^ μ a := by ring
    linarith

/-- The size bound from branching numbers: at most `(h(root) + 1) c ^ μ(root)` nodes. -/
theorem size_le_of_branches (c : ℝ) (hc : 1 ≤ c) (μ h : α → ℝ) (t : Tree α)
    (ht : Branches c μ h t) : (t.size : ℝ) ≤ (h t.label + 1) * c ^ μ t.label :=
  size_le_of_pays _ t (pays_of_branches c hc μ h t ht)

/-- Branching with attachment nodes: at every node the measure and the height are nonnegative,
and either the subtree has at most `p c ^ μ` nodes (an attachment node, whose subtree is the tree of
another algorithm), or `∑ c ^ μ(child) ≤ c ^ μ` and the height drops by at least one to each child,
which again satisfy the condition. -/
def BranchesAt (c p : ℝ) (μ h : α → ℝ) : Tree α → Prop
  | node a k cs => 0 ≤ μ a ∧ 0 ≤ h a ∧
      (((node a k cs).size : ℝ) ≤ p * c ^ μ a ∨
        ((∑ i, c ^ μ (cs i).label ≤ c ^ μ a) ∧
          ∀ i, h (cs i).label + 1 ≤ h a ∧ BranchesAt c p μ h (cs i)))

/-- The counting lemma with attachment nodes: at most `(h(root) + 1) p c ^ μ(root)` nodes. -/
theorem size_le_of_branchesAt (c p : ℝ) (hc : 1 ≤ c) (hp : 1 ≤ p) (μ h : α → ℝ) :
    ∀ t : Tree α, BranchesAt c p μ h t → (t.size : ℝ) ≤ (h t.label + 1) * p * c ^ μ t.label
  | node a k cs, ⟨hμ, hh, hor⟩ => by
    have h1 : (1 : ℝ) ≤ c ^ μ a := Real.one_le_rpow hc hμ
    have hpc : 1 ≤ p * c ^ μ a := by nlinarith
    show ((node a k cs).size : ℝ) ≤ (h a + 1) * p * c ^ μ a
    rcases hor with hs | ⟨hsum, hcs⟩
    · have : p * c ^ μ a ≤ (h a + 1) * p * c ^ μ a := by nlinarith
      linarith
    · have ih : ∀ i, ((cs i).size : ℝ) ≤ (h (cs i).label + 1) * p * c ^ μ (cs i).label :=
        fun i => size_le_of_branchesAt c p hc hp μ h (cs i) (hcs i).2
      have hstep : ∀ i, ((cs i).size : ℝ) ≤ (h a * p) * c ^ μ (cs i).label := fun i => by
        have hci : 0 ≤ c ^ μ (cs i).label := by positivity
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hcs i).1 (by linarith : (0 : ℝ) ≤ p)) hci
        linarith [ih i]
      have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hstep i)
      rw [← Finset.mul_sum] at hs
      have hhp : 0 ≤ h a * p := mul_nonneg hh (by linarith)
      have := mul_le_mul_of_nonneg_left hsum hhp
      show ((1 + ∑ i, (cs i).size : ℕ) : ℝ) ≤ (h a + 1) * p * c ^ μ a
      push_cast
      nlinarith

end Tree

/-- A branching vector `d` with `∑ c ^ (-dᵢ) ≤ 1` gives the step condition of `Branches`. -/
theorem branch_step {k : ℕ} (c : ℝ) (hc : 0 < c) (μ : ℝ) (μs d : Fin k → ℝ)
    (hd : ∀ i, μs i ≤ μ - d i) (hc1 : 1 ≤ c) (hτ : ∑ i, c ^ (-d i) ≤ 1) :
    ∑ i, c ^ μs i ≤ c ^ μ := by
  calc ∑ i, c ^ μs i ≤ ∑ i, c ^ μ * c ^ (-d i) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Real.rpow_add hc]
        exact Real.rpow_le_rpow_of_exponent_le hc1 (by linarith [hd i])
    _ = c ^ μ * ∑ i, c ^ (-d i) := by rw [Finset.mul_sum]
    _ ≤ c ^ μ * 1 := mul_le_mul_of_nonneg_left hτ (by positivity)
    _ = c ^ μ := mul_one _

/-! ### Numeric certificates -/

/-- XSAT: `√1.1674 ≤ 1.0805`. -/
theorem xsat_root : (11674 / 10000 : ℝ) ≤ (10805 / 10000) ^ 2 := by norm_num

/-- X3SAT: `1.1003` is at least the branching numbers of `(12, 4)`, `(11, 5)`, `(9, 6)`, `(8, 7)`. -/
theorem x3sat_vectors :
    (10000 / 11003 : ℝ) ^ 12 + (10000 / 11003) ^ 4 ≤ 1 ∧
    (10000 / 11003 : ℝ) ^ 11 + (10000 / 11003) ^ 5 ≤ 1 ∧
    (10000 / 11003 : ℝ) ^ 9 + (10000 / 11003) ^ 6 ≤ 1 ∧
    (10000 / 11003 : ℝ) ^ 8 + (10000 / 11003) ^ 7 ≤ 1 := by norm_num

/-- X3SAT: the sparse enumeration `2 ^ (2n/15)` is below `1.1003 ^ n`, and `√1.1003 ≤ 1.0490`. -/
theorem x3sat_sparse_root : (2 : ℝ) ^ 2 ≤ (11003 / 10000) ^ 15 ∧
    (11003 / 10000 : ℝ) ≤ (10490 / 10000) ^ 2 := by norm_num

/-- X3SAT in terms of clauses: `1.1586` is at least the branching numbers of `(7, 3)`, `(6, 4)` and
`(5, 5)`, and `√1.1586 ≤ 1.0764`. -/
theorem x3satm_cert :
    (10000 / 11586 : ℝ) ^ 7 + (10000 / 11586) ^ 3 ≤ 1 ∧
    (10000 / 11586 : ℝ) ^ 6 + (10000 / 11586) ^ 4 ≤ 1 ∧
    (10000 / 11586 : ℝ) ^ 5 + (10000 / 11586) ^ 5 ≤ 1 ∧
    (11586 / 10000 : ℝ) ≤ (10764 / 10000) ^ 2 := by norm_num

/-- MaxSAT: `1.2886` is at least the branching number of `(6, 6, 5, 5)` and the set cover base
`1.2576`, and `√1.2886 ≤ 1.1352`. -/
theorem maxsat_cert :
    2 * (10000 / 12886 : ℝ) ^ 6 + 2 * (10000 / 12886) ^ 5 ≤ 1 ∧
    (12576 / 10000 : ℝ) ≤ 12886 / 10000 ∧ (12886 / 10000 : ℝ) ≤ (11352 / 10000) ^ 2 := by
  norm_num

/-- SAT in terms of the length: `√(2 ^ 0.0926) ≤ 1.0327`. -/
theorem satl_root : (2 : ℝ) ^ ((463 : ℝ) / 5000) ≤ (10327 / 10000) ^ 2 := by
  have hb : (0 : ℝ) ≤ (10327 / 10000) ^ 2 := by positivity
  -- `0.0926 ≤ 9/97` and `2 ^ 9 ≤ 1.0327 ^ 194`
  have key : (2 : ℝ) ^ (9 : ℕ) ≤ ((10327 / 10000 : ℝ) ^ 2) ^ (97 : ℕ) := by norm_num
  calc (2 : ℝ) ^ ((463 : ℝ) / 5000) ≤ (2 : ℝ) ^ ((9 : ℝ) / 97) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = ((2 : ℝ) ^ (9 : ℕ)) ^ ((1 : ℝ) / 97) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    _ ≤ (((10327 / 10000 : ℝ) ^ 2) ^ (97 : ℕ)) ^ ((1 : ℝ) / 97) :=
        Real.rpow_le_rpow (by positivity) key (by norm_num)
    _ = (10327 / 10000) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hb]; norm_num

/-- The comparisons behind the `1.0638^L` tree for SAT in terms of the formula length: the
3-SAT part with `n` variables of weight 5 has `1.34^n ≤ (1.0638^5)^n` nodes; the formula of maximum
degree 3 with `n` variables of weight `w₃ = 1.94719 ≥ 109/56` has `1.1279^n ≤ 1.0638^(w₃ n)` nodes,
since `1.1279^56 ≤ 1.0638^109`; and `√1.0638 ≤ 1.0315`. -/
theorem satl2_cert :
    (134 / 100 : ℝ) ≤ (10638 / 10000) ^ 5 ∧
    (11279 / 10000 : ℝ) ^ 56 ≤ (10638 / 10000) ^ 109 ∧ (109 / 56 : ℝ) ≤ 194719 / 100000 ∧
    (10638 / 10000 : ℝ) ≤ (10315 / 10000) ^ 2 := by norm_num

/-! ### The amortized count for SAT in terms of clauses -/

/-- The base `g = 1.2226` and the constants `c₁ = 2`, `c₂ = c₁ / 0.9136`. -/
noncomputable def g : ℝ := 12226 / 10000
noncomputable def c₁ : ℝ := 2
noncomputable def c₂ : ℝ := 2 / (9136 / 10000)

/-- The constant of a formula: `c₁` if it is good, `c₂` if it is bad. -/
noncomputable def cst : Bool → ℝ
  | true => c₁
  | false => c₂

/-- The potential of a formula with `m` clauses. -/
noncomputable def Φ : Bool × ℕ → ℝ
  | (b, m) => cst b * g ^ m - 1

lemma g_pos : 0 < g := by unfold g; norm_num
lemma one_le_g : 1 ≤ g := by unfold g; norm_num
lemma c₁_pos : 0 < c₁ := by unfold c₁; norm_num
lemma c₁_le_c₂ : c₁ ≤ c₂ := by unfold c₁ c₂; norm_num
lemma cst_le_c₂ : ∀ b : Bool, cst b ≤ c₂
  | true => c₁_le_c₂
  | false => le_rfl
lemma two_le_cst : ∀ b : Bool, 2 ≤ cst b
  | true => by show (2 : ℝ) ≤ c₁; unfold c₁; norm_num
  | false => by show (2 : ℝ) ≤ c₂; unfold c₂; norm_num
lemma cst_pos (b : Bool) : 0 < cst b := lt_of_lt_of_le (by norm_num) (two_le_cst b)

/-- The inequalities of the substitution proof, in exact arithmetic: one for each branching
pattern (with the two children in either order), and `c₂ ≤ g c₁` for reduction. -/
theorem amortized_inequalities :
    c₂ * g⁻¹ ^ 3 + c₂ * g⁻¹ ^ 4 ≤ c₂ ∧ c₂ * g⁻¹ ^ 4 + c₂ * g⁻¹ ^ 3 ≤ c₂ ∧
    c₁ * g⁻¹ ^ 3 + c₁ * g⁻¹ ^ 3 ≤ c₂ ∧
    c₂ * g⁻¹ ^ 3 + c₂ * g⁻¹ ^ 5 ≤ c₁ ∧ c₂ * g⁻¹ ^ 5 + c₂ * g⁻¹ ^ 3 ≤ c₁ ∧
    c₂ * g⁻¹ ^ 4 + c₂ * g⁻¹ ^ 4 ≤ c₁ ∧
    c₁ * g⁻¹ ^ 3 + c₁ * g⁻¹ ^ 4 ≤ c₁ ∧ c₁ * g⁻¹ ^ 4 + c₁ * g⁻¹ ^ 3 ≤ c₁ ∧
    c₂ ≤ g * c₁ := by
  unfold c₁ c₂ g; norm_num

/-- Reduction: a formula `(b, m)` reduced to `(b', m')` with `m' ≤ m`, and with `m' + 1 ≤ m` when a
good formula becomes bad. -/
def Reduces : Bool × ℕ → Bool × ℕ → Prop
  | (b, m), (b', m') => m' ≤ m ∧ (b = true → b' = false → m' + 1 ≤ m)

/-- Reduction does not raise the potential. -/
lemma Φ_reduces : ∀ {x y : Bool × ℕ}, Reduces x y → Φ y ≤ Φ x
  | (b, m), (b', m'), ⟨hm, hgb⟩ => by
    show cst b' * g ^ m' - 1 ≤ cst b * g ^ m - 1
    have gm : g ^ m' ≤ g ^ m := pow_le_pow_right₀ one_le_g hm
    have gpos : 0 ≤ g ^ m' := pow_nonneg g_pos.le m'
    have c₂pos : 0 ≤ c₂ := le_trans c₁_pos.le c₁_le_c₂
    cases b <;> cases b'
    · -- bad to bad
      show c₂ * g ^ m' - 1 ≤ c₂ * g ^ m - 1
      linarith [mul_le_mul_of_nonneg_left gm c₂pos]
    · -- bad to good
      show c₁ * g ^ m' - 1 ≤ c₂ * g ^ m - 1
      linarith [mul_le_mul_of_nonneg_right c₁_le_c₂ gpos, mul_le_mul_of_nonneg_left gm c₂pos]
    · -- good to bad: one clause fewer, and `c₂ ≤ g c₁`
      show c₂ * g ^ m' - 1 ≤ c₁ * g ^ m - 1
      have hm1 : m' + 1 ≤ m := hgb rfl rfl
      have gm1 : g ^ (m' + 1) ≤ g ^ m := pow_le_pow_right₀ one_le_g hm1
      have h6 := amortized_inequalities.2.2.2.2.2.2.2.2
      have s : c₂ * g ^ m' ≤ g * c₁ * g ^ m' := mul_le_mul_of_nonneg_right h6 gpos
      have e : g * c₁ * g ^ m' = c₁ * g ^ (m' + 1) := by rw [pow_succ]; ring
      linarith [mul_le_mul_of_nonneg_left gm1 c₁_pos.le]
    · -- good to good
      show c₁ * g ^ m' - 1 ≤ c₁ * g ^ m - 1
      linarith [mul_le_mul_of_nonneg_left gm c₁_pos.le]

/-- The branching patterns of the algorithm for SAT on a reduced formula `(b, m)` with the two
formulas `y₀, y₁` produced by the branching (before reduction). A bad formula branches with
`(3, 4)` or `(4, 3)`, or with `(3, 3)` into two good formulas. A good formula branches with `(3, 5)`,
`(5, 3)` or `(4, 4)`, or with `(3, 4)` or `(4, 3)` into two good formulas. -/
def Pattern : Bool × ℕ → Bool × ℕ → Bool × ℕ → Prop
  | (false, m), (b₀, m₀), (b₁, m₁) =>
      (m₀ + 3 ≤ m ∧ m₁ + 4 ≤ m) ∨ (m₀ + 4 ≤ m ∧ m₁ + 3 ≤ m) ∨
      (b₀ = true ∧ b₁ = true ∧ m₀ + 3 ≤ m ∧ m₁ + 3 ≤ m)
  | (true, m), (b₀, m₀), (b₁, m₁) =>
      (m₀ + 3 ≤ m ∧ m₁ + 5 ≤ m) ∨ (m₀ + 5 ≤ m ∧ m₁ + 3 ≤ m) ∨ (m₀ + 4 ≤ m ∧ m₁ + 4 ≤ m) ∨
      (b₀ = true ∧ b₁ = true ∧ ((m₀ + 3 ≤ m ∧ m₁ + 4 ≤ m) ∨ (m₀ + 4 ≤ m ∧ m₁ + 3 ≤ m)))

/-- `g ^ a ≤ g ^ m g⁻¹ ^ d` when `a + d ≤ m`. -/
lemma g_split {a d m : ℕ} (hm : a + d ≤ m) : g ^ a ≤ g ^ m * g⁻¹ ^ d := by
  have hg := g_pos
  have e : g ^ m = g ^ (m - (a + d)) * g ^ a * g ^ d := by
    rw [mul_assoc, ← pow_add, ← pow_add]; congr 1; omega
  rw [e, inv_pow, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ one_le_g)

/-- Closing step: two children bounded by `Kᵢ G eᵢ` with `K₀ e₀ + K₁ e₁ ≤ C` pay for a node. -/
lemma close {X₀ X₁ K₀ K₁ C G e₀ e₁ : ℝ} (hG : 0 ≤ G) (h₀ : X₀ ≤ K₀ * G * e₀)
    (h₁ : X₁ ≤ K₁ * G * e₁) (hi : K₀ * e₀ + K₁ * e₁ ≤ C) : 1 + (X₀ - 1) + (X₁ - 1) ≤ C * G - 1 := by
  have h2 : G * (K₀ * e₀ + K₁ * e₁) ≤ G * C := mul_le_mul_of_nonneg_left hi hG
  have e : K₀ * G * e₀ + K₁ * G * e₁ = G * (K₀ * e₀ + K₁ * e₁) := by ring
  have e2 : C * G = G * C := by ring
  linarith

lemma pattern_pays : ∀ {x y₀ y₁ : Bool × ℕ}, Pattern x y₀ y₁ → 1 + Φ y₀ + Φ y₁ ≤ Φ x
  | (b, m), (b₀, m₀), (b₁, m₁), h => by
    obtain ⟨i1, i1', i2, i3, i3', i4, i5, i5', _⟩ := amortized_inequalities
    have gmp : 0 ≤ g ^ m := pow_nonneg g_pos.le m
    -- a child at distance `d` with its own constant, and with the larger constant `c₂`
    have child : ∀ (bb : Bool) (mm d : ℕ), mm + d ≤ m → cst bb * g ^ mm ≤ cst bb * g ^ m * g⁻¹ ^ d :=
      fun bb mm d hd => by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (g_split hd) (cst_pos bb).le
    have any : ∀ (bb : Bool) (mm d : ℕ), mm + d ≤ m → cst bb * g ^ mm ≤ c₂ * g ^ m * g⁻¹ ^ d :=
      fun bb mm d hd => (child bb mm d hd).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (cst_le_c₂ bb) gmp) (pow_nonneg (inv_nonneg.2 g_pos.le) d))
    show 1 + (cst b₀ * g ^ m₀ - 1) + (cst b₁ * g ^ m₁ - 1) ≤ cst b * g ^ m - 1
    cases b
    · -- bad formula
      show 1 + (cst b₀ * g ^ m₀ - 1) + (cst b₁ * g ^ m₁ - 1) ≤ c₂ * g ^ m - 1
      rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨e0, e1, h0, h1⟩
      · exact close gmp (any b₀ m₀ 3 h0) (any b₁ m₁ 4 h1) i1
      · exact close gmp (any b₀ m₀ 4 h0) (any b₁ m₁ 3 h1) i1'
      · subst e0; subst e1
        exact close gmp (child true m₀ 3 h0) (child true m₁ 3 h1) i2
    · -- good formula
      show 1 + (cst b₀ * g ^ m₀ - 1) + (cst b₁ * g ^ m₁ - 1) ≤ c₁ * g ^ m - 1
      rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨h0, h1⟩ | ⟨e0, e1, ⟨h0, h1⟩ | ⟨h0, h1⟩⟩
      · exact close gmp (any b₀ m₀ 3 h0) (any b₁ m₁ 5 h1) i3
      · exact close gmp (any b₀ m₀ 5 h0) (any b₁ m₁ 3 h1) i3'
      · exact close gmp (any b₀ m₀ 4 h0) (any b₁ m₁ 4 h1) i4
      · subst e0; subst e1
        exact close gmp (child true m₀ 3 h0) (child true m₁ 4 h1) i5
      · subst e0; subst e1
        exact close gmp (child true m₀ 4 h0) (child true m₁ 3 h1) i5'

/-- The search tree of the algorithm for SAT, with labels (good, number of clauses) of the reduced
formulas: a leaf, or two children that arise from formulas `y₀, y₁` in one of the patterns, each
reduced to the label of its child. -/
def SatTree : Tree (Bool × ℕ) → Prop
  | .node x k c => k = 0 ∨ ∃ h : k = 2,
      (∃ y₀ y₁, Pattern x y₀ y₁ ∧ Reduces y₀ (c ⟨0, by omega⟩).label ∧
        Reduces y₁ (c ⟨1, by omega⟩).label) ∧
      ∀ i, SatTree (c i)

/-- The amortized count: the search tree of the algorithm on a reduced formula with `m` clauses
has at most `c₁ g ^ m - 1` nodes if the formula is good and `c₂ g ^ m - 1` if it is bad. -/
theorem sat_tree_pays : ∀ t : Tree (Bool × ℕ), SatTree t → Tree.Pays Φ t
  | .node x k c, h => by
    have hrec : ∀ i, SatTree (c i) → Tree.Pays Φ (c i) := fun i hi => sat_tree_pays (c i) hi
    rcases h with h0 | ⟨rfl, ⟨y₀, y₁, hp, r₀, r₁⟩, hc⟩
    · subst h0
      refine ⟨?_, fun i => i.elim0⟩
      obtain ⟨b, m⟩ := x
      show 1 + ∑ i : Fin 0, Φ (c i).label ≤ cst b * g ^ m - 1
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      have := two_le_cst b
      have : (1 : ℝ) ≤ g ^ m := one_le_pow₀ one_le_g
      nlinarith
    · refine ⟨?_, fun i => hrec i (hc i)⟩
      have r₀' : Reduces y₀ (c 0).label := r₀
      have r₁' : Reduces y₁ (c 1).label := r₁
      show 1 + ∑ i, Φ (c i).label ≤ Φ x
      rw [Fin.sum_univ_two]
      have := pattern_pays hp
      linarith [Φ_reduces r₀', Φ_reduces r₁']

theorem sat_tree_size (t : Tree (Bool × ℕ)) (ht : SatTree t) : (t.size : ℝ) ≤ Φ t.label :=
  Tree.size_le_of_pays Φ t (sat_tree_pays t ht)

/-- The quantum base: `√1.2226 ≤ 1.1058`. -/
theorem sat_root : g ≤ (11058 / 10000) ^ 2 := by unfold g; norm_num

/-! ### Self-reduction -/

section SelfReduction

variable {n : ℕ} (f : (Fin n → Bool) → ℕ)

/-- The optimum of `f` over the assignments that agree with `y` on the first `k` variables. -/
def best (k : ℕ) (y : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun x : Fin n → Bool => ∀ i : Fin n, i.val < k → x i = y i)).sup f

lemma best_zero (y : Fin n → Bool) : best f 0 y = Finset.univ.sup f := by
  unfold best
  rw [Finset.filter_true_of_mem (fun x _ i hi => absurd hi (Nat.not_lt_zero _))]

lemma best_n (y : Fin n → Bool) : best f n y = f y := by
  unfold best
  apply le_antisymm
  · refine Finset.sup_le fun x hx => ?_
    have : x = y := funext fun i => (Finset.mem_filter.1 hx).2 i i.isLt
    rw [this]
  · exact Finset.le_sup (Finset.mem_filter.2 ⟨Finset.mem_univ _, fun _ _ => rfl⟩)

/-- Fixing the next variable to the right value keeps the optimum. -/
lemma exists_step (k : ℕ) (hk : k < n) (y : Fin n → Bool) :
    ∃ b, best f (k + 1) (Function.update y ⟨k, hk⟩ b) = best f k y := by
  set S := Finset.univ.filter (fun x : Fin n → Bool => ∀ i : Fin n, i.val < k → x i = y i)
  have hy : y ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, fun _ _ => rfl⟩
  obtain ⟨x, hx, hxs⟩ := Finset.exists_mem_eq_sup S ⟨y, hy⟩ f
  have hxk := (Finset.mem_filter.1 hx).2
  refine ⟨x ⟨k, hk⟩, le_antisymm ?_ ?_⟩
  · refine Finset.sup_mono fun z hz => Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i hi => ?_⟩
    have hz' := (Finset.mem_filter.1 hz).2 i (by omega)
    have hne : i ≠ ⟨k, hk⟩ := fun e => by rw [e] at hi; exact lt_irrefl _ hi
    rw [hz', Function.update_of_ne hne]
  · show S.sup f ≤ _
    rw [hxs]
    refine Finset.le_sup (Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i hi => ?_⟩)
    by_cases e : i = ⟨k, hk⟩
    · subst e; rw [Function.update_self]
    · rw [Function.update_of_ne e]
      exact hxk i (lt_of_le_of_ne (Nat.lt_succ_iff.1 hi) (fun h => e (Fin.ext h)))

/-- The self-reduction: fix the variables in order, each to `false` if that keeps the optimum and
to `true` otherwise. Each step compares two values of `best`. -/
def greedy : (k : ℕ) → k ≤ n → (Fin n → Bool)
  | 0, _ => fun _ => false
  | k + 1, hk =>
    let y := greedy k (by omega)
    let i : Fin n := ⟨k, by omega⟩
    if best f (k + 1) (Function.update y i false) = best f k y then Function.update y i false
    else Function.update y i true

lemma best_greedy : ∀ (k : ℕ) (hk : k ≤ n), best f k (greedy f k hk) = Finset.univ.sup f
  | 0, _ => best_zero f _
  | k + 1, hk => by
    have ih := best_greedy k (by omega)
    obtain ⟨b, hb⟩ := exists_step f k (by omega) (greedy f k (by omega))
    unfold greedy
    simp only
    split_ifs with h
    · rw [h, ih]
    · cases b
      · exact absurd hb h
      · rw [hb, ih]

/-- The assignment found by the self-reduction is optimal: `f (greedy) ≥ f x` for every `x`. For
the indicator of a satisfying assignment it finds one whenever one exists. -/
theorem greedy_optimal (x : Fin n → Bool) : f x ≤ f (greedy f n le_rfl) := by
  have h := best_greedy f n le_rfl
  rw [best_n] at h
  rw [h]
  exact Finset.le_sup (Finset.mem_univ x)

end SelfReduction

end SatTrees
