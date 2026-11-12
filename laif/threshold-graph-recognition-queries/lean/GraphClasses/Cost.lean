import GraphClasses.Threshold
import GraphClasses.Rounds
import GraphClasses.Model

/-!
# The cost accounting

This is accounting, not a compilation of `learn` into a quantum circuit. The expected cost is defined by the recursion
of Learn with uniform pivots, charging each node `c · m`. The theorems bound that recursion, and show which `c` a node
needs given the cost of quantum search and the expected rounds of Holding.
-/

open Finset

namespace GraphClasses

universe u v

variable {R C : Type*} [DecidableEq R] [DecidableEq C]

/-- A search on a block: `√(ab) ≤ (a + b) / 2`. That inequality is what makes this work. -/
theorem sqrt_mul_le_half (a b : ℕ) : Real.sqrt ((a : ℝ) * b) ≤ ((a : ℝ) + b) / 2 := by
  have ha : (0 : ℝ) ≤ a := by positivity
  have hb : (0 : ℝ) ≤ b := by positivity
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_nonneg ((a : ℝ) - b)]

/-! ## The recursion tree -/

/-- The three trimmed blocks of a node. -/
def children (M : R → C → Bool) (A : Finset R) (B : Finset C) (x : R) (w : C) : List (Finset R × Finset C) :=
  let b := splitBlocks M A B x w
  [(survR M b.1.1 b.1.2, survC M b.1.1 b.1.2), (survR M b.2.1.1 b.2.1.2, survC M b.2.1.1 b.2.1.2),
    (survR M b.2.2.1 b.2.2.2, survC M b.2.2.1 b.2.2.2)]

private theorem card_three_le {α : Type*} [DecidableEq α] {X Y Z S : Finset α} (hX : X ⊆ S) (hY : Y ⊆ S) (hZ : Z ⊆ S)
    (h1 : Disjoint X Y) (h2 : Disjoint X Z) (h3 : Disjoint Y Z) : X.card + Y.card + Z.card ≤ S.card := by
  have hd : Disjoint (X ∪ Y) Z := disjoint_union_left.2 ⟨h2, h3⟩
  have hc := card_le_card (union_subset (union_subset hX hY) hZ)
  rw [card_union_of_disjoint hd, card_union_of_disjoint h1] at hc
  exact hc

/-- **The blocks of a node are disjoint in rows and columns**, so together they hold at most `m` rows and columns. -/
theorem children_size_le {M : R → C → Bool} {A : Finset R} {B : Finset C} {p : R → ℤ} {q : C → ℤ} {x : R} {w : C}
    (h : PositionsOn M A B p q) (hx : x ∈ A) (hw : w ∈ B) :
    survSize M (splitBlocks M A B x w).1 + survSize M (splitBlocks M A B x w).2.1 +
      survSize M (splitBlocks M A B x w).2.2 ≤ A.card + B.card := by
  obtain ⟨d1, d2, d3, d4, d5, d6, _⟩ := split_disjoint h hx hw
  have hRA : ∀ v, rowsAt M A w v ⊆ A := rowsAt_subset M A w
  have hCB : ∀ v, colsAt M B x v ⊆ B := colsAt_subset M B x
  have hsub : (∀ b ∈ [(splitBlocks M A B x w).1, (splitBlocks M A B x w).2.1, (splitBlocks M A B x w).2.2],
      b.1 ⊆ A ∧ b.2 ⊆ B) := by
    intro b hb
    simp only [splitBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
    split_ifs at hb <;> rcases hb with rfl | rfl | rfl <;> exact ⟨hRA _, hCB _⟩
  have s1 := hsub _ (by simp : (splitBlocks M A B x w).1 ∈ _)
  have s2 := hsub (splitBlocks M A B x w).2.1 (by simp)
  have s3 := hsub (splitBlocks M A B x w).2.2 (by simp)
  have e1 := card_three_le ((survR_subset _ _ _).trans s1.1) ((survR_subset _ _ _).trans s2.1)
    ((survR_subset _ _ _).trans s3.1) d1 d2 d3
  have e2 := card_three_le ((survC_subset _ _ _).trans s1.2) ((survC_subset _ _ _).trans s2.2)
    ((survC_subset _ _ _).trans s3.2) d4 d5 d6
  simp only [survSize]
  omega

/-- The total number of rows and columns at depth `d` below a block, for fixed pivots. -/
def levelSize (pick : Finset R → Finset C → Option (R × C)) (M : R → C → Bool) :
    ℕ → Finset R → Finset C → ℕ
  | 0, A, B => A.card + B.card
  | d + 1, A, B =>
    if IsBase A B then 0
    else
      match pick A B with
      | none => 0
      | some e => ((children M A B e.1 e.2).map fun b => levelSize pick M d b.1 b.2).sum

/-- **The level sum.** On a nested block, for any pivots, the blocks at any depth hold at most `m` rows and columns
in total. -/
theorem levelSize_le {pick : Finset R → Finset C → Option (R × C)} (hp : PickSpec pick) (M : R → C → Bool) :
    ∀ (d : ℕ) (A : Finset R) (B : Finset C), NestedOn M A B → levelSize pick M d A B ≤ A.card + B.card := by
  intro d
  induction d with
  | zero => intro A B _; exact le_rfl
  | succ d ih =>
    intro A B hN
    rw [levelSize]
    by_cases hb : IsBase A B
    · rw [if_pos hb]; omega
    rw [if_neg hb]
    obtain ⟨hA, hB⟩ := IsBase.nonempty_of_not hb
    obtain ⟨x, hx, w, hw, hpick⟩ := hp A B hA hB
    rw [hpick]
    obtain ⟨p, q, hpq⟩ := (nestedOn_iff_positions M A B).1 hN
    have hsize := children_size_le hpq hx hw
    have hRA : ∀ v, rowsAt M A w v ⊆ A := rowsAt_subset M A w
    have hCB : ∀ v, colsAt M B x v ⊆ B := colsAt_subset M B x
    have hsub : ∀ b ∈ [(splitBlocks M A B x w).1, (splitBlocks M A B x w).2.1, (splitBlocks M A B x w).2.2],
        b.1 ⊆ A ∧ b.2 ⊆ B := by
      intro b hb
      simp only [splitBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
      split_ifs at hb <;> rcases hb with rfl | rfl | rfl <;> exact ⟨hRA _, hCB _⟩
    have hrec : ∀ b ∈ [(splitBlocks M A B x w).1, (splitBlocks M A B x w).2.1, (splitBlocks M A B x w).2.2],
        levelSize pick M d (survR M b.1 b.2) (survC M b.1 b.2) ≤ survSize M b := fun b hb =>
      ih _ _ (hN.mono ((survR_subset _ _ _).trans (hsub b hb).1) ((survC_subset _ _ _).trans (hsub b hb).2))
    have h1 := hrec (splitBlocks M A B x w).1 (by simp)
    have h2 := hrec (splitBlocks M A B x w).2.1 (by simp)
    have h3 := hrec (splitBlocks M A B x w).2.2 (by simp)
    simp only [children, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

/-- **The level sum, charged.** A cost `c` per row or column at each of `D` levels totals at most `c D m`. -/
theorem level_total_le {pick : Finset R → Finset C → Option (R × C)} (hp : PickSpec pick) {M : R → C → Bool}
    {A : Finset R} {B : Finset C} (hN : NestedOn M A B) {c : ℝ} (hc : 0 ≤ c) (D : ℕ) :
    ∑ d ∈ range D, c * (levelSize pick M d A B : ℝ) ≤ c * D * ((A.card : ℝ) + B.card) := by
  calc ∑ d ∈ range D, c * (levelSize pick M d A B : ℝ)
      ≤ ∑ _d ∈ range D, c * ((A.card : ℝ) + B.card) := by
        refine sum_le_sum fun d _ => mul_le_mul_of_nonneg_left ?_ hc
        exact_mod_cast levelSize_le hp M d A B hN
    _ = c * D * ((A.card : ℝ) + B.card) := by
        simp only [sum_const, card_range, nsmul_eq_mul]
        ring

/-! ## The expected cost with uniform pivots -/

/-- **The expected cost of Learn with uniform pivots**, charging each node `c · m`. The average over `A × B` is the
expectation over a uniform and independent pair of pivots. The trimmed blocks depend on the pivots only, not on the
outcomes of the searches, so this recursion is the whole of the randomness in the shape of the tree. -/
noncomputable def expCost (c : ℝ) (M : R → C → Bool) : ℕ → Finset R → Finset C → ℝ
  | 0, _, _ => 0
  | n + 1, A, B =>
    if IsBase A B then c * ((A.card : ℝ) + B.card)
    else c * ((A.card : ℝ) + B.card) +
      (∑ e ∈ A ×ˢ B, ((children M A B e.1 e.2).map fun b => expCost c M n b.1 b.2).sum) /
        ((A.card : ℝ) * B.card)

/-- The potential: `1 + 4 log_{4/3} m`, so that a good pivot pair saves `4`. -/
noncomputable def depthG (m : ℝ) : ℝ := 1 + 4 * Real.logb (4 / 3) m

private theorem one_lt_b : (1 : ℝ) < 4 / 3 := by norm_num

theorem depthG_one_le {m : ℝ} (hm : 1 ≤ m) : 1 ≤ depthG m := by
  have := Real.logb_nonneg one_lt_b hm
  simp only [depthG]
  linarith

theorem depthG_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) : depthG s ≤ depthG t := by
  have := Real.logb_le_logb_of_le one_lt_b hs hst
  simp only [depthG]
  linarith

theorem depthG_step {m : ℝ} (hm : 0 < m) : depthG (3 / 4 * m) = depthG m - 4 := by
  simp only [depthG]
  have e : 3 / 4 * m = m / (4 / 3) := by ring
  rw [e, Real.logb_div hm.ne' (by norm_num), Real.logb_self_eq_one one_lt_b]
  ring

/-- A child block against a size bound `t ≥ 1`. -/
private theorem potential_le {c s t : ℝ} (hc : 0 ≤ c) (hs : 0 ≤ s) (hst : s ≤ t) :
    c * s * depthG s ≤ c * s * depthG t := by
  rcases hs.eq_or_lt with h | h
  · simp [← h]
  · exact mul_le_mul_of_nonneg_left (depthG_mono h hst) (mul_nonneg hc hs)

/-- The potential bound of a list of three children, given a common size bound. -/
private theorem sum_three_le {c t m s1 s2 s3 : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ depthG t) (h1 : 0 ≤ s1) (h2 : 0 ≤ s2)
    (h3 : 0 ≤ s3) (h1t : s1 ≤ t) (h2t : s2 ≤ t) (h3t : s3 ≤ t) (hsum : s1 + s2 + s3 ≤ m) :
    c * s1 * depthG s1 + c * s2 * depthG s2 + c * s3 * depthG s3 ≤ c * m * depthG t := by
  have e1 := potential_le hc h1 h1t
  have e2 := potential_le hc h2 h2t
  have e3 := potential_le hc h3 h3t
  have e4 : c * (s1 + s2 + s3) * depthG t ≤ c * m * depthG t :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hc) ht
  nlinarith

/-- **The expected cost.** On a nested block, with uniform pivots and a charge `c · m` per node, the expected total is
at most `c m (1 + 4 log_{4/3} m)`, at any fuel. This replaces the argument that a row or column lies in expected
`O(log m)` levels: it is the same recurrence, summed over the block by a potential. -/
theorem expCost_le {c : ℝ} (hc : 0 ≤ c) (M : R → C → Bool) :
    ∀ (n : ℕ) (A : Finset R) (B : Finset C), NestedOn M A B →
      expCost c M n A B ≤ c * ((A.card : ℝ) + B.card) * depthG ((A.card : ℝ) + B.card) := by
  -- the bound is nonnegative and at least `c m`
  have hbase : ∀ m : ℕ, c * (m : ℝ) ≤ c * (m : ℝ) * depthG (m : ℝ) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have := depthG_one_le h1
      have h2 : 0 ≤ c * (m : ℝ) := by positivity
      nlinarith
  intro n
  induction n with
  | zero =>
    intro A B _
    simp only [expCost]
    have := hbase (A.card + B.card)
    push_cast at this
    have h2 : 0 ≤ c * ((A.card : ℝ) + B.card) := by positivity
    linarith
  | succ n ih =>
    intro A B hN
    rw [expCost]
    have hb0 := hbase (A.card + B.card)
    push_cast at hb0
    by_cases hb : IsBase A B
    · rw [if_pos hb]; exact hb0
    rw [if_neg hb]
    obtain ⟨hA, hB⟩ := IsBase.nonempty_of_not hb
    obtain ⟨p, q, hpq⟩ := (nestedOn_iff_positions M A B).1 hN
    set m : ℝ := (A.card : ℝ) + B.card with hm
    have hApos : (0 : ℝ) < A.card := by exact_mod_cast card_pos.2 hA
    have hBpos : (0 : ℝ) < B.card := by exact_mod_cast card_pos.2 hB
    have hmpos : 0 < m := by positivity
    have hA1 : (1 : ℝ) ≤ A.card := by exact_mod_cast card_pos.2 hA
    have hB1 : (1 : ℝ) ≤ B.card := by exact_mod_cast card_pos.2 hB
    -- non-base blocks are large, so `3m/4 ≥ 1`
    have hbig : 4 ≤ A.card + B.card := by
      by_contra hlt
      apply hb
      have h1 : A.card ≤ 3 := by have := card_pos.2 hB; omega
      have h2 : B.card ≤ 3 := by have := card_pos.2 hA; omega
      simp only [IsBase]
      nlinarith
    have hm4 : (4 : ℝ) ≤ m := by
      rw [hm]
      exact_mod_cast hbig
    have hG1 : 1 ≤ depthG m := depthG_one_le (by linarith)
    have hG1' : 1 ≤ depthG (3 / 4 * m) := depthG_one_le (by linarith)
    set Y := c * m * depthG m with hY
    set X := c * m * depthG (3 / 4 * m) with hX
    have hXY : X = Y - 4 * (c * m) := by
      rw [hX, hY, depthG_step hmpos]
      ring
    let P : R × C → Prop := fun e => Good p A e.1 ∧ Good q B e.2
    -- the bound for one pivot pair
    have hpair : ∀ e ∈ A ×ˢ B, ((children M A B e.1 e.2).map fun b => expCost c M n b.1 b.2).sum ≤
        if P e then X else Y := by
      rintro ⟨x, w⟩ he
      have hx : x ∈ A := (mem_product.1 he).1
      have hw : w ∈ B := (mem_product.1 he).2
      have hsize := children_size_le hpq hx hw
      have hRA : ∀ v, rowsAt M A w v ⊆ A := rowsAt_subset M A w
      have hCB : ∀ v, colsAt M B x v ⊆ B := colsAt_subset M B x
      have hsub : ∀ b ∈ [(splitBlocks M A B x w).1, (splitBlocks M A B x w).2.1, (splitBlocks M A B x w).2.2],
          b.1 ⊆ A ∧ b.2 ⊆ B := by
        intro b hb
        simp only [splitBlocks, List.mem_cons, List.not_mem_nil, or_false] at hb
        split_ifs at hb <;> rcases hb with rfl | rfl | rfl <;> exact ⟨hRA _, hCB _⟩
      have hrec : ∀ b ∈ [(splitBlocks M A B x w).1, (splitBlocks M A B x w).2.1, (splitBlocks M A B x w).2.2],
          expCost c M n (survR M b.1 b.2) (survC M b.1 b.2) ≤
            c * (survSize M b : ℝ) * depthG (survSize M b : ℝ) := by
        intro b hb
        have := ih (survR M b.1 b.2) (survC M b.1 b.2)
          (hN.mono ((survR_subset _ _ _).trans (hsub b hb).1) ((survC_subset _ _ _).trans (hsub b hb).2))
        simpa [survSize] using this
      have h1 := hrec (splitBlocks M A B x w).1 (by simp)
      have h2 := hrec (splitBlocks M A B x w).2.1 (by simp)
      have h3 := hrec (splitBlocks M A B x w).2.2 (by simp)
      simp only [children, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      set s1 := survSize M (splitBlocks M A B x w).1
      set s2 := survSize M (splitBlocks M A B x w).2.1
      set s3 := survSize M (splitBlocks M A B x w).2.2
      have hs : (s1 : ℝ) + s2 + s3 ≤ m := by
        rw [hm]
        exact_mod_cast hsize
      have hs1 : (0 : ℝ) ≤ s1 := by positivity
      have hs2 : (0 : ℝ) ≤ s2 := by positivity
      have hs3 : (0 : ℝ) ≤ s3 := by positivity
      by_cases hP : P (x, w)
      · rw [if_pos hP]
        obtain ⟨g1, g2, g3⟩ := lemma4_good hpq hx hw hP.1 hP.2
        have cast : ∀ s : ℕ, 4 * s ≤ 3 * (A.card + B.card) → (s : ℝ) ≤ 3 / 4 * m := by
          intro s hs'
          have : (4 : ℝ) * s ≤ 3 * ((A.card : ℝ) + B.card) := by exact_mod_cast hs'
          rw [hm]
          linarith
        have := sum_three_le hc (by linarith) hs1 hs2 hs3 (cast _ g1) (cast _ g2) (cast _ g3) hs
        simp only [add_assoc] at this ⊢
        linarith
      · rw [if_neg hP]
        have hle : ∀ s t u : ℝ, 0 ≤ t → 0 ≤ u → s + t + u ≤ m → s ≤ m := fun s t u h1 h2 h3 => by linarith
        have := sum_three_le hc (t := m) (by linarith) hs1 hs2 hs3 (by linarith) (by linarith) (by linarith) hs
        simp only [add_assoc] at this ⊢
        linarith
    -- sum over the pivot pairs
    classical
    have hsum := sum_le_sum hpair
    set N : ℝ := (A.card : ℝ) * B.card with hNdef
    have hNpos : 0 < N := by positivity
    let g := ((A ×ˢ B).filter P).card
    have hgood : (A.card * B.card : ℕ) ≤ 4 * g := by
      have := good_pairs_card p q A B
      convert this using 3
    have hgood' : N ≤ 4 * (g : ℝ) := by
      rw [hNdef]
      exact_mod_cast hgood
    have hite : (∑ e ∈ A ×ˢ B, if P e then X else Y) = (g : ℝ) * X + (N - g) * Y := by
      rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
      have e2 := card_filter_add_card_filter_not (s := A ×ˢ B) P
      have e3 : (((A ×ˢ B).filter fun e => ¬ P e).card : ℝ) = N - g := by
        have e4 : (((A ×ˢ B).filter P).card : ℝ) + ((A ×ˢ B).filter fun e => ¬ P e).card = (A ×ˢ B).card := by
          exact_mod_cast e2
        rw [card_product] at e4
        push_cast at e4
        rw [hNdef]
        simp only [g]
        linarith
      rw [e3]
    rw [hite] at hsum
    have hcm : 0 ≤ c * m := by positivity
    have hfinal : (g : ℝ) * X + (N - g) * Y ≤ N * (Y - c * m) := by
      rw [hXY]
      nlinarith
    have hdiv : (∑ e ∈ A ×ˢ B, ((children M A B e.1 e.2).map fun b => expCost c M n b.1 b.2).sum) / N ≤
        Y - c * m := by
      rw [div_le_iff₀ hNpos]
      linarith
    linarith

/-! ## From the cost of quantum search to the charge per node -/

/-- The charge per row or column of a node: two reads, and twelve Holding calls of expected rounds at most
`roundsBound m₀`, each round a search of cost `cs (m/2) lam` and a read of `m`. -/
noncomputable def nodeCoeff (cs lam : ℝ) (m₀ : ℕ) : ℝ := 2 + 12 * roundsBound m₀ * (cs * lam / 2 + 1)

theorem roundsBound_nonneg (u : ℕ) : 0 ≤ roundsBound u := by
  unfold roundsBound
  split_ifs
  · norm_num
  · positivity

theorem one_le_roundsBound (u : ℕ) : 1 ≤ roundsBound u := by
  unfold roundsBound
  split_ifs
  · exact le_rfl
  · have : (0 : ℝ) ≤ (Nat.log 2 u : ℝ) := by positivity
    linarith

/-- A base case reads at most `4` per row or column, which the charge covers. -/
theorem base_cost_le {cs lam : ℝ} (hcs : 0 ≤ cs) (hlam : 0 ≤ lam) {A : Finset R} {B : Finset C} (hb : IsBase A B)
    (m₀ : ℕ) : ((A.card * B.card : ℕ) : ℝ) ≤ nodeCoeff cs lam m₀ * ((A.card : ℝ) + B.card) := by
  have h1 : ((A.card * B.card : ℕ) : ℝ) ≤ 4 * ((A.card : ℝ) + B.card) := by
    have : A.card * B.card ≤ 4 * (A.card + B.card) := hb
    exact_mod_cast this
  have h2 : (4 : ℝ) ≤ nodeCoeff cs lam m₀ := by
    simp only [nodeCoeff]
    have hr := one_le_roundsBound m₀
    have ht : (0 : ℝ) ≤ cs * lam / 2 := by positivity
    nlinarith
  have h3 : (0 : ℝ) ≤ (A.card : ℝ) + B.card := by positivity
  nlinarith

/-- A node with `a` rows and `b` columns, inside a block with `m₀` rows and columns: reading a row and a column, and
twelve Holding calls with `ρ ≤ roundsBound m₀` expected rounds of a quantum search and a read, cost at most
`nodeCoeff · (a + b)`. A child block and the candidates of a search are no larger than the node, so this is an upper
bound for each of the twelve calls. -/
theorem node_cost_le {cs lam : ℝ} (hcs : 0 ≤ cs) (hlam : 0 ≤ lam) {a b m₀ : ℕ} {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ roundsBound m₀) :
    2 * ((a : ℝ) + b) + 12 * ρ * (cs * Real.sqrt ((a : ℝ) * b) * lam + ((a : ℝ) + b)) ≤
      nodeCoeff cs lam m₀ * ((a : ℝ) + b) := by
  have hab : (0 : ℝ) ≤ (a : ℝ) + b := by positivity
  have h1 : cs * Real.sqrt ((a : ℝ) * b) * lam ≤ cs * (((a : ℝ) + b) / 2) * lam :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sqrt_mul_le_half a b) hcs) hlam
  have h2 : cs * Real.sqrt ((a : ℝ) * b) * lam + ((a : ℝ) + b) ≤ (cs * lam / 2 + 1) * ((a : ℝ) + b) := by
    nlinarith
  have h3 : (0 : ℝ) ≤ cs * lam / 2 + 1 := by positivity
  have h4 : 12 * ρ * (cs * Real.sqrt ((a : ℝ) * b) * lam + ((a : ℝ) + b)) ≤
      12 * ρ * ((cs * lam / 2 + 1) * ((a : ℝ) + b)) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have h5 : 12 * ρ * ((cs * lam / 2 + 1) * ((a : ℝ) + b)) ≤
      12 * roundsBound m₀ * ((cs * lam / 2 + 1) * ((a : ℝ) + b)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ (by norm_num)) (by positivity)
  have e : nodeCoeff cs lam m₀ * ((a : ℝ) + b) =
      2 * ((a : ℝ) + b) + 12 * roundsBound m₀ * ((cs * lam / 2 + 1) * ((a : ℝ) + b)) := by
    simp only [nodeCoeff]
    ring
  rw [e]
  linarith

/-- `log₂ m ≥ 1` from `m ≥ 2`. -/
private theorem logb_two_ge_one {m : ℕ} (hm : 2 ≤ m) : 1 ≤ Real.logb 2 m := by
  have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (x := 2) (y := m) (by norm_num) (by exact_mod_cast hm)
  rwa [Real.logb_self_eq_one (by norm_num)] at h

/-- The rounds bound against `log₂`. -/
private theorem roundsBound_le_log {m : ℕ} (hm : 2 ≤ m) : roundsBound m ≤ 5 * Real.logb 2 m := by
  have h1 := logb_two_ge_one hm
  have h2 : (Nat.log 2 m : ℝ) ≤ Real.logb 2 m := Real.natLog_le_logb m 2
  unfold roundsBound
  rw [if_neg (by omega)]
  linarith

/-- The arithmetic of Theorem 1: `c m (1 + 4 log_{4/3} m)` with `c = nodeCoeff` and `lam ≤ log₂ m` is `O(m log³ m)`, with
an explicit constant. -/
theorem theorem1_arith {cs lam : ℝ} (hcs : 0 ≤ cs) (hlam : 0 ≤ lam) {m : ℕ} (hm : 2 ≤ m)
    (hlamL : lam ≤ Real.logb 2 m) :
    nodeCoeff cs lam m * (m : ℝ) * depthG (m : ℝ) ≤
      ((62 + 30 * cs) * (1 + 4 * Real.logb (4 / 3) 2)) * (m : ℝ) * Real.logb 2 m ^ 3 := by
  set L := Real.logb 2 m with hL
  have hL1 : 1 ≤ L := logb_two_ge_one hm
  have hm0 : (0 : ℝ) < m := by positivity
  have hκ : 0 ≤ Real.logb (4 / 3) 2 := Real.logb_nonneg one_lt_b (by norm_num)
  -- the coefficient
  have hr := roundsBound_le_log hm
  have hr0 := roundsBound_nonneg m
  have hco : nodeCoeff cs lam m ≤ (62 + 30 * cs) * L ^ 2 := by
    have h1 : cs * lam / 2 + 1 ≤ cs * L / 2 + 1 := by nlinarith
    have h2 : (0 : ℝ) ≤ cs * lam / 2 + 1 := by positivity
    have h3 : roundsBound m * (cs * lam / 2 + 1) ≤ (5 * L) * (cs * L / 2 + 1) :=
      mul_le_mul hr h1 h2 (by linarith)
    simp only [nodeCoeff]
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    have hcsL : 0 ≤ cs * L ^ 2 := by positivity
    nlinarith
  have hco0 : 0 ≤ nodeCoeff cs lam m := by
    simp only [nodeCoeff]
    have := roundsBound_nonneg m
    positivity
  -- the potential
  have hdep : depthG (m : ℝ) ≤ (1 + 4 * Real.logb (4 / 3) 2) * L := by
    have e : Real.logb (4 / 3) (m : ℝ) = L * Real.logb (4 / 3) 2 := by
      simp only [hL, Real.logb]
      have h2 : Real.log 2 ≠ 0 := by positivity
      field_simp
    simp only [depthG, e]
    nlinarith
  have hdep0 : 0 ≤ depthG (m : ℝ) := by
    have := depthG_one_le (m := (m : ℝ)) (by exact_mod_cast (by omega : 1 ≤ m))
    linarith
  calc nodeCoeff cs lam m * (m : ℝ) * depthG (m : ℝ)
      = (nodeCoeff cs lam m * depthG (m : ℝ)) * m := by ring
    _ ≤ ((62 + 30 * cs) * L ^ 2 * ((1 + 4 * Real.logb (4 / 3) 2) * L)) * m := by
        apply mul_le_mul_of_nonneg_right _ hm0.le
        exact mul_le_mul hco hdep hdep0 (by positivity)
    _ = _ := by ring

/-- `log m ≤ log₂ m`, since `log 2 ≤ 1`. -/
private theorem log_le_logb_two (m : ℕ) : Real.log (m : ℝ) ≤ Real.logb 2 (m : ℝ) := by
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
  simp only [Real.logb]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  rw [le_div_iff₀ hl2]
  nlinarith

/-- The constant of Theorem 1, given the constant of quantum search `cs`. -/
noncomputable def theorem1Const (cs : ℝ) : ℝ := (62 + 30 * cs) * (1 + 4 * Real.logb (4 / 3) 2)

/-- The expected charge of Learn on a nested block, with `λ = log m`, for an explicit constant. -/
theorem expected_cost_explicit {cs : ℝ} (hcs : 0 ≤ cs) (M : R → C → Bool) (A : Finset R) (B : Finset C) (n : ℕ)
    (hN : NestedOn M A B) (hm : 2 ≤ A.card + B.card) :
    expCost (nodeCoeff cs (Real.log ((A.card + B.card : ℕ) : ℝ)) (A.card + B.card)) M n A B ≤
      theorem1Const cs * ((A.card + B.card : ℕ) : ℝ) * Real.logb 2 ((A.card + B.card : ℕ) : ℝ) ^ 3 := by
  set m := A.card + B.card with hmdef
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
  have hco0 : 0 ≤ nodeCoeff cs (Real.log (m : ℝ)) m := by
    simp only [nodeCoeff]
    have := roundsBound_nonneg m
    positivity
  have h1 := expCost_le hco0 M n A B hN
  have h2 := theorem1_arith hcs hlogm hm (log_le_logb_two m)
  have e : (A.card : ℝ) + B.card = (m : ℝ) := by
    rw [hmdef]
    push_cast
    rfl
  rw [e] at h1
  exact h1.trans h2

theorem theorem1Const_pos {cs : ℝ} (hcs : 0 < cs) : 0 < theorem1Const cs := by
  have hκ : 0 ≤ Real.logb (4 / 3) 2 := Real.logb_nonneg one_lt_b (by norm_num)
  simp only [theorem1Const]
  positivity

/-- **Theorem 1, the expected-cost arithmetic, from quantum search.** Take its constant `cs`, and `δ = 1/m`, so `λ = log m`.
This gives the search with cost `cs √N log m` that the node charge assumes. There is a constant `K` such that on every
nested block with `m ≥ 2` rows and columns the expected total charge of Learn with uniform pivots is at most
`K m log₂³ m`. The node charge covers those searches and Holding's expected
rounds; see `node_cost_le`, `base_cost_le` and `expRounds_le_rows`. The union bound over the searches and the truncation
are not formalized. -/
theorem theorem1_expected_cost (hB : BBHTSearch) :
    ∃ cs K : ℝ, 0 < cs ∧ 0 < K ∧
      (∀ (N m : ℕ), 1 ≤ N → 2 ≤ m →
        ∃ (T : ℕ) (S : Type) (_ : Fintype S) (_ : DecidableEq S) (A : QAlg (Fin N) T S (Option (Fin N))),
          (T : ℝ) ≤ cs * Real.sqrt N * Real.log m ∧
          ∀ x : Fin N → Bool,
            (∀ i, x i = false → A.prob x (some i) = 0) ∧
            ((∀ i, x i = false) → A.prob x none = 1) ∧
            ((∃ i, x i = true) → A.prob x none ≤ 1 / m) ∧
            (∀ i j, x i = true → x j = true → A.prob x (some i) = A.prob x (some j))) ∧
      ∀ {R : Type u} {C : Type v} [DecidableEq R] [DecidableEq C] (M : R → C → Bool) (A : Finset R) (B : Finset C)
        (n : ℕ), NestedOn M A B → 2 ≤ A.card + B.card →
        expCost (nodeCoeff cs (Real.log ((A.card + B.card : ℕ) : ℝ)) (A.card + B.card)) M n A B ≤
          K * ((A.card + B.card : ℕ) : ℝ) * Real.logb 2 ((A.card + B.card : ℕ) : ℝ) ^ 3 := by
  obtain ⟨cs, hcs, hsearch⟩ := hB
  refine ⟨cs, theorem1Const cs, hcs, theorem1Const_pos hcs, ?_,
    fun M A B n hN hm => expected_cost_explicit hcs.le M A B n hN hm⟩
  intro N m hN hm
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hδ : (1 : ℝ) / m ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hmR
  obtain ⟨T, S, i1, i2, A, hT, hA⟩ := hsearch N (1 / m) hN (by positivity) hδ
  refine ⟨T, S, i1, i2, A, ?_, hA⟩
  simpa using hT

/-! ## The recurrence of Theorem 3 -/

section Recurrence

/-- `⌈log₂⌉` halves. -/
private theorem clog_half {n : ℕ} (hn : 2 ≤ n) : Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := by
  have := Nat.clog_of_two_le (b := 2) (by norm_num) hn
  simpa using this

private theorem step_arith (k : ℝ) (hk : 0 ≤ k) : k ^ 4 + (k + 1) ^ 3 ≤ (k + 1) ^ 4 := by
  nlinarith [pow_nonneg hk 2, pow_nonneg hk 3]

/-- **The recurrence.** `L(n) ≤ L(⌊n/2⌋) + L(⌈n/2⌉) + c n ℓ(n)³` with `L(0), L(1) ≤ 0` and `ℓ = ⌈log₂⌉` gives
`L(n) ≤ c n ℓ(n)⁴`. -/
theorem recurrence_le {c : ℝ} (hc : 0 ≤ c) {L : ℕ → ℝ} (h0 : L 0 ≤ 0) (h1 : L 1 ≤ 0)
    (hL : ∀ n, 2 ≤ n → L n ≤ L (n / 2) + L ((n + 1) / 2) + c * n * (Nat.clog 2 n : ℝ) ^ 3) :
    ∀ n, L n ≤ c * n * (Nat.clog 2 n : ℝ) ^ 4 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hpos : 0 ≤ c * n * (Nat.clog 2 n : ℝ) ^ 4 := by positivity
      interval_cases n
      · linarith
      · linarith
    · have e := clog_half hn
      set k := Nat.clog 2 ((n + 1) / 2) with hk
      have h2 := ih (n / 2) (by omega)
      have h3 := ih ((n + 1) / 2) (by omega)
      have hlog : (Nat.clog 2 (n / 2) : ℝ) ≤ k := by
        exact_mod_cast Nat.clog_mono_right 2 (by omega)
      have hkn : (0 : ℝ) ≤ k := by positivity
      have hn1 : ((n / 2 : ℕ) : ℝ) + ((n + 1) / 2 : ℕ) = n := by
        exact_mod_cast (by omega : n / 2 + (n + 1) / 2 = n)
      have h4 : c * ((n / 2 : ℕ) : ℝ) * (Nat.clog 2 (n / 2) : ℝ) ^ 4 ≤ c * ((n / 2 : ℕ) : ℝ) * (k : ℝ) ^ 4 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_left₀ (by positivity) hlog 4
      have hn0 : (0 : ℝ) ≤ c * n := by positivity
      have h5 := mul_le_mul_of_nonneg_left (step_arith k hkn) hn0
      have h6 := hL n hn
      rw [e] at h6 ⊢
      push_cast at h6 ⊢
      rw [← hn1] at h5 h6 ⊢
      have hfin : c * (((n / 2 : ℕ) : ℝ) + ((n + 1) / 2 : ℕ)) * (k : ℝ) ^ 4 =
          c * ((n / 2 : ℕ) : ℝ) * (k : ℝ) ^ 4 + c * (((n + 1) / 2 : ℕ) : ℝ) * (k : ℝ) ^ 4 := by ring
      nlinarith

/-- The recurrence with the actual logarithm: for `n ≥ 2`, `L(n) ≤ 16 c n log₂⁴ n`. -/
theorem recurrence_le_log {c : ℝ} (hc : 0 ≤ c) {L : ℕ → ℝ} (h0 : L 0 ≤ 0) (h1 : L 1 ≤ 0)
    (hL : ∀ n, 2 ≤ n → L n ≤ L (n / 2) + L ((n + 1) / 2) + c * n * (Nat.clog 2 n : ℝ) ^ 3) {n : ℕ}
    (hn : 2 ≤ n) : L n ≤ 16 * c * n * Real.logb 2 n ^ 4 := by
  refine (recurrence_le hc h0 h1 hL n).trans ?_
  have hL1 := logb_two_ge_one hn
  have hclog : (Nat.clog 2 n : ℝ) ≤ 2 * Real.logb 2 n := by
    have hcl : 1 ≤ Nat.clog 2 n := Nat.clog_pos (by norm_num) hn
    have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := n) (by omega)
    have hlt' : ((2 : ℝ) ^ (Nat.clog 2 n).pred) ≤ (n : ℝ) := by exact_mod_cast hlt.le
    have hle := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hlt'
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hle
    have hp : ((Nat.clog 2 n).pred : ℝ) + 1 = Nat.clog 2 n := by
      have : (Nat.clog 2 n).pred + 1 = Nat.clog 2 n := Nat.succ_pred_eq_of_pos hcl
      exact_mod_cast this
    linarith
  have hp : (Nat.clog 2 n : ℝ) ^ 4 ≤ (2 * Real.logb 2 n) ^ 4 := pow_le_pow_left₀ (by positivity) hclog 4
  have hn0 : (0 : ℝ) ≤ c * n := by positivity
  calc c * n * (Nat.clog 2 n : ℝ) ^ 4 ≤ c * n * (2 * Real.logb 2 n) ^ 4 := mul_le_mul_of_nonneg_left hp hn0
    _ = 16 * c * n * Real.logb 2 n ^ 4 := by ring

variable {V : Type*} [DecidableEq V] {split : Finset V → Finset V × Finset V}

/-- **The recurrence on the actual split.** If each cross block `A × B` of the recursion costs at most `c m ℓ(m)³`
with `m = |A| + |B|`, then all blocks of the recursive split of `S` cost at most `c |S| ℓ(|S|)⁴` in total. -/
theorem blocks_cost_le (hsp : SplitSpec split) {c : ℝ} (hc : 0 ≤ c) (f : Finset V × Finset V → ℝ) :
    ∀ (n : ℕ) (S : Finset V),
      (∀ b ∈ blocks split n S,
        f b ≤ c * ((b.1.card + b.2.card : ℕ) : ℝ) * (Nat.clog 2 (b.1.card + b.2.card) : ℝ) ^ 3) →
      ((blocks split n S).map f).sum ≤ c * (S.card : ℝ) * (Nat.clog 2 S.card : ℝ) ^ 4 := by
  intro n
  induction n with
  | zero => intro S _; simp only [blocks, List.map_nil, List.sum_nil]; positivity
  | succ n ih =>
    intro S hf
    rw [blocks] at hf ⊢
    split_ifs at hf ⊢ with h1
    · simp only [List.map_nil, List.sum_nil]; positivity
    obtain ⟨hd, hun, _, _, hA, hB⟩ := hsp S (by omega)
    have hsum : (split S).1.card + (split S).2.card = S.card := by
      rw [← card_union_of_disjoint hd, hun]
    have e := clog_half (n := S.card) (by omega)
    set k := Nat.clog 2 ((S.card + 1) / 2) with hk
    have ha : (Nat.clog 2 (split S).1.card : ℝ) ≤ k := by
      exact_mod_cast Nat.clog_mono_right 2 (by omega)
    have hb : (Nat.clog 2 (split S).2.card : ℝ) ≤ k := by
      exact_mod_cast Nat.clog_mono_right 2 (by omega)
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hf' := hf (split S) (by simp)
    rw [hsum, e] at hf'
    have i1 := ih (split S).1 fun b hb => hf b (by simp [hb])
    have i2 := ih (split S).2 fun b hb => hf b (by simp [hb])
    simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append]
    have ha4 : c * ((split S).1.card : ℝ) * (Nat.clog 2 (split S).1.card : ℝ) ^ 4 ≤
        c * ((split S).1.card : ℝ) * (k : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ha 4) (by positivity)
    have hb4 : c * ((split S).2.card : ℝ) * (Nat.clog 2 (split S).2.card : ℝ) ^ 4 ≤
        c * ((split S).2.card : ℝ) * (k : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb 4) (by positivity)
    have hS : (S.card : ℝ) = ((split S).1.card : ℝ) + (split S).2.card := by
      rw [← hsum]
      push_cast
      rfl
    have h5 := mul_le_mul_of_nonneg_left (step_arith k hk0) (by positivity : (0 : ℝ) ≤ c * S.card)
    rw [e]
    push_cast at hf' ⊢
    have h6 : c * (S.card : ℝ) * (k : ℝ) ^ 4 = c * ((split S).1.card : ℝ) * (k : ℝ) ^ 4 +
        c * ((split S).2.card : ℝ) * (k : ℝ) ^ 4 := by
      rw [hS]
      ring
    nlinarith

/-- `log₂ m ≤ ⌈log₂ m⌉`. -/
private theorem logb_le_clog {m : ℕ} (hm : 1 ≤ m) : Real.logb 2 (m : ℝ) ≤ (Nat.clog 2 m : ℝ) := by
  have h : (m : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 m := by exact_mod_cast Nat.le_pow_clog (by norm_num) m
  have hle := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by exact_mod_cast hm) h
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hle

/-- **Theorem 3, the learning cost.** On a graph with no alternating 4-cycle, the expected charge of Learn with uniform
pivots, summed over all cross blocks of the recursive split, is at most `K n ⌈log₂ n⌉⁴`, with the constant of
Theorem 1. -/
theorem threshold_expected_cost {cs : ℝ} (hcs : 0 < cs) [Fintype V] (hsp : SplitSpec split) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : NoAlt G) (fuel : ℕ) :
    ((blocks split (Fintype.card V) univ).map fun b =>
        expCost (nodeCoeff cs (Real.log ((b.1.card + b.2.card : ℕ) : ℝ)) (b.1.card + b.2.card))
          (adjM G) fuel b.1 b.2).sum ≤
      theorem1Const cs * (Fintype.card V : ℝ) * (Nat.clog 2 (Fintype.card V) : ℝ) ^ 4 := by
  refine blocks_cost_le hsp (theorem1Const_pos hcs).le _ _ univ fun b hb => ?_
  have hm := blocks_two_le hsp _ _ b hb
  refine (expected_cost_explicit hcs.le (adjM G) b.1 b.2 fuel (blocks_nested hsp hG _ _ b hb) hm).trans ?_
  have hK : 0 ≤ theorem1Const cs * ((b.1.card + b.2.card : ℕ) : ℝ) :=
    mul_nonneg (theorem1Const_pos hcs).le (by positivity)
  refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ (logb_le_clog (by omega)) 3) hK
  exact (Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ b.1.card + b.2.card)))

end Recurrence

end GraphClasses
