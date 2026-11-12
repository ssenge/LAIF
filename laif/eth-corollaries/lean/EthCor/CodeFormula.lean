import EthCor.ConnIso

/-! # The distance of a quantum CSS code as a sized count

A CSS code on n qubits is given by two lists of checks H₁, H₂, each check a list of qubits. The
Z-type logical operators are the x ∈ ker H₁ outside the row space of H₂ (with H₁ = H_X, H₂ = H_Z;
swap them for the X-type ones), and the distance is the least weight of one. Over 𝔽₂ the row space
of H₂ is the orthogonal complement of ker H₂, so x is logical iff ⟨x, y⟩ = 1 for some y ∈ ker H₂
(`logical_iff`), and then for exactly half of ker H₂ (`half`). So

  2·#{(x, y) : |x| = s, x ∈ ker H₁, y ∈ ker H₂, ⟨x, y⟩ = 1} = |ker H₂| · #{logical x of weight s}.

The formula `cssF w n ψ e` has the bits of x and y, a chain c₀ = 0, c_{i+1} = c_i ⊕ x_i y_i with
c_n = e, and the complements of y and c. A check of weight L ≤ w is written as the 2^{L−1} clauses
that forbid its odd patterns, so the formula has 5n + 2 variables for every number of checks
(`cnt_cssF`). The pairs with ⟨x, y⟩ = 0 and |x| = 0 are ker H₂ itself, which gives |ker H₂| from a
second count (`numLog_eq`). -/

namespace EthCor.Code

open Groundwork Groundwork.Prog CountKSat GraphProblems Finset EthCor.Ham EthCor.HamS EthCor.HamI EthCor.Conn EthCor.ConnI Matrix

/-! ### Codes over 𝔽₂ -/

section Codes

variable {n : ℕ}

/-- A bit in 𝔽₂. -/
def toZ (b : Bool) : ZMod 2 := if b then 1 else 0

theorem toZ_inj {a b : Bool} : toZ a = toZ b ↔ a = b := by cases a <;> cases b <;> decide

theorem toZ_xor (a b : Bool) : toZ (xor a b) = toZ a + toZ b := by cases a <;> cases b <;> decide

theorem toZ_and (a b : Bool) : toZ (a && b) = toZ a * toZ b := by cases a <;> cases b <;> decide

/-- A Bool vector as a vector over 𝔽₂. -/
def vecB (x : Fin n → Bool) : Fin n → ZMod 2 := fun j => toZ (x j)

/-- The vector of a check over 𝔽₂. -/
def vecR (r : List (Fin n)) : Fin n → ZMod 2 := fun j => (r.count j : ZMod 2)

/-- x is in the kernel of the checks H. -/
def InKer (H : List (List (Fin n))) (x : Fin n → Bool) : Prop := ∀ r ∈ H, vecR r ⬝ᵥ vecB x = 0

/-- The row space of the checks H. -/
def rowSp (H : List (List (Fin n))) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  Submodule.span (ZMod 2) {v | ∃ r ∈ H, vecR r = v}

open Classical in
/-- The number of logical operators of weight s: x ∈ ker H₁, x ∉ rowspace H₂, |x| = s. -/
noncomputable def numLog (H₁ H₂ : List (List (Fin n))) (s : ℕ) : ℕ :=
  (univ.filter fun x : Fin n → Bool => (univ.filter fun j => x j = true).card = s ∧ InKer H₁ x ∧
    vecB x ∉ rowSp H₂).card

theorem vecR_dot (r : List (Fin n)) (y : Fin n → Bool) : vecR r ⬝ᵥ vecB y = ((r.map y).count true : ZMod 2) := by
  induction r with
  | nil => simp [vecR, dotProduct]
  | cons a r ih =>
    have e : vecR (a :: r) = Pi.single a 1 + vecR r := by
      funext j
      simp only [vecR, List.count_cons, Pi.add_apply, Pi.single_apply, beq_iff_eq]
      by_cases h : j = a <;> simp [h, Ne.symm, add_comm]
    rw [e, add_dotProduct, single_dotProduct, ih, List.map_cons, List.count_cons]
    simp only [vecB, toZ, beq_iff_eq, one_mul]
    cases y a <;> simp [add_comm]

theorem zmod2_eq : ∀ a : ZMod 2, (if a = 1 then (1 : ZMod 2) else 0) = a := by decide

theorem zmod2_ne : ∀ a : ZMod 2, a ≠ 0 ↔ a = 1 := by decide

/-- **Logical operators**: x ∉ rowspace H₂ iff ⟨x, y⟩ = 1 for some y ∈ ker H₂. -/
theorem logical_iff (H₂ : List (List (Fin n))) (x : Fin n → Bool) :
    vecB x ∉ rowSp H₂ ↔ ∃ y, InKer H₂ y ∧ vecB x ⬝ᵥ vecB y = 1 := by
  constructor
  · intro hx
    obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    obtain ⟨y, hy⟩ : ∃ y : Fin n → Bool, y = fun j => decide (f (Pi.single j 1) = 1) := ⟨_, rfl⟩
    have hv : vecB y = fun j => f (Pi.single j 1) := by
      funext j; rw [hy, vecB, toZ]; simpa using zmod2_eq (f (Pi.single j 1))
    have hfv : ∀ v, f v = v ⬝ᵥ vecB y := fun v => by
      rw [LinearMap.pi_apply_eq_sum_univ f v, hv, dotProduct]
      refine sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul]
      congr 2
      funext j
      simp [Pi.single_apply, eq_comm]
    refine ⟨y, fun r hr => ?_, ?_⟩
    · have h : f (vecR r) ∈ (rowSp H₂).map f := Submodule.mem_map_of_mem (Submodule.subset_span ⟨r, hr, rfl⟩)
      rw [hmap, Submodule.mem_bot, hfv] at h
      exact h
    · rw [← hfv]; exact (zmod2_ne _).1 hf
  · rintro ⟨y, hy, h1⟩ hx
    have key : ∀ v ∈ rowSp H₂, v ⬝ᵥ vecB y = 0 := fun v hv => by
      induction hv using Submodule.span_induction with
      | mem v hv => obtain ⟨r, hr, rfl⟩ := hv; exact hy r hr
      | zero => simp
      | add a b _ _ ha hb => rw [add_dotProduct, ha, hb, add_zero]
      | smul c a _ ha => rw [smul_dotProduct, ha, smul_zero]
    rw [key _ hx] at h1
    exact zero_ne_one h1

/-! ### Half of the kernel -/

/-- Pointwise xor. -/
def bxor (y z : Fin n → Bool) : Fin n → Bool := fun j => xor (y j) (z j)

theorem vecB_bxor (y z : Fin n → Bool) : vecB (bxor y z) = vecB y + vecB z := by
  funext j; exact toZ_xor (y j) (z j)

theorem inKer_bxor {H : List (List (Fin n))} {y z : Fin n → Bool} (hy : InKer H y) (hz : InKer H z) :
    InKer H (bxor y z) := fun r hr => by rw [vecB_bxor, dotProduct_add, hy r hr, hz r hr, add_zero]

open Classical in
/-- **Half of the kernel**: if ⟨x, y₀⟩ = 1 for some y₀ ∈ ker H, then ⟨x, y⟩ = 1 for exactly half
of ker H. -/
theorem half (H : List (List (Fin n))) (x : Fin n → Bool) :
    2 * (univ.filter fun y => InKer H y ∧ vecB x ⬝ᵥ vecB y = 1).card =
      if ∃ y, InKer H y ∧ vecB x ⬝ᵥ vecB y = 1 then (univ.filter fun y => InKer H y).card else 0 := by
  split_ifs with h
  · obtain ⟨y₀, hy₀, h1⟩ := h
    have hsplit := card_filter_add_card_filter_not (s := univ.filter fun y => InKer H y)
      (fun y => vecB x ⬝ᵥ vecB y = 1)
    rw [filter_filter, filter_filter] at hsplit
    have hbij : (univ.filter fun y => InKer H y ∧ ¬ vecB x ⬝ᵥ vecB y = 1).card =
        (univ.filter fun y => InKer H y ∧ vecB x ⬝ᵥ vecB y = 1).card := by
      refine card_nbij' (fun y => bxor y y₀) (fun y => bxor y y₀) ?_ ?_ ?_ ?_
      · intro y hy
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
        refine ⟨inKer_bxor hy.1 hy₀, ?_⟩
        rw [vecB_bxor, dotProduct_add, h1]
        have := hy.2; revert this; generalize vecB x ⬝ᵥ vecB y = a; revert a; decide
      · intro y hy
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
        refine ⟨inKer_bxor hy.1 hy₀, ?_⟩
        rw [vecB_bxor, dotProduct_add, h1, hy.2]; decide
      · intro y _; funext j; simp [bxor]
      · intro y _; funext j; simp [bxor]
    omega
  · simp only [not_exists, not_and] at h
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or, card_eq_zero, filter_eq_empty_iff, mem_univ,
      true_implies, not_and]
    exact h

end Codes

/-! ### The formula -/

/-- All Bool lists of length at most w. -/
def pats : ℕ → List (List Bool)
  | 0 => [[]]
  | w + 1 => [] :: (pats w).flatMap fun b => [false :: b, true :: b]

theorem mem_pats {w : ℕ} {b : List Bool} : b ∈ pats w ↔ b.length ≤ w := by
  induction w generalizing b with
  | zero => cases b <;> simp [pats]
  | succ w ih =>
    cases b with
    | nil => simp [pats]
    | cons c b => cases c <;> simp [pats, ih]

theorem length_dup (l : List (List Bool)) : (l.flatMap fun b => [false :: b, true :: b]).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]; omega

theorem length_pats (w : ℕ) : (pats w).length + 1 = 2 ^ (w + 1) := by
  induction w with
  | zero => rfl
  | succ w ih => rw [pats, List.length_cons, length_dup, pow_succ]; omega

/-- The variable of a literal of the code: x_j = j for (j, true), y_j = n + j for (j, false). -/
def pos (n : ℕ) (l : ℕ × Bool) : ℕ := cond l.2 l.1 (n + l.1)

/-- The clauses of a check C of weight at most w: one clause forbids each odd pattern of its bits. -/
def rowF (w n : ℕ) (C : List (ℕ × Bool)) : Fml :=
  ((pats w).filter fun b => decide (b.length = C.length) && decide (b.count true % 2 = 1)).map fun b =>
    (C.zip b).map fun q => (pos n q.1, !q.2)

def rowsF (w n : ℕ) (ψ : Fml) : Fml := ψ.flatMap (rowF w n)

/-- x_d = x_c ⊕ (x_a ∧ x_b). -/
def xorC (a b c d : ℕ) : Fml :=
  [false, true].flatMap fun α => [false, true].flatMap fun β => [false, true].map fun γ =>
    [(a, !α), (b, !β), (c, !γ), (d, xor γ (α && β))]

/-- The chain c₀ = 0, c_{i+1} = c_i ⊕ x_i y_i, c_n = e, with x_i = i, y_i = n + i, c_i = 2n + i. -/
def chainF (n : ℕ) (e : Bool) : Fml :=
  [[(n + n, false)]] ++ (List.range n).flatMap (fun i => xorC i (n + i) (n + n + i) (n + n + i + 1)) ++
    [[(n + n + n, e)]]

/-- **The formula** on 5n + 2 variables: the checks, the chain, and the complements of y and c. -/
def cssF (w n : ℕ) (ψ : Fml) (e : Bool) : Fml := rowsF w n ψ ++ chainF n e ++ compF n (n + (n + 1))

/-- The code as a CNF on n variables: the checks of H₁ as positive clauses, those of H₂ as negative
clauses. -/
def codeCNF {n : ℕ} (H₁ H₂ : List (List (Fin n))) : Sat3.CNF n :=
  H₁.map (·.map (·, true)) ++ H₂.map (·.map (·, false))

/-! ### What the formula says -/

theorem zip_map_self {α β : Type} (C : List α) (g : α → β) : C.zip (C.map g) = C.map fun c => (c, g c) := by
  induction C with
  | nil => rfl
  | cons c C ih => simp [ih]

theorem map_of_zip {α β : Type} (g : α → β) : ∀ (C : List α) (b : List β), b.length = C.length →
    (∀ q ∈ C.zip b, g q.1 = q.2) → C.map g = b
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl
  | c :: C, d :: b, hl, h => by
    simp only [List.zip_cons_cons, List.mem_cons, forall_eq_or_imp] at h
    rw [List.map_cons, h.1, map_of_zip g C b (by simpa using hl) h.2]

theorem sat_rowF (f : ℕ → Bool) {w n : ℕ} {C : List (ℕ × Bool)} (hC : C.length ≤ w) :
    (∀ D ∈ rowF w n C, ∃ l ∈ D, f l.1 = l.2) ↔ (C.map fun l => f (pos n l)).count true % 2 = 0 := by
  constructor
  · intro h
    by_contra hodd
    have hb : (C.map fun l => f (pos n l)) ∈ (pats w).filter fun b =>
        decide (b.length = C.length) && decide (b.count true % 2 = 1) := by
      simp only [List.mem_filter, mem_pats, List.length_map, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hC, trivial, by omega⟩
    obtain ⟨l, hl, hfl⟩ := h _ (List.mem_map_of_mem (f := fun b => (C.zip b).map fun q => (pos n q.1, !q.2)) hb)
    rw [zip_map_self, List.map_map, List.mem_map] at hl
    obtain ⟨c, _, rfl⟩ := hl
    simp at hfl
  · intro h D hD
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hD
    simp only [List.mem_filter, mem_pats, Bool.and_eq_true, decide_eq_true_eq] at hb
    by_contra hno
    have key : ∀ q ∈ C.zip b, f (pos n q.1) = q.2 := fun q hq => by
      by_contra hne
      refine hno ⟨(pos n q.1, !q.2), List.mem_map_of_mem hq, ?_⟩
      show f (pos n q.1) = !q.2
      revert hne
      cases f (pos n q.1) <;> cases q.2 <;> decide
    rw [map_of_zip (fun l => f (pos n l)) C b hb.2.1 key] at h
    omega

theorem sat_rowsF (f : ℕ → Bool) {w n : ℕ} {ψ : Fml} (hψ : ∀ C ∈ ψ, C.length ≤ w) :
    (∀ D ∈ rowsF w n ψ, ∃ l ∈ D, f l.1 = l.2) ↔ ∀ C ∈ ψ, (C.map fun l => f (pos n l)).count true % 2 = 0 := by
  simp only [rowsF, List.mem_flatMap]
  constructor
  · intro h C hC; exact (sat_rowF f (hψ C hC)).1 fun D hD => h D ⟨C, hC, hD⟩
  · rintro h D ⟨C, hC, hD⟩; exact (sat_rowF f (hψ C hC)).2 (h C hC) D hD

theorem sat_xorC (f : ℕ → Bool) (a b c d : ℕ) :
    (∀ D ∈ xorC a b c d, ∃ l ∈ D, f l.1 = l.2) ↔ f d = xor (f c) (f a && f b) := by
  simp only [xorC, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil,
    List.cons_append, List.nil_append, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
    and_true, sat4]
  generalize f a = p, f b = q, f c = r, f d = t
  cases p <;> cases q <;> cases r <;> cases t <;> decide

theorem sat_chainF (f : ℕ → Bool) (n : ℕ) (e : Bool) :
    (∀ D ∈ chainF n e, ∃ l ∈ D, f l.1 = l.2) ↔ f (n + n) = false ∧
      (∀ i < n, f (n + n + i + 1) = xor (f (n + n + i)) (f i && f (n + i))) ∧ f (n + n + n) = e := by
  rw [chainF, List.forall_mem_append, List.forall_mem_append, forall_flatMap_range]
  simp only [sat_xorC, List.mem_singleton, forall_eq, exists_eq_left, and_assoc]

/-! ### Variables and widths -/

theorem rowsF_vars {w n : ℕ} {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) :
    ∀ D ∈ rowsF w n ψ, D.length ≤ w ∧ ∀ l ∈ D, l.1 < n + n := by
  intro D hD
  obtain ⟨C, hC, hD⟩ := List.mem_flatMap.1 hD
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hD
  have hb' := mem_pats.1 (List.mem_filter.1 hb).1
  refine ⟨by simp only [List.length_map, List.length_zip]; omega, fun l hl => ?_⟩
  obtain ⟨⟨⟨j, β⟩, d⟩, hq, rfl⟩ := List.mem_map.1 hl
  have := hψ C hC _ (List.of_mem_zip hq).1
  cases β <;> simp only [pos, cond_true, cond_false] at this ⊢ <;> omega

theorem mem_xorC {a b c d : ℕ} {D : List (ℕ × Bool)} (hD : D ∈ xorC a b c d) :
    D.length ≤ 4 ∧ ∀ l ∈ D, l.1 = a ∨ l.1 = b ∨ l.1 = c ∨ l.1 = d := by
  rw [xorC, List.mem_flatMap] at hD
  obtain ⟨α, -, hD⟩ := hD
  rw [List.mem_flatMap] at hD
  obtain ⟨β, -, hD⟩ := hD
  rw [List.mem_map] at hD
  obtain ⟨γ, -, rfl⟩ := hD
  refine ⟨by simp, fun l hl => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> simp

theorem chainF_vars {n : ℕ} {e : Bool} : ∀ D ∈ chainF n e, D.length ≤ 4 ∧ ∀ l ∈ D, l.1 < n + n + (n + 1) := by
  intro D hD
  simp only [chainF, List.mem_append, List.mem_singleton, List.mem_flatMap, List.mem_range] at hD
  rcases hD with (rfl | ⟨i, hi, hD⟩) | rfl
  · refine ⟨by simp, fun l hl => ?_⟩
    rw [List.mem_singleton] at hl; subst hl; simp only; omega
  · obtain ⟨h1, h2⟩ := mem_xorC hD
    exact ⟨h1, fun l hl => by rcases h2 l hl with h | h | h | h <;> rw [h] <;> omega⟩
  · refine ⟨by simp, fun l hl => ?_⟩
    rw [List.mem_singleton] at hl; subst hl; simp only; omega

theorem shaped_cssF {w n : ℕ} {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (e : Bool) :
    Shaped (w + 4) (n + n + (n + 1) + (n + (n + 1))) (cssF w n ψ e) := by
  intro D hD
  simp only [cssF, List.mem_append] at hD
  rcases hD with (hD | hD) | hD
  · obtain ⟨h1, h2⟩ := rowsF_vars hψ D hD
    exact ⟨by omega, fun l hl => by have := h2 l hl; omega⟩
  · obtain ⟨h1, h2⟩ := chainF_vars D hD
    exact ⟨by omega, fun l hl => by have := h2 l hl; omega⟩
  · rw [compF] at hD
    obtain ⟨i, hi, hD⟩ := List.mem_flatMap.1 hD
    rw [List.mem_range] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl <;> refine ⟨by simp, fun l hl => ?_⟩ <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> rcases hl with rfl | rfl <;> simp <;> omega

theorem length_rowsF (w n : ℕ) (ψ : Fml) : (rowsF w n ψ).length ≤ ψ.length * 2 ^ (w + 1) := by
  rw [rowsF, List.length_flatMap]
  have h : ∀ C ∈ ψ, (rowF w n C).length ≤ 2 ^ (w + 1) := fun C _ => by
    rw [rowF, List.length_map]
    have := List.length_filter_le (fun b => decide (b.length = C.length) && decide (b.count true % 2 = 1)) (pats w)
    have := length_pats w
    omega
  have := List.sum_le_card_nsmul (ψ.map fun C => (rowF w n C).length) (2 ^ (w + 1)) (by
    intro y hy
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hy
    exact h C hC)
  simpa using this

theorem length_cssF (w n : ℕ) (ψ : Fml) (e : Bool) :
    (cssF w n ψ e).length ≤ ψ.length * 2 ^ (w + 1) + 12 * n + 4 := by
  have h1 := length_rowsF w n ψ
  have h2 : (chainF n e).length = 8 * n + 2 := by
    simp [chainF, xorC, List.length_flatMap]; ring
  have h3 : (compF n (n + (n + 1))).length = 2 * (n + (n + 1)) := by
    simp [compF, List.length_flatMap]; ring
  rw [cssF, List.length_append, List.length_append, h2, h3]
  omega

/-! ### The count -/

/-- The partial inner products: `ipB f n i` = ⊕_{j < i} f j ∧ f (n + j). -/
def ipB (f : ℕ → Bool) (n : ℕ) : ℕ → Bool
  | 0 => false
  | i + 1 => xor (ipB f n i) (f i && f (n + i))

theorem toZ_ipB (f : ℕ → Bool) (n i : ℕ) : toZ (ipB f n i) = ∑ j ∈ range i, toZ (f j) * toZ (f (n + j)) := by
  induction i with
  | zero => simp [ipB, toZ]
  | succ i ih => rw [ipB, toZ_xor, toZ_and, ih, sum_range_succ]

section Count

variable {n : ℕ}

theorem chain_iff (f : ℕ → Bool) (g : Fin (n + 1) → Bool) :
    (ext g 0 = false ∧ ∀ i < n, ext g (i + 1) = xor (ext g i) (f i && f (n + i))) ↔
      g = fun i => ipB f n i.val := by
  constructor
  · rintro ⟨h0, hs⟩
    have key : ∀ i ≤ n, ext g i = ipB f n i := by
      intro i hi
      induction i with
      | zero => exact h0
      | succ i ih => rw [hs i (by omega), ih (by omega), ipB]
    funext i
    rw [← ext_fin g i, key i (by omega)]
  · rintro rfl
    have e : ∀ i ≤ n, ext (fun i : Fin (n + 1) => ipB f n i.val) i = ipB f n i := fun i hi => by
      simp only [CountKSat.ext, dif_pos (show i < n + 1 by omega)]
    exact ⟨by rw [e 0 (by omega)]; rfl, fun i hi => by rw [e _ hi, e _ (by omega), ipB]⟩

theorem count_aux (y : Fin (n + n + (n + 1)) → Bool) :
    (univ.filter fun i => Fin.append y (fun i : Fin (n + (n + 1)) => !ext y (n + i.val)) i = true).card =
      (univ.filter fun j : Fin n => ext y j.val = true).card + (n + (n + 1)) := by
  obtain ⟨xz, c, rfl⟩ : ∃ (xz : Fin (n + n) → Bool) (c : Fin (n + 1) → Bool), y = Fin.append xz c :=
    ⟨_, _, (Fin.append_castAdd_natAdd (f := y)).symm⟩
  obtain ⟨x, z, rfl⟩ : ∃ (x z : Fin n → Bool), xz = Fin.append x z :=
    ⟨_, _, (Fin.append_castAdd_natAdd (f := xz)).symm⟩
  have hx : ∀ j : Fin n, ext (Fin.append (Fin.append x z) c) j.val = x j := fun j => by
    rw [ext_append_lt _ _ (by have := j.2; omega), ext_append_lt _ _ j.2, ext_fin]
  have haux : (fun i : Fin (n + (n + 1)) => !ext (Fin.append (Fin.append x z) c) (n + i.val)) =
      Fin.append (fun j => !z j) (fun j => !c j) := by
    funext i
    induction i using Fin.addCases with
    | left j =>
      rw [Fin.append_left, Fin.val_castAdd, ext_append_lt _ _ (by have := j.2; omega), ext_append_ge, ext_fin]
    | right j =>
      rw [Fin.append_right, Fin.val_natAdd, show n + (n + j.val) = n + n + j.val by omega, ext_append_ge, ext_fin]
  rw [haux, card_true_append, card_true_append, card_true_append, card_true_append]
  have e1 : (univ.filter fun j : Fin n => ext (Fin.append (Fin.append x z) c) j.val = true) =
      univ.filter fun j => x j = true := by
    ext j; simp [hx]
  rw [e1]
  have := card_true_not z
  have := card_true_not c
  omega

/-- Step A: the complements are determined. -/
theorem stepA (w : ℕ) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (s : ℕ) (e : Bool) :
    cntS (n + n + (n + 1) + (n + (n + 1))) (s + (n + (n + 1))) (cssF w n ψ e) =
      (univ.filter fun y : Fin (n + n + (n + 1)) → Bool =>
        (∀ D ∈ rowsF w n ψ ++ chainF n e, ∃ l ∈ D, ext y l.1 = l.2) ∧
        (univ.filter fun j : Fin n => ext y j.val = true).card = s).card := by
  unfold cntS
  refine card_append _ _ (fun y i => !ext y (n + i.val)) fun y g => ?_
  have hlt : ∀ a < n + n + (n + 1), ext (Fin.append y g) a = ext y a := fun a ha => ext_append_lt y g ha
  have hvars : ∀ D ∈ rowsF w n ψ ++ chainF n e, ∀ l ∈ D, l.1 < n + n + (n + 1) := by
    intro D hD l hl
    rcases List.mem_append.1 hD with hD | hD
    · have := (rowsF_vars hψ D hD).2 l hl; omega
    · exact (chainF_vars D hD).2 l hl
  rw [cssF, List.forall_mem_append, sat_congr (f' := ext y) (fun C hC l hl => hlt _ (hvars C hC l hl)), sat_compF]
  have hc : (∀ i < n + (n + 1), ext (Fin.append y g) (n + (n + (n + 1)) + i) =
      !ext (Fin.append y g) (n + i)) ↔ g = fun i => !ext y (n + i.val) := by
    constructor
    · intro H
      funext i
      have := H i.val i.2
      rwa [show n + (n + (n + 1)) + i.val = n + n + (n + 1) + i.val by omega, ext_append_ge, ext_fin,
        hlt _ (by omega)] at this
    · rintro rfl i hi
      rw [show n + (n + (n + 1)) + i = n + n + (n + 1) + i by omega, ext_append_ge, hlt _ (by omega)]
      simp only [CountKSat.ext, dif_pos hi]
  rw [hc]
  have hcnt := count_aux y
  constructor
  · rintro ⟨⟨h1, rfl⟩, h3⟩
    exact ⟨⟨h1, by omega⟩, rfl⟩
  · rintro ⟨⟨h1, h3⟩, rfl⟩
    exact ⟨⟨h1, rfl⟩, by omega⟩

/-- Step B: the chain is determined. -/
theorem stepB (w : ℕ) {ψ : Fml} (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 < n) (s : ℕ) (e : Bool) :
    (univ.filter fun y : Fin (n + n + (n + 1)) → Bool =>
        (∀ D ∈ rowsF w n ψ ++ chainF n e, ∃ l ∈ D, ext y l.1 = l.2) ∧
        (univ.filter fun j : Fin n => ext y j.val = true).card = s).card =
      (univ.filter fun v : Fin (n + n) → Bool => ((∀ D ∈ rowsF w n ψ, ∃ l ∈ D, ext v l.1 = l.2) ∧
        ipB (ext v) n n = e) ∧ (univ.filter fun j : Fin n => ext v j.val = true).card = s).card := by
  refine card_append _ _ (fun v i => ipB (ext v) n i.val) fun v g => ?_
  have hlt : ∀ a < n + n, ext (Fin.append v g) a = ext v a := fun a ha => ext_append_lt v g ha
  have hge : ∀ a, ext (Fin.append v g) (n + n + a) = ext g a := fun a => ext_append_ge v g a
  rw [List.forall_mem_append, sat_congr (f' := ext v) (fun C hC l hl => hlt _ ((rowsF_vars hψ C hC).2 l hl)),
    sat_chainF]
  have h0 : ext (Fin.append v g) (n + n) = ext g 0 := by simpa using hge 0
  have hch : (∀ i < n, ext (Fin.append v g) (n + n + i + 1) = xor (ext (Fin.append v g) (n + n + i))
      (ext (Fin.append v g) i && ext (Fin.append v g) (n + i))) ↔
      ∀ i < n, ext g (i + 1) = xor (ext g i) (ext v i && ext v (n + i)) :=
    forall₂_congr fun i hi => by
      rw [show n + n + i + 1 = n + n + (i + 1) by omega, hge, hge, hlt i (by omega), hlt (n + i) (by omega)]
  have hcard : (univ.filter fun j : Fin n => ext (Fin.append v g) j.val = true) =
      univ.filter fun j : Fin n => ext v j.val = true := by
    ext j; simp only [mem_filter, mem_univ, true_and]; rw [hlt _ (by have := j.2; omega)]
  rw [h0, hge n, hch, hcard]
  constructor
  · rintro ⟨⟨hr, hz, hs, he⟩, hc⟩
    have hg := (chain_iff (ext v) g).1 ⟨hz, hs⟩
    refine ⟨⟨⟨hr, ?_⟩, hc⟩, hg⟩
    rw [hg] at he
    simpa [CountKSat.ext] using he
  · rintro ⟨⟨⟨hr, he⟩, hc⟩, hg⟩
    obtain ⟨hz, hs⟩ := (chain_iff (ext v) g).2 hg
    refine ⟨⟨hr, hz, hs, ?_⟩, hc⟩
    rw [hg]
    simpa [CountKSat.ext] using he

theorem toN_code (H₁ H₂ : List (List (Fin n))) : Decode.toN (codeCNF H₁ H₂) =
    H₁.map (fun r => r.map fun j => (j.val, true)) ++ H₂.map (fun r => r.map fun j => (j.val, false)) := by
  simp [Decode.toN, codeCNF, List.map_map, Function.comp_def]

theorem even_iff (r : List (Fin n)) (x : Fin n → Bool) : (r.map x).count true % 2 = 0 ↔ vecR r ⬝ᵥ vecB x = 0 := by
  rw [vecR_dot, ZMod.natCast_eq_zero_iff]; omega

theorem sat_code {w : ℕ} {H₁ H₂ : List (List (Fin n))} (hw : ∀ r ∈ H₁ ++ H₂, r.length ≤ w) (x y : Fin n → Bool) :
    (∀ D ∈ rowsF w n (Decode.toN (codeCNF H₁ H₂)), ∃ l ∈ D, ext (Fin.append x y) l.1 = l.2) ↔
      InKer H₁ x ∧ InKer H₂ y := by
  have hψ : ∀ C ∈ Decode.toN (codeCNF H₁ H₂), C.length ≤ w := by
    intro C hC
    rw [toN_code, List.mem_append, List.mem_map, List.mem_map] at hC
    rcases hC with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
    · rw [List.length_map]; exact hw r (List.mem_append_left _ hr)
    · rw [List.length_map]; exact hw r (List.mem_append_right _ hr)
  rw [sat_rowsF _ hψ, toN_code, List.forall_mem_append, List.forall_mem_map, List.forall_mem_map]
  have hX : ∀ r : List (Fin n), ((r.map fun j => (j.val, true)).map fun l => ext (Fin.append x y) (pos n l)) =
      r.map x := fun r => by
    rw [List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, pos, cond_true]
    rw [ext_append_lt _ _ j.2, ext_fin]
  have hZ : ∀ r : List (Fin n), ((r.map fun j => (j.val, false)).map fun l => ext (Fin.append x y) (pos n l)) =
      r.map y := fun r => by
    rw [List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, pos, cond_false]
    rw [ext_append_ge, ext_fin]
  simp only [hX, hZ, even_iff]
  rfl

theorem ipB_iff (x y : Fin n → Bool) (e : Bool) :
    ipB (ext (Fin.append x y)) n n = e ↔ vecB x ⬝ᵥ vecB y = toZ e := by
  have hs : ∑ j ∈ range n, toZ (ext (Fin.append x y) j) * toZ (ext (Fin.append x y) (n + j)) =
      vecB x ⬝ᵥ vecB y := by
    rw [dotProduct, ← Fin.sum_univ_eq_sum_range]
    refine sum_congr rfl fun j _ => ?_
    rw [ext_append_lt _ _ j.2, ext_fin, ext_append_ge, ext_fin]
    rfl
  rw [← toZ_inj, toZ_ipB, hs]

open Classical in
/-- **The count**: the satisfying assignments of `cssF` with s + 2n + 1 true variables are the pairs
(x, y) with |x| = s, x ∈ ker H₁, y ∈ ker H₂ and ⟨x, y⟩ = e. -/
theorem cnt_cssF {w : ℕ} (H₁ H₂ : List (List (Fin n))) (hw : ∀ r ∈ H₁ ++ H₂, r.length ≤ w) (s : ℕ) (e : Bool) :
    cntS (n + n + (n + 1) + (n + (n + 1))) (s + (n + (n + 1))) (cssF w n (Decode.toN (codeCNF H₁ H₂)) e) =
      (univ.filter fun p : (Fin n → Bool) × (Fin n → Bool) => (univ.filter fun j => p.1 j = true).card = s ∧
        InKer H₁ p.1 ∧ InKer H₂ p.2 ∧ vecB p.1 ⬝ᵥ vecB p.2 = toZ e).card := by
  have hψ : ∀ C ∈ Decode.toN (codeCNF H₁ H₂), ∀ l ∈ C, l.1 < n := fun C hC => (Decode.mem_toN hC).2
  rw [stepA w hψ, stepB w hψ]
  refine Finset.card_equiv (Fin.appendEquiv n n).symm fun b => ?_
  simp only [mem_filter, mem_univ, true_and]
  obtain ⟨p, rfl⟩ : ∃ p, b = Fin.appendEquiv n n p := ⟨_, ((Fin.appendEquiv _ _).apply_symm_apply b).symm⟩
  rw [Equiv.symm_apply_apply]
  have hb : (Fin.appendEquiv n n) p = Fin.append p.1 p.2 := funext fun a => Fin.appendEquiv_apply _ _ _ _
  have hcard : (univ.filter fun j : Fin n => ext (Fin.append p.1 p.2) j.val = true) =
      univ.filter fun j => p.1 j = true := by
    ext j; simp only [mem_filter, mem_univ, true_and]; rw [ext_append_lt _ _ j.2, ext_fin]
  rw [hb, sat_code hw, ipB_iff, hcard]
  tauto

theorem card_pairs {α β : Type} [Fintype α] [Fintype β] (P : α → Prop) (Q : α → β → Prop) [DecidablePred P]
    [∀ x, DecidablePred (Q x)] :
    (univ.filter fun p : α × β => P p.1 ∧ Q p.1 p.2).card = ∑ x, if P x then (univ.filter (Q x)).card else 0 := by
  rw [card_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  split_ifs with h
  · rw [card_filter]; simp [h]
  · simp [h]

open Classical in
theorem pairs_true (H₁ H₂ : List (List (Fin n))) (s : ℕ) :
    2 * (univ.filter fun p : (Fin n → Bool) × (Fin n → Bool) => (univ.filter fun j => p.1 j = true).card = s ∧
        InKer H₁ p.1 ∧ InKer H₂ p.2 ∧ vecB p.1 ⬝ᵥ vecB p.2 = toZ true).card =
      (univ.filter fun y => InKer H₂ y).card * numLog H₁ H₂ s := by
  have e1 : (univ.filter fun p : (Fin n → Bool) × (Fin n → Bool) => (univ.filter fun j => p.1 j = true).card = s ∧
        InKer H₁ p.1 ∧ InKer H₂ p.2 ∧ vecB p.1 ⬝ᵥ vecB p.2 = toZ true) =
      univ.filter fun p : (Fin n → Bool) × (Fin n → Bool) => ((univ.filter fun j => p.1 j = true).card = s ∧
        InKer H₁ p.1) ∧ (InKer H₂ p.2 ∧ vecB p.1 ⬝ᵥ vecB p.2 = 1) := by
    refine filter_congr fun p _ => ?_
    simp only [toZ, if_true, and_assoc]
  have key : ∀ x : Fin n → Bool, 2 * (if (univ.filter fun j => x j = true).card = s ∧ InKer H₁ x then
      (univ.filter fun y => InKer H₂ y ∧ vecB x ⬝ᵥ vecB y = 1).card else 0) =
      if ((univ.filter fun j => x j = true).card = s ∧ InKer H₁ x) ∧ vecB x ∉ rowSp H₂ then
        (univ.filter fun y => InKer H₂ y).card else 0 := fun x => by
    rw [mul_ite, mul_zero, half]
    simp only [logical_iff]
    by_cases hP : (univ.filter fun j => x j = true).card = s ∧ InKer H₁ x <;> simp [hP]
  have e2 : (univ.filter fun x : Fin n → Bool => ((univ.filter fun j => x j = true).card = s ∧ InKer H₁ x) ∧
      vecB x ∉ rowSp H₂).card = numLog H₁ H₂ s := by
    rw [numLog]; congr 1; exact filter_congr fun x _ => and_assoc
  rw [e1, card_pairs (fun x => (univ.filter fun j => x j = true).card = s ∧ InKer H₁ x)
    (fun x y => InKer H₂ y ∧ vecB x ⬝ᵥ vecB y = 1), mul_sum, sum_congr rfl fun x _ => key x, ← sum_filter, sum_const, smul_eq_mul, e2, mul_comm]

open Classical in
theorem pairs_false (H₁ H₂ : List (List (Fin n))) :
    (univ.filter fun p : (Fin n → Bool) × (Fin n → Bool) => (univ.filter fun j => p.1 j = true).card = 0 ∧
        InKer H₁ p.1 ∧ InKer H₂ p.2 ∧ vecB p.1 ⬝ᵥ vecB p.2 = toZ false).card =
      (univ.filter fun y => InKer H₂ y).card := by
  have h0 : ∀ y : Fin n → Bool, vecB (fun _ => false) ⬝ᵥ vecB y = 0 := fun y => by simp [vecB, toZ, dotProduct]
  have hK : InKer H₁ (fun _ => false) := fun r _ => by simp [vecB, toZ, dotProduct]
  refine card_nbij' (fun p => p.2) (fun y => (fun _ => false, y)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    exact hp.2.2.1
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    exact ⟨by simp, hK, hy, by rw [h0]; rfl⟩
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp
    have hz := filter_eq_empty_iff.1 (card_eq_zero.1 hp.1)
    exact Prod.ext (funext fun j => by simpa using (hz (mem_univ j))) rfl
  · intro y _
    rfl

open Classical in
/-- **The number of logical operators of weight s** from two counts of `cssF`. -/
theorem numLog_eq {w : ℕ} (H₁ H₂ : List (List (Fin n))) (hw : ∀ r ∈ H₁ ++ H₂, r.length ≤ w) (s : ℕ) :
    2 * cntS (n + n + (n + 1) + (n + (n + 1))) (s + (n + (n + 1))) (cssF w n (Decode.toN (codeCNF H₁ H₂)) true) /
      cntS (n + n + (n + 1) + (n + (n + 1))) (n + (n + 1)) (cssF w n (Decode.toN (codeCNF H₁ H₂)) false) =
      numLog H₁ H₂ s := by
  have h0 := cnt_cssF H₁ H₂ hw 0 false
  rw [zero_add] at h0
  rw [cnt_cssF H₁ H₂ hw, h0, pairs_true, pairs_false]
  have : 0 < (univ.filter fun y => InKer H₂ y).card :=
    card_pos.2 ⟨fun _ => false, by simp [InKer, vecB, toZ, dotProduct]⟩
  exact Nat.mul_div_cancel_left _ this

end Count

end EthCor.Code
