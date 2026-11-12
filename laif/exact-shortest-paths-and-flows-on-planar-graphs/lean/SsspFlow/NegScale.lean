import SsspFlow.NegLevels

/-!
# Scaling, negative cycles and the output: Lemma 5 and Section 5 of `notes/NEGATIVE.md`

The weights `x = 2((n + 1) w + 1)` are rounded in phases. A phase with bound `B` divides the reduced
weights by `ρ`, adds `α` (`ysc`), keeps the arcs of rounded weight at most `n` (`keptS`), and adds
`ρ` times the last potential of its levels (`phiNext`). Without a negative closed walk, and if the
decompositions behave (`DecOK`), the reduced weights stay at least `-B` (`scale_all`), and the bound
is `0` after `nPhase B₀` phases (`Bseq_nPhase`). A negative closed walk leaves an arc of negative
reduced weight for every potential (`exists_bad_arc`). Without one, the least reduced walk from `s`
gives the least weight (`negSpec_of`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal
open Cslib.Congest

namespace SsspFlow

namespace Walk

section Arith

variable {V : Type} {adj : V → V → Prop}

lemma zw_congr {f g : V → V → ℤ} (h : ∀ a b, adj a b → f a b = g a b) :
    ∀ {a b : V} (p : Walk adj a b), p.zw f = p.zw g
  | _, _, .nil _ => rfl
  | _, _, .cons e p => by rw [zw_cons, zw_cons, h _ _ e, zw_congr h p]

lemma zw_affine (f : V → V → ℤ) (c d : ℤ) : ∀ {a b : V} (p : Walk adj a b),
    p.zw (fun a b => c * f a b + d) = c * p.zw f + d * p.len
  | _, _, .nil _ => by simp
  | _, _, .cons e p => by
    simp only [zw_cons, len_cons, zw_affine f c d p]
    push_cast
    ring

/-- Rounding down loses less than `ρ` on each arc. -/
lemma zw_round (f : V → V → ℤ) {ρ : ℤ} (hρ : 0 < ρ) (α : ℤ) : ∀ {a b : V} (p : Walk adj a b),
    p.zw f + p.len * (1 - ρ + ρ * α) ≤ ρ * p.zw (fun a b => f a b / ρ + α)
  | _, _, .nil _ => by simp
  | _, _, @cons _ _ a m _ e p => by
    have ih := zw_round f hρ α p
    have h₁ := Int.lt_mul_ediv_self_add (x := f a m) hρ
    simp only [zw_cons, len_cons]
    push_cast
    linarith

lemma exists_neg_arc {f : V → V → ℤ} : ∀ {a b : V} (p : Walk adj a b), p.zw f < 0 →
    ∃ u v, adj u v ∧ f u v < 0
  | _, _, .nil _, h => by simp at h
  | _, _, @cons _ _ a m _ e p, h => by
    rw [zw_cons] at h
    by_cases hf : f a m < 0
    · exact ⟨a, m, e, hf⟩
    · exact exists_neg_arc p (by omega)

lemma end_mem_support : ∀ {a b : V} (p : Walk adj a b), b ∈ p.support
  | _, _, .nil _ => by simp
  | _, _, .cons e p => by simp [end_mem_support p]

lemma zw_nodup_closed (y : V → V → ℤ) : ∀ {a b : V} (p : Walk adj a b), a = b → p.support.Nodup →
    p.zw y = 0
  | _, _, .nil _, _, _ => rfl
  | _, _, .cons e p, rfl, h => by
    rw [support_cons, List.nodup_cons] at h
    exact absurd (end_mem_support p) h.1

/-- **Shortcuts from short cycles.** If closed walks with at most `card V` arcs have nonnegative
weight, every walk can be replaced by one without repeated vertices that is not heavier. -/
lemma exists_nodup_le_of_short [Fintype V] [DecidableEq V] (y : V → V → ℤ)
    (hC : ∀ a (C : Walk adj a a), C.len ≤ Fintype.card V → 0 ≤ C.zw y) :
    ∀ {a b : V} (p : Walk adj a b), ∃ q : Walk adj a b, q.support.Nodup ∧ q.zw y ≤ p.zw y ∧
      q.len ≤ p.len
  | _, _, nil a => ⟨nil a, by simp, le_rfl, le_rfl⟩
  | a, _, cons e p => by
    obtain ⟨q, hq, hw, hl⟩ := exists_nodup_le_of_short y hC p
    by_cases ha : a ∈ q.support
    · obtain ⟨s, r, h₁, h₂, h₃⟩ := exists_cut y q ha
      have hlen := len_lt_card q hq
      have hc := hC a (cons e s) (by rw [len_cons]; omega)
      rw [zw_cons] at hc
      refine ⟨r, h₁.nodup hq, ?_, ?_⟩
      · rw [zw_cons]
        omega
      · rw [len_cons]
        omega
    · refine ⟨cons e q, by simp [ha, hq], ?_, ?_⟩
      · rw [zw_cons, zw_cons]
        omega
      · rw [len_cons, len_cons]
        omega

/-- A negative closed walk gives one with at most `card V` arcs. -/
lemma exists_short_neg [Fintype V] [DecidableEq V] {y : V → V → ℤ} {a : V} (C : Walk adj a a)
    (hC : C.zw y < 0) : ∃ b, ∃ C' : Walk adj b b, C'.len ≤ Fintype.card V ∧ C'.zw y < 0 := by
  by_contra h
  push Not at h
  obtain ⟨q, hq, hw, -⟩ := exists_nodup_le_of_short y (fun b C' hl => h b C' hl) C
  have := zw_nodup_closed y q rfl hq
  omega

lemma nwt_toNat {f : V → V → ℤ} (h : ∀ a b, adj a b → 0 ≤ f a b) : ∀ {a b : V} (p : Walk adj a b),
    (p.nwt (fun a b => (f a b).toNat) : ℤ) = p.zw f
  | _, _, .nil _ => rfl
  | _, _, .cons e p => by
    rw [nwt_cons, zw_cons, Nat.cast_add, nwt_toNat h p, Int.toNat_of_nonneg (h _ _ e)]

lemma wt_zero : ∀ {a b : V} (p : Walk adj a b), p.wt (Congest.lenTop fun _ _ => (0 : ℕ∞)) = 0
  | _, _, .nil _ => by simp
  | _, _, .cons e p => by simp [wt_zero p, Congest.lenTop]

/-- A walk of the graph is a walk along its adjacency. -/
lemma nonempty_of_sg {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : Nonempty (Walk G.Adj a b) := by
  induction p with
  | nil => exact ⟨.nil _⟩
  | cons h _ ih => exact ⟨.cons h ih.some⟩

end Arith

end Walk

namespace Congest

/-! ### The bounds of the phases -/

/-- The divisor of a phase with bound `B`. -/
def rhoB (B : ℕ) : ℕ := if 5 ≤ B then (B + 2) / 3 else 1

/-- The added constant of a phase with bound `B`. -/
def alphaB (B : ℕ) : ℕ := if 5 ≤ B then 2 else B - 1

/-- The bound after a phase. -/
def bnext (B : ℕ) : ℕ := rhoB B * alphaB B

/-- The bounds of the phases, from `B₀`. -/
def Bseq (B₀ : ℕ) : ℕ → ℕ
  | 0 => B₀
  | j + 1 => bnext (Bseq B₀ j)

/-- The number of phases. -/
def nPhase (B₀ : ℕ) : ℕ := 2 * (Nat.log 2 B₀ + 1) + 4

theorem rhoB_pos (B : ℕ) : 0 < rhoB B := by
  unfold rhoB
  split_ifs <;> omega

theorem rhoB_le (B : ℕ) : rhoB B ≤ B + 1 := by
  unfold rhoB
  split_ifs <;> omega

theorem bnext_le (B : ℕ) : bnext B ≤ B := by
  unfold bnext rhoB alphaB
  split_ifs <;> omega

theorem bnext_big {B : ℕ} (h : 5 ≤ B) : 4 ≤ bnext B ∧ 3 * (bnext B - 4) ≤ 2 * (B - 4) := by
  unfold bnext rhoB alphaB
  split_ifs
  omega

theorem bnext_small {B : ℕ} (h : B ≤ 4) : bnext B = B - 1 := by
  unfold bnext rhoB alphaB
  split_ifs <;> omega

theorem Bseq_anti (B₀ : ℕ) {i j : ℕ} (h : i ≤ j) : Bseq B₀ j ≤ Bseq B₀ i := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (bnext_le _).trans ih

theorem Bseq_le (B₀ j : ℕ) : Bseq B₀ j ≤ B₀ := Bseq_anti B₀ (Nat.zero_le j)

theorem Bseq_big (B₀ : ℕ) : ∀ m, 5 ≤ Bseq B₀ m → 3 ^ m * (Bseq B₀ m - 4) ≤ 2 ^ m * B₀
  | 0, _ => by
    show 3 ^ 0 * (B₀ - 4) ≤ 2 ^ 0 * B₀
    omega
  | m + 1, h => by
    have hm : 5 ≤ Bseq B₀ m := h.trans (bnext_le _)
    have ih := Bseq_big B₀ m hm
    have h₁ := (bnext_big hm).2
    show 3 ^ (m + 1) * (bnext (Bseq B₀ m) - 4) ≤ 2 ^ (m + 1) * B₀
    generalize bnext (Bseq B₀ m) - 4 = y at h₁ ⊢
    generalize Bseq B₀ m - 4 = z at h₁ ih
    calc 3 ^ (m + 1) * y = 3 ^ m * (3 * y) := by ring
      _ ≤ 3 ^ m * (2 * z) := Nat.mul_le_mul_left _ h₁
      _ = 2 * (3 ^ m * z) := by ring
      _ ≤ 2 * (2 ^ m * B₀) := Nat.mul_le_mul_left _ ih
      _ = 2 ^ (m + 1) * B₀ := by ring

/-- The bound is `0` after `nPhase B₀` phases. -/
theorem Bseq_nPhase (B₀ : ℕ) : Bseq B₀ (nPhase B₀) = 0 := by
  have h2 : B₀ < 2 ^ (Nat.log 2 B₀ + 1) := Nat.lt_pow_succ_log_self (by norm_num) B₀
  unfold nPhase
  generalize Nat.log 2 B₀ + 1 = x at h2 ⊢
  have h4 : Bseq B₀ (2 * x) ≤ 4 := by
    by_contra h
    have h5 := Bseq_big B₀ (2 * x) (by omega)
    have h3 : 3 ^ (2 * x) ≤ 2 ^ (2 * x) * B₀ :=
      le_trans (Nat.le_mul_of_pos_right _ (by omega)) h5
    rw [pow_mul, pow_mul] at h3
    norm_num at h3
    have h6 : 4 ^ x * B₀ < 4 ^ x * 2 ^ x := Nat.mul_lt_mul_of_pos_left h2 (by positivity)
    have h7 : 4 ^ x * 2 ^ x ≤ 9 ^ x := by
      rw [← mul_pow]
      exact Nat.pow_le_pow_left (by norm_num) x
    exact absurd (h3.trans_lt (h6.trans_le h7)) (lt_irrefl _)
  have step : ∀ i, Bseq B₀ (2 * x + i) ≤ 4 - i := by
    intro i
    induction i with
    | zero => simpa using h4
    | succ i ih =>
      show bnext (Bseq B₀ (2 * x + i)) ≤ 4 - (i + 1)
      rw [bnext_small (by omega)]
      omega
  have := step 4
  omega

/-! ### The phases -/

section Phase

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The scaled weights `x = 2((n + 1) w + 1)`. -/
def xw (n : ℕ) (w : V → V → Option ℤ) (a b : V) : ℤ := 2 * (((n : ℤ) + 1) * zWt w a b + 1)

/-- The rounded weights of a phase with bound `B` and potential `φ`, at least `-1`. -/
def ysc (n : ℕ) (w : V → V → Option ℤ) (φ : V → ℤ) (B : ℕ) (a b : V) : ℤ :=
  max (-1) (yr (xw n w) φ a b / (rhoB B : ℤ) + (alphaB B : ℤ))

/-- The kept arcs of a phase: finite weight and rounded weight at most `n`. -/
def keptS (adj : V → V → Prop) (n : ℕ) (w : V → V → Option ℤ) (φ : V → ℤ) (B : ℕ) (a b : V) : Prop :=
  zArc adj w a b ∧ ysc n w φ B a b ≤ n

/-- The conditions of `Good` that depend on the decompositions. -/
def DecOK (L R t : ℕ) (kept : V → V → Prop) (ys : V → V → ℤ) (idx : ℕ → ℕ → V → ℕ) : Prop :=
  (∀ ℓ < L, ∀ r ≤ R, ∀ u v, idx ℓ r u = idx ℓ r v →
    ∃ Q : Walk kept u v, Q.nwt (posPart ys) ≤ 2 ^ (ℓ + 1)) ∧
  ∀ ℓ, 1 ≤ ℓ → ℓ ≤ L → ∀ r ≤ R, ∀ v, ∃ a, ∃ P : Walk (clArc L kept idx ℓ r) a v,
    P.zw ys = wdist (clArc L kept idx ℓ r) ys v ∧ ∃ r' ≤ R, P.cnt (cutArc idx (ℓ - 1) r') ≤ t

/-- The potential of a phase: the last of its levels. -/
noncomputable def psiS (adj : V → V → Prop) (n L R t : ℕ) (w : V → V → Option ℤ) (φ : V → ℤ)
    (B : ℕ) (idx : ℕ → ℕ → V → ℕ) : V → ℤ :=
  levPhi n L R t (keptS adj n w φ B) (ysc n w φ B) idx L 0

/-- The potential after a phase. -/
noncomputable def phiNext (adj : V → V → Prop) (n L R t : ℕ) (w : V → V → Option ℤ) (φ : V → ℤ)
    (B : ℕ) (idx : ℕ → ℕ → V → ℕ) (v : V) : ℤ :=
  φ v + rhoB B * psiS adj n L R t w φ B idx v

/-- The potentials of the phases. Phase `j` with potential `φ` uses the decompositions `dec j φ`. -/
noncomputable def phiS (adj : V → V → Prop) (n L R t : ℕ) (w : V → V → Option ℤ) (B₀ : ℕ)
    (dec : ℕ → (V → ℤ) → ℕ → ℕ → V → ℕ) : ℕ → V → ℤ
  | 0 => fun _ => 0
  | j + 1 => phiNext adj n L R t w (phiS adj n L R t w B₀ dec j) (Bseq B₀ j)
      (dec j (phiS adj n L R t w B₀ dec j))

variable {adj : V → V → Prop} {n L R t : ℕ} {w : V → V → Option ℤ}

theorem zw_xw : ∀ {a b : V} (p : Walk adj a b),
    p.zw (xw n w) = 2 * ((n : ℤ) + 1) * p.zw (zWt w) + 2 * p.len
  | _, _, .nil _ => by simp
  | _, _, .cons e p => by
    simp only [Walk.zw_cons, Walk.len_cons, zw_xw p, xw]
    push_cast
    ring

theorem psiS_bounds (φ : V → ℤ) (B : ℕ) (idx : ℕ → ℕ → V → ℕ) (v : V) :
    -(n : ℤ) ≤ psiS adj n L R t w φ B idx v ∧ psiS adj n L R t w φ B idx v ≤ 0 :=
  levPhi_last_bounds v

/-- The potentials stay in `[-j (B₀ + 1) n, 0]`, on every input. -/
theorem phiS_bounds (B₀ : ℕ) (dec : ℕ → (V → ℤ) → ℕ → ℕ → V → ℕ) : ∀ j v,
    -(((j * (B₀ + 1) * n : ℕ)) : ℤ) ≤ phiS adj n L R t w B₀ dec j v ∧
      phiS adj n L R t w B₀ dec j v ≤ 0
  | 0, v => by simp [phiS]
  | j + 1, v => by
    obtain ⟨h₁, h₂⟩ := phiS_bounds B₀ dec j v
    obtain ⟨h₃, h₄⟩ := psiS_bounds (adj := adj) (n := n) (L := L) (R := R) (t := t) (w := w)
      (phiS adj n L R t w B₀ dec j) (Bseq B₀ j) (dec j (phiS adj n L R t w B₀ dec j)) v
    have hρ : rhoB (Bseq B₀ j) ≤ B₀ + 1 := (rhoB_le _).trans (by have := Bseq_le B₀ j; omega)
    have hρ' : ((rhoB (Bseq B₀ j) : ℕ) : ℤ) ≤ (B₀ : ℤ) + 1 := by exact_mod_cast hρ
    have hρ0 : (0 : ℤ) ≤ (rhoB (Bseq B₀ j) : ℤ) := Int.natCast_nonneg _
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg _
    show _ ≤ phiNext adj n L R t w _ _ _ v ∧ phiNext adj n L R t w _ _ _ v ≤ 0
    unfold phiNext
    push_cast at h₁ ⊢
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left h₃ hρ0, mul_le_mul_of_nonneg_right hρ' hn0]
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos hρ0 h₄]

theorem rhoB_pos' (B : ℕ) : (0 : ℤ) < rhoB B := by exact_mod_cast rhoB_pos B

/-- With reduced weights at least `-B`, the rounding never needs the clip at `-1`. -/
theorem ysc_eq {φ : V → ℤ} {B : ℕ} (hB : ∀ a b, zArc adj w a b → -(B : ℤ) ≤ yr (xw n w) φ a b)
    {a b : V} (hab : zArc adj w a b) :
    ysc n w φ B a b = yr (xw n w) φ a b / (rhoB B : ℤ) + (alphaB B : ℤ) := by
  have hlow : (B : ℤ) ≤ (rhoB B : ℤ) * ((alphaB B : ℤ) + 1) := by
    have : B ≤ rhoB B * (alphaB B + 1) := by
      unfold rhoB alphaB
      split_ifs <;> omega
    exact_mod_cast this
  exact max_eq_right (NegScaling.round_low (rhoB_pos' B) (hB a b hab) hlow)

/-- **Lemma 5, first part.** Without negative closed walks and with reduced weights at least `-B`,
the rounded weights on the kept arcs are restricted. -/
theorem restr_of_bound (hneg : ∀ a (C : Walk (zArc adj w) a a), 0 ≤ C.zw (zWt w))
    {φ : V → ℤ} {B : ℕ} (hB : ∀ a b, zArc adj w a b → -(B : ℤ) ≤ yr (xw n w) φ a b) :
    Restr (keptS adj n w φ B) (ysc n w φ B) := by
  have hρ := rhoB_pos' B
  have hmean : (rhoB B : ℤ) ≤ (rhoB B : ℤ) * (alphaB B : ℤ) - rhoB B + 3 := by
    have : rhoB B + rhoB B ≤ rhoB B * alphaB B + 3 := by
      unfold rhoB alphaB
      split_ifs <;> omega
    have h' : ((rhoB B + rhoB B : ℕ) : ℤ) ≤ ((rhoB B * alphaB B + 3 : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at h'
    linarith
  refine ⟨fun a b _ => le_max_left _ _, fun a C => ?_⟩
  have hE : ∀ a b, keptS adj n w φ B a b → zArc adj w a b := fun _ _ h => h.1
  have e1 : C.zw (ysc n w φ B) =
      C.zw (fun a b => yr (xw n w) φ a b / (rhoB B : ℤ) + (alphaB B : ℤ)) :=
    Walk.zw_congr (fun a b h => ysc_eq hB h.1) C
  have e2 := Walk.zw_round (yr (xw n w) φ) hρ (alphaB B : ℤ) C
  have e3 : C.zw (yr (xw n w) φ) = C.zw (xw n w) := by
    rw [zw_yr]
    ring
  have e4 := zw_xw (n := n) (w := w) C
  have e5 : 0 ≤ (C.lift hE).zw (zWt w) := hneg a (C.lift hE)
  rw [Walk.zw_lift] at e5
  have hlen : (0 : ℤ) ≤ C.len := Int.natCast_nonneg _
  have h6 := mul_nonneg (by positivity : (0 : ℤ) ≤ 2 * ((n : ℤ) + 1)) e5
  have h7 := mul_le_mul_of_nonneg_left hmean hlen
  have key : (rhoB B : ℤ) * C.len ≤ (rhoB B : ℤ) * C.zw (ysc n w φ B) := by
    rw [e1]
    nlinarith
  exact le_of_mul_le_mul_left key hρ

/-- **Lemma 5 with Proposition 4.** Without negative closed walks, a phase with reduced weights at
least `-B`, in which the decompositions behave, leaves reduced weights at least `-bnext B`. -/
theorem scale_step (hcard : Fintype.card V ≤ n)
    (hneg : ∀ a (C : Walk (zArc adj w) a a), 0 ≤ C.zw (zWt w))
    {φ : V → ℤ} {B : ℕ} (hB : ∀ a b, zArc adj w a b → -(B : ℤ) ≤ yr (xw n w) φ a b)
    (ht : 2 ≤ t) (hL : 1 ≤ L) {idx : ℕ → ℕ → V → ℕ}
    (hdec : DecOK L R t (keptS adj n w φ B) (ysc n w φ B) idx) (a b : V) (hab : zArc adj w a b) :
    -(bnext B : ℤ) ≤ yr (xw n w) (phiNext adj n L R t w φ B idx) a b := by
  have hρ := rhoB_pos' B
  have hys : ∀ a b, zArc adj w a b →
      ysc n w φ B a b = yr (xw n w) φ a b / (rhoB B : ℤ) + (alphaB B : ℤ) := fun a b h =>
    ysc_eq hB h
  have hG : Good n L R t (keptS adj n w φ B) (ysc n w φ B) idx :=
    ⟨hcard, restr_of_bound hneg hB, ht, hL, hdec.1, hdec.2⟩
  obtain ⟨hψa, -⟩ := psiS_bounds (adj := adj) (n := n) (L := L) (R := R) (t := t) (w := w) φ B idx a
  obtain ⟨-, hψb⟩ := psiS_bounds (adj := adj) (n := n) (L := L) (R := R) (t := t) (w := w) φ B idx b
  have harc : 0 ≤ yr (xw n w) φ a b / (rhoB B : ℤ) + (alphaB B : ℤ) +
      psiS adj n L R t w φ B idx a - psiS adj n L R t w φ B idx b := by
    rw [← hys a b hab]
    by_cases hk : keptS adj n w φ B a b
    · unfold psiS
      exact hG.levPhi_last hk
    · have : (n : ℤ) < ysc n w φ B a b := by
        by_contra h
        exact hk ⟨hab, not_lt.1 h⟩
      linarith
  have := NegScaling.round_back hρ harc
  unfold phiNext yr
  unfold yr at this
  unfold bnext
  push_cast
  linarith

/-- **The phases.** Without negative closed walks, if the decompositions of the first `m` phases
behave, the reduced weights after them are at least `-Bseq B₀ m`. -/
theorem scale_all (hcard : Fintype.card V ≤ n)
    (hneg : ∀ a (C : Walk (zArc adj w) a a), 0 ≤ C.zw (zWt w)) (ht : 2 ≤ t) (hL : 1 ≤ L)
    {B₀ : ℕ} (hB₀ : ∀ a b, zArc adj w a b → -(B₀ : ℤ) ≤ xw n w a b)
    {dec : ℕ → (V → ℤ) → ℕ → ℕ → V → ℕ} : ∀ m,
    (∀ j < m, DecOK L R t (keptS adj n w (phiS adj n L R t w B₀ dec j) (Bseq B₀ j))
      (ysc n w (phiS adj n L R t w B₀ dec j) (Bseq B₀ j)) (dec j (phiS adj n L R t w B₀ dec j))) →
    ∀ a b, zArc adj w a b → -(Bseq B₀ m : ℤ) ≤ yr (xw n w) (phiS adj n L R t w B₀ dec m) a b
  | 0, _, a, b, hab => by simpa [phiS, yr, Bseq] using hB₀ a b hab
  | m + 1, h, a, b, hab =>
    scale_step hcard hneg (scale_all hcard hneg ht hL hB₀ m fun j hj => h j (by omega)) ht hL
      (h m (by omega)) a b hab

/-- A negative closed walk leaves an arc of negative reduced weight, for every potential. -/
theorem exists_bad_arc (hcard : Fintype.card V ≤ n) {a : V} (C : Walk (zArc adj w) a a)
    (hC : C.zw (zWt w) < 0) (φ : V → ℤ) : ∃ u v, zArc adj w u v ∧ yr (xw n w) φ u v < 0 := by
  obtain ⟨b, C', hlen, hneg⟩ := Walk.exists_short_neg C hC
  refine Walk.exists_neg_arc C' ?_
  rw [zw_yr, zw_xw]
  have : (C'.len : ℤ) ≤ n := by exact_mod_cast hlen.trans hcard
  nlinarith

end Phase

/-! ### The output -/

section Output

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Offset `c` at `s` and `⊤` elsewhere. -/
def single (s : V) (c : ℕ) (a : V) : ℕ∞ := if a = s then (c : ℕ∞) else ⊤

/-- The lengths of the last call: the reduced weights, as natural numbers. -/
def lenX (n : ℕ) (w : V → V → Option ℤ) (φ : V → ℤ) (a b : V) : ℕ := (yr (xw n w) φ a b).toNat

/-- The output of a node from the bit of the check, the value of the last call and its potential. -/
def outS (n : ℕ) (bad : Bool) (m : ℕ∞) (φv : ℤ) : Option (Option ℤ) :=
  if bad then none
  else if m = ⊤ then some none
  else some (some (((m.toNat : ℤ) + φv) / (2 * ((n : ℤ) + 1))))

variable {adj E : V → V → Prop} (hE : ∀ a b, E a b → adj a b) (len : V → V → ℕ)

include hE in
theorem dsrc_single_le {s v : V} (c : ℕ) (p : Walk E s v) :
    dsrc adj (lenTop (restrictLen E len)) (offTop (single s c)) v ≤ ((c + p.nwt len : ℕ) : ℝ≥0∞) := by
  refine (dsrc_le_walk _ _ (p.lift hE)).trans_eq ?_
  rw [wt_restrict hE len p]
  simp [offTop, single]

include hE in
/-- **One source.** A finite value is the offset plus the least length of a walk along `E`. -/
theorem dsrc_single_spec {s v : V} (c : ℕ)
    (h : dsrc adj (lenTop (restrictLen E len)) (offTop (single s c)) v ≠ ⊤) :
    ∃ p : Walk E s v,
      dsrc adj (lenTop (restrictLen E len)) (offTop (single s c)) v = ((c + p.nwt len : ℕ) : ℝ≥0∞) ∧
      ∀ q : Walk E s v, p.nwt len ≤ q.nwt len := by
  classical
  have hex : ∃ k, ∃ p : Walk E s v, p.nwt len = k := by
    obtain ⟨a, p, hp⟩ := dsrc_lt_iff.1 (lt_top_iff_ne_top.2 h)
    by_cases ha : a = s
    · subst ha
      have hp' : p.wt (lenTop (restrictLen E len)) ≠ ⊤ := fun h' => by simp [h'] at hp
      obtain ⟨q, -⟩ := exists_of_wt_ne_top len p hp'
      exact ⟨_, q, rfl⟩
    · simp [offTop, single, ha] at hp
  obtain ⟨p, hp⟩ := Nat.find_spec hex
  have hmin : ∀ q : Walk E s v, p.nwt len ≤ q.nwt len := fun q => hp ▸ Nat.find_min' hex ⟨q, rfl⟩
  refine ⟨p, le_antisymm (dsrc_single_le hE len c p) ?_, hmin⟩
  refine le_dsrc fun a q => ?_
  by_cases ha : a = s
  · subst ha
    by_cases hq : q.wt (lenTop (restrictLen E len)) = ⊤
    · rw [hq, add_top]
      exact le_top
    · obtain ⟨q', hq'⟩ := exists_of_wt_ne_top len q hq
      rw [← hq']
      have h₁ : c + p.nwt len ≤ c + q'.nwt len := by have := hmin q'; omega
      have h₂ : ((c + p.nwt len : ℕ) : ℝ≥0∞) ≤ ((c + q'.nwt len : ℕ) : ℝ≥0∞) := by exact_mod_cast h₁
      simpa [offTop, single] using h₂
  · simp [offTop, single, ha]

omit hE in
/-- **The check.** With lengths `0` and offsets `0` on a set `P`, `⊤` elsewhere, the value is finite
at `v` exactly if `P` is not empty, in a connected graph. -/
theorem dsrc_or (conn : ∀ u v, Nonempty (Walk adj u v)) (P : V → Prop) [DecidablePred P] (v : V) :
    dsrc adj (lenTop fun _ _ => (0 : ℕ∞)) (offTop fun a => if P a then (0 : ℕ∞) else ⊤) v ≠ ⊤ ↔
      ∃ a, P a := by
  constructor
  · intro h
    obtain ⟨a, p, hp⟩ := dsrc_lt_iff.1 (lt_top_iff_ne_top.2 h)
    by_contra hn
    push Not at hn
    simp [offTop, hn a] at hp
  · rintro ⟨a, ha⟩
    refine ne_top_of_le_ne_top (b := 0) ENNReal.zero_ne_top ?_
    refine (dsrc_le_walk _ _ (conn a v).some).trans_eq ?_
    simp [offTop, ha, Walk.wt_zero]

variable {n : ℕ} {w : V → V → Option ℤ}

/-- The least walk of the reduced weights gives the least weight. -/
theorem least_of_xw (hcard : Fintype.card V ≤ n)
    (hneg : ∀ a (C : Walk (zArc adj w) a a), 0 ≤ C.zw (zWt w)) {s v : V}
    (p : Walk (zArc adj w) s v) (hp : ∀ q : Walk (zArc adj w) s v, p.zw (xw n w) ≤ q.zw (xw n w)) :
    IsLeast {y | WalkZ adj w s v y} (p.zw (xw n w) / (2 * ((n : ℤ) + 1))) := by
  have hnegX : ∀ a (C : Walk (zArc adj w) a a), 0 ≤ C.zw (xw n w) := fun a C => by
    rw [zw_xw]
    have := hneg a C
    positivity
  obtain ⟨p₁, hp₁, hw₁, -⟩ := Walk.exists_nodup_le (xw n w) hnegX p
  have heq : p₁.zw (xw n w) = p.zw (xw n w) := le_antisymm hw₁ (hp p₁)
  have hlen₁ := Walk.len_lt_card p₁ hp₁
  have hval : p.zw (xw n w) / (2 * ((n : ℤ) + 1)) = p₁.zw (zWt w) := by
    rw [← heq, zw_xw]
    exact NegScaling.hop_recover (Int.natCast_nonneg _) (by omega)
  rw [hval]
  refine ⟨walkZ_iff.2 ⟨p₁, rfl⟩, ?_⟩
  rintro y hy
  obtain ⟨q, rfl⟩ := walkZ_iff.1 hy
  obtain ⟨q₁, hq₁, hwq, -⟩ := Walk.exists_nodup_le (zWt w) hneg q
  have hlenq := Walk.len_lt_card q₁ hq₁
  by_contra hlt
  push Not at hlt
  have h1 := hp q₁
  rw [← heq, zw_xw, zw_xw] at h1
  have h2 : q₁.zw (zWt w) + 1 ≤ p₁.zw (zWt w) := by omega
  have h3 : (q₁.len : ℤ) + 1 ≤ n := by omega
  have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℤ) ≤ 2 * ((n : ℤ) + 1))
  have h5 : (0 : ℤ) ≤ p₁.len := Int.natCast_nonneg _
  nlinarith

/-- **The output.** With the bit of the check and the value of the last call at every node, the
output is correct, if the potential makes all arcs nonnegative whenever there is no negative cycle. -/
theorem negSpec_of {N : Net V} (hcard : Fintype.card V ≤ n) {s : V} {φ : V → ℤ} (hφ : φ s ≤ 0)
    (bad : V → Bool) (m : V → ℕ∞)
    (hbad : ∀ v, bad v = true ↔ ∃ a b, zArc N.G.Adj w a b ∧ yr (xw n w) φ a b < 0)
    (hm : ∀ v, (m v : ℝ≥0∞) = dsrc N.G.Adj (lenTop (restrictLen (zArc N.G.Adj w) (lenX n w φ)))
      (offTop (single s (-φ s).toNat)) v)
    (hgood : ¬ N.HasNegCycle w → ∀ a b, zArc N.G.Adj w a b → 0 ≤ yr (xw n w) φ a b) :
    N.NegSpec w s fun v => outS n (bad v) (m v) (φ v) := by
  by_cases hc : N.HasNegCycle w
  · left
    refine ⟨hc, fun v => ?_⟩
    obtain ⟨a, y, hy, hy0⟩ := hc
    obtain ⟨C, rfl⟩ := walkZ_iff.1 hy
    have := (hbad v).2 (exists_bad_arc hcard C hy0 φ)
    simp [outS, this]
  · right
    refine ⟨hc, fun v => ?_⟩
    have hneg : ∀ a (C : Walk (zArc N.G.Adj w) a a), 0 ≤ C.zw (zWt w) := by
      intro a C
      by_contra h
      push Not at h
      exact hc ⟨a, _, walkZ_iff.2 ⟨C, rfl⟩, h⟩
    have hpos := hgood hc
    have hb : bad v = false := by
      by_contra h
      obtain ⟨a, b, hab, hlt⟩ := (hbad v).1 (by simpa using h)
      exact absurd (hpos a b hab) (not_le.2 hlt)
    have hE : ∀ a b, zArc N.G.Adj w a b → N.G.Adj a b := fun _ _ h => h.1
    by_cases hmt : m v = ⊤
    · left
      refine ⟨by simp [outS, hb, hmt], fun y hy => ?_⟩
      obtain ⟨q, rfl⟩ := walkZ_iff.1 hy
      have := dsrc_single_le hE (lenX n w φ) (-φ s).toNat q
      rw [← hm v, hmt] at this
      simp at this
    · right
      have hne : dsrc N.G.Adj (lenTop (restrictLen (zArc N.G.Adj w) (lenX n w φ)))
          (offTop (single s (-φ s).toNat)) v ≠ ⊤ := by
        rw [← hm v]
        simpa using hmt
      obtain ⟨p, hp, hmin⟩ := dsrc_single_spec hE (lenX n w φ) (-φ s).toNat hne
      have hX : ∀ {a b : V} (q : Walk (zArc N.G.Adj w) a b),
          (q.nwt (lenX n w φ) : ℤ) = q.zw (xw n w) + φ a - φ b := fun q => by
        rw [show lenX n w φ = fun a b => (yr (xw n w) φ a b).toNat from rfl, Walk.nwt_toNat hpos q,
          zw_yr]
      have hmv : ((m v).toNat : ℤ) = -φ s + p.zw (xw n w) + φ s - φ v := by
        have h₁ : (m v : ℝ≥0∞) = (((-φ s).toNat + p.nwt (lenX n w φ) : ℕ) : ℝ≥0∞) := (hm v).trans hp
        have h₂ : m v = (((-φ s).toNat + p.nwt (lenX n w φ) : ℕ) : ℕ∞) := by
          rw [← ENat.toENNReal_coe] at h₁
          exact ENat.toENNReal_inj.1 h₁
        rw [h₂, ENat.toNat_natCast]
        push_cast
        rw [Int.toNat_of_nonneg (by omega), hX p]
        ring
      refine ⟨(((m v).toNat : ℤ) + φ v) / (2 * ((n : ℤ) + 1)), by simp [outS, hb, hmt], ?_⟩
      have hval : ((m v).toNat : ℤ) + φ v = p.zw (xw n w) := by rw [hmv]; ring
      rw [hval]
      refine least_of_xw hcard hneg p fun q => ?_
      have h₁ := hmin q
      have h₂ := hX p
      have h₃ := hX q
      have h₄ : (p.nwt (lenX n w φ) : ℤ) ≤ q.nwt (lenX n w φ) := by exact_mod_cast h₁
      linarith

end Output

end Congest

end SsspFlow
