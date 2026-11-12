import SsspFlow.SmoothStep
import SsspFlow.AggFinal

/-!
# Smoothing in the message model

`smoothingBox` proves `SmoothingBox` by the algorithm of [3, Alg. 3 and 4] in natural numbers
(`SmoothStep`), with `t = K log n + 3` steps of two oracle calls each.

* `dsrc_eq_ndsrc`: the distance from the virtual source in the contract of the oracle is the natural
  distance along the finite arcs (`adjT`, `lenN`).
* `first_spec`, `level_spec`: the answers of the oracle on the first network and on a level graph,
  in natural numbers.
* `dG`: the estimates of the steps, from the answers of the oracle. `dG_inv` gives their smoothness.
* `progS`: the program of a node on the machine of `Machine.lean`. `dM_eq` says that the memory of a
  node holds the estimates `dG`.
* `smoothAlg`: the algorithm, `3 t + 1` phases of `T + 1` rounds with messages of `B + C log n` bits.
  `smooth_run` gives the three bounds of `SmoothingBox`, and `smooth_nums` the numbers.

With `smoothingBox` and `aggBox`, exact shortest paths follow from the realization of metrics,
distance labels and the names of the faces, and negative weights and maximum flow also from the
decomposition.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal
open Cslib.Congest Cslib.Congest.Algorithm

namespace SsspFlow.Congest

/-! ### Distances in natural numbers -/

section Bridge

variable {V : Type} {adj : V → V → Prop}

/-- The finite arcs. -/
def adjT (adj : V → V → Prop) (ℓ : V → V → ℕ∞) (a b : V) : Prop := adj a b ∧ ℓ a b ≠ ⊤

/-- The lengths of the arcs as natural numbers. -/
def lenN (ℓ : V → V → ℕ∞) (a b : V) : ℕ := (ℓ a b).toNat

theorem lenTop_of_ne {ℓ : V → V → ℕ∞} {a b : V} (h : ℓ a b ≠ ⊤) :
    lenTop ℓ a b = (lenN ℓ a b : ℝ≥0∞) := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 h
  simp [lenTop, lenN, ← hm]

theorem wt_or (ℓ : V → V → ℕ∞) : ∀ {a b : V} (p : Walk adj a b),
    p.wt (lenTop ℓ) = ⊤ ∨ ∃ q : Walk (adjT adj ℓ) a b, p.wt (lenTop ℓ) = (q.nwt (lenN ℓ) : ℝ≥0∞)
  | _, _, .nil a => .inr ⟨.nil a, by simp⟩
  | _, _, @Walk.cons _ _ a m _ e p => by
    rcases wt_or ℓ p with h | ⟨q, hq⟩
    · left
      simp [h]
    · by_cases hℓ : ℓ a m = ⊤
      · left
        simp [lenTop, hℓ]
      · right
        refine ⟨.cons (show adjT adj ℓ a m from ⟨e, hℓ⟩) q, ?_⟩
        show lenTop ℓ a m + p.wt (lenTop ℓ) = ((lenN ℓ a m + q.nwt (lenN ℓ) : ℕ) : ℝ≥0∞)
        rw [hq, lenTop_of_ne hℓ]
        push_cast
        rfl

theorem wt_liftT (ℓ : V → V → ℕ∞) : ∀ {a b : V} (q : Walk (adjT adj ℓ) a b),
    (q.lift fun _ _ h => h.1).wt (lenTop ℓ) = (q.nwt (lenN ℓ) : ℝ≥0∞)
  | _, _, .nil a => by simp [Walk.lift]
  | _, _, @Walk.cons _ _ a m _ e q => by
    show lenTop ℓ a m + (q.lift fun _ _ h => h.1).wt (lenTop ℓ) = ((lenN ℓ a m + q.nwt (lenN ℓ) : ℕ) : ℝ≥0∞)
    rw [wt_liftT ℓ q, lenTop_of_ne e.2]
    push_cast
    rfl

/-- **The distance from the virtual source in natural numbers.** -/
theorem dsrc_eq_ndsrc (ℓ : V → V → ℕ∞) (y : V → ℕ) (v : V) :
    dsrc adj (lenTop ℓ) (offTop fun a => (y a : ℕ∞)) v = (ndsrc (adjT adj ℓ) (lenN ℓ) y v : ℝ≥0∞) := by
  have hoff : ∀ a, offTop (fun a => (y a : ℕ∞)) a = (y a : ℝ≥0∞) := fun a => by simp [offTop]
  apply le_antisymm
  · obtain ⟨a, q, hq⟩ := ndsrc_spec (adjT adj ℓ) (lenN ℓ) y v
    refine (dsrc_le_walk _ _ (q.lift fun _ _ h => h.1)).trans_eq ?_
    rw [hoff, wt_liftT, hq]
    push_cast
    rfl
  · refine le_dsrc fun a p => ?_
    rcases wt_or ℓ p with h | ⟨q, hq⟩
    · rw [h, add_top]
      exact le_top
    · rw [hq, hoff, ← Nat.cast_add]
      exact Nat.cast_le.2 (ndsrc_le q)

theorem walk_congr {adj' : V → V → Prop} {x x' : V → V → ℕ}
    (h : ∀ a b, adj a b → adj' a b ∧ x a b = x' a b) :
    ∀ {a b : V} (p : Walk adj a b), ∃ q : Walk adj' a b, q.nwt x' = p.nwt x
  | _, _, .nil a => ⟨.nil a, rfl⟩
  | _, _, @Walk.cons _ _ a m _ e p => by
    obtain ⟨q, hq⟩ := walk_congr h p
    exact ⟨.cons (h a m e).1 q, by
      show x' a m + q.nwt x' = x a m + p.nwt x
      rw [hq, (h a m e).2]⟩

theorem ndsrc_congr {adj' : V → V → Prop} {x x' : V → V → ℕ} (h : ∀ a b, adj a b ↔ adj' a b)
    (hx : ∀ a b, adj a b → x a b = x' a b) (y : V → ℕ) (v : V) :
    ndsrc adj x y v = ndsrc adj' x' y v := by
  apply le_antisymm
  · obtain ⟨a, p, hp⟩ := ndsrc_spec adj' x' y v
    obtain ⟨q, hq⟩ := walk_congr (x := x') (x' := x)
      (fun a b e => ⟨(h a b).2 e, (hx a b ((h a b).2 e)).symm⟩) p
    rw [hp, ← hq]
    exact ndsrc_le q
  · obtain ⟨a, p, hp⟩ := ndsrc_spec adj x y v
    obtain ⟨q, hq⟩ := walk_congr (x := x) (x' := x') (fun a b e => ⟨(h a b).1 e, hx a b e⟩) p
    rw [hp, ← hq]
    exact ndsrc_le q

theorem ndsrc_mul (c : ℕ) (x : V → V → ℕ) (y : V → ℕ) (v : V) :
    ndsrc adj (fun a b => c * x a b) (fun a => c * y a) v = c * ndsrc adj x y v := by
  apply le_antisymm
  · obtain ⟨a, p, hp⟩ := ndsrc_spec adj x y v
    have := ndsrc_le (adj := adj) (x := fun a b => c * x a b) (y := fun a => c * y a) p
    rw [nwt_mul] at this
    rw [hp, Nat.mul_add]
    exact this
  · obtain ⟨a, p, hp⟩ := ndsrc_spec adj (fun a b => c * x a b) (fun a => c * y a) v
    rw [hp, nwt_mul, ← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (ndsrc_le p)

/-- **The bounds of an approximate answer in natural numbers.** -/
theorem oracle_nat {E : ℕ} (hE : 0 < E) {o : ℕ∞} {k : ℕ} (h1 : (k : ℝ≥0∞) ≤ (o : ℝ≥0∞))
    (h2 : (o : ℝ≥0∞) ≤ (1 + (E : ℝ≥0∞)⁻¹) * k) :
    k ≤ o.toNat ∧ E * o.toNat ≤ (E + 1) * k := by
  have hE0 : (E : ℝ≥0∞) ≠ 0 := by exact_mod_cast hE.ne'
  have hfin : (o : ℝ≥0∞) ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.inv_ne_top.2 hE0⟩)
      (ENNReal.natCast_ne_top k)) h2
  have ho : o ≠ ⊤ := fun h => hfin (by simp [h])
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 ho
  simp only [ENat.toENNReal_coe, ENat.toNat_natCast] at h1 h2 ⊢
  refine ⟨by exact_mod_cast h1, ?_⟩
  have h3 : (E : ℝ≥0∞) * m ≤ (E + 1) * k := by
    calc (E : ℝ≥0∞) * m ≤ E * ((1 + (E : ℝ≥0∞)⁻¹) * k) := by gcongr
      _ = (E + 1) * k := by
        rw [← mul_assoc, mul_add, mul_one, ENNReal.mul_inv_cancel hE0 (ENNReal.natCast_ne_top E)]
  exact_mod_cast h3

end Bridge

/-! ### The estimates of the steps -/

section Global

variable {n : ℕ} {σ : Type} {B : ℕ} (A : Algorithm (Fin n) (OracleIn (Fin n)) σ B)
  (outA : Fin n → σ → ℕ∞) (T : ℕ) (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞)

/-- The answer of the oracle at `v` on lengths `ℓ'` and offsets `φ'`, as a natural number. -/
noncomputable def oraAns (ℓ' : Fin n → Fin n → ℕ∞) (φ' : Fin n → ℕ∞) (v : Fin n) : ℕ :=
  (outA v (A.run N.G (N.oracleIn ℓ' φ') T v)).toNat

/-- The lengths of a level graph. -/
def lenH (d : Fin n → ℕ) (A' ω r : ℕ) (a b : Fin n) : ℕ∞ :=
  if lev ω r (d a) = lev ω r (d b) then (A' : ℕ∞) * ℓ a b else ⊤

/-- The offsets of a level graph. -/
def offH (d : Fin n → ℕ) (ω r : ℕ) (a : Fin n) : ℕ∞ := (frc ω r (d a) : ℕ∞)

/-- **The estimates of the steps.** -/
noncomputable def dG (t : ℕ) : ℕ → Fin n → ℕ
  | 0 => oraAns A outA T N (fun a b => ((4 * t : ℕ) : ℕ∞) * ℓ a b) (fun a => ((4 * t : ℕ) : ℕ∞) * φ a)
  | i + 1 => stepD (ωS t i) (hS t i) (dG t i)
      (oraAns A outA T N (lenH ℓ (dG t i) (4 * t + i + 1) (ωS t i) 0) (offH (dG t i) (ωS t i) 0))
      (oraAns A outA T N (lenH ℓ (dG t i) (4 * t + i + 1) (ωS t i) (hS t i))
        (offH (dG t i) (ωS t i) (hS t i)))

variable {A outA T N ℓ φ} {W W' E D : ℕ}

theorem enat_mul_ne_top {c : ℕ} (hc : c ≠ 0) {a : ℕ∞} : (c : ℕ∞) * a ≠ ⊤ ↔ a ≠ ⊤ := by
  constructor
  · intro h ha
    rw [ha, ENat.mul_top (by exact_mod_cast hc)] at h
    exact h rfl
  · intro ha
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 ha
    exact_mod_cast ENat.natCast_ne_top (c * m)

theorem toNat_mul (c : ℕ) (a : ℕ∞) : ((c : ℕ∞) * a).toNat = c * a.toNat := by
  simp [ENat.toNat_mul]

/-- Scaled lengths in `[1, W]` stay valid with the bound `c W`. -/
theorem valid_len {c : ℕ} (hc : 1 ≤ c) {a : ℕ∞} (h : a = ⊤ ∨ ((1 : ℕ∞) ≤ a ∧ a ≤ W)) :
    (c : ℕ∞) * a = ⊤ ∨ ((1 : ℕ∞) ≤ (c : ℕ∞) * a ∧ (c : ℕ∞) * a ≤ (c * W : ℕ)) := by
  rcases h with h | ⟨h1, h2⟩
  · left
    rw [h, ENat.mul_top (by exact_mod_cast (show c ≠ 0 by omega))]
  · right
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top W) h2)
    have hm1 : 1 ≤ m := by exact_mod_cast h1
    have hm2 : m ≤ W := by exact_mod_cast h2
    refine ⟨by exact_mod_cast (show 1 ≤ c * m by nlinarith), ?_⟩
    exact_mod_cast Nat.mul_le_mul_left c hm2

/-- **The first call** in natural numbers: `U` times the distance, up to the factor `1 + 1/E`. -/
theorem first_spec (hora : ApproxOracleOK n W' E D T A outA) (hP : N.toRot.Planar) (hD : N.DiamLE D)
    (hV : OracleValid N 1 W ℓ φ) (hφ : ∀ v, φ v ≠ ⊤) {U : ℕ} (hU : 1 ≤ U) (hUW : U * W ≤ W') (hE : 0 < E)
    (v : Fin n) :
    U * ndsrc (adjT N.G.Adj ℓ) (lenN ℓ) (fun a => (φ a).toNat) v ≤
        oraAns A outA T N (fun a b => (U : ℕ∞) * ℓ a b) (fun a => (U : ℕ∞) * φ a) v ∧
      E * oraAns A outA T N (fun a b => (U : ℕ∞) * ℓ a b) (fun a => (U : ℕ∞) * φ a) v ≤
        (E + 1) * (U * ndsrc (adjT N.G.Adj ℓ) (lenN ℓ) (fun a => (φ a).toNat) v) := by
  have hφ' : (fun a => (U : ℕ∞) * φ a) = fun a => ((U * (φ a).toNat : ℕ) : ℕ∞) := by
    funext a
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (hφ a)
    rw [← hm]
    push_cast
    rfl
  have hval : OracleValid N 1 W' (fun a b => (U : ℕ∞) * ℓ a b) (fun a => (U : ℕ∞) * φ a) := by
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · rcases valid_len hU (hV.1 a b hab) with h | ⟨h1, h2⟩
      · exact .inl h
      · exact .inr ⟨h1, h2.trans (by exact_mod_cast hUW)⟩
    · right
      rcases hV.2 a with h | h
      · exact absurd h (hφ a)
      · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (hφ a)
        show (U : ℕ∞) * φ a ≤ (W' : ℕ∞)
        rw [← hm] at h ⊢
        have : m ≤ W := by exact_mod_cast h
        exact_mod_cast (Nat.mul_le_mul_left U this).trans hUW
  obtain ⟨h1, h2⟩ := hora N _ _ hP hD hval v
  have hd : N.dsrcTop (fun a b => (U : ℕ∞) * ℓ a b) (fun a => (U : ℕ∞) * φ a) v =
      ((U * ndsrc (adjT N.G.Adj ℓ) (lenN ℓ) (fun a => (φ a).toNat) v : ℕ) : ℝ≥0∞) := by
    unfold Net.dsrcTop
    rw [hφ', dsrc_eq_ndsrc, ← ndsrc_mul]
    congr 1
    refine ndsrc_congr (fun a b => ?_) (fun a b _ => ?_) _ v
    · exact and_congr_right fun _ => enat_mul_ne_top (by omega)
    · exact toNat_mul U (ℓ a b)
  rw [hd] at h1 h2
  exact oracle_nat hE h1 h2

/-- **A call on a level graph** in natural numbers. -/
theorem level_spec (hora : ApproxOracleOK n W' E D T A outA) (hP : N.toRot.Planar) (hD : N.DiamLE D)
    (hV : OracleValid N 1 W ℓ φ) (d : Fin n → ℕ) {A' ω : ℕ} (r : ℕ) (hA : 1 ≤ A') (hAW : A' * W ≤ W')
    (hω : 0 < ω) (hωW : ω ≤ W') (hE : 0 < E) (v : Fin n) :
    ndsrc (adjL (adjT N.G.Adj ℓ) d ω r) (fun a b => A' * lenN ℓ a b) (fun a => frc ω r (d a)) v ≤
        oraAns A outA T N (lenH ℓ d A' ω r) (offH d ω r) v ∧
      E * oraAns A outA T N (lenH ℓ d A' ω r) (offH d ω r) v ≤
        (E + 1) * ndsrc (adjL (adjT N.G.Adj ℓ) d ω r) (fun a b => A' * lenN ℓ a b)
          (fun a => frc ω r (d a)) v := by
  have hval : OracleValid N 1 W' (lenH ℓ d A' ω r) (offH d ω r) := by
    refine ⟨fun a b hab => ?_, fun a => .inr ?_⟩
    · unfold lenH
      split_ifs
      · rcases valid_len hA (hV.1 a b hab) with h | ⟨h1, h2⟩
        · exact .inl h
        · exact .inr ⟨h1, h2.trans (by exact_mod_cast hAW)⟩
      · exact .inl rfl
    · unfold offH frc
      exact_mod_cast ((Nat.mod_lt _ hω).le.trans hωW)
  obtain ⟨h1, h2⟩ := hora N _ _ hP hD hval v
  have hd : N.dsrcTop (lenH ℓ d A' ω r) (offH d ω r) v =
      (ndsrc (adjL (adjT N.G.Adj ℓ) d ω r) (fun a b => A' * lenN ℓ a b) (fun a => frc ω r (d a)) v :
        ℝ≥0∞) := by
    unfold Net.dsrcTop offH
    rw [dsrc_eq_ndsrc]
    congr 1
    refine ndsrc_congr (fun a b => ?_) (fun a b hab => ?_) _ v
    · unfold adjT adjL lenH
      by_cases hl : lev ω r (d a) = lev ω r (d b)
      · simp only [hl, ite_true, and_true]
        exact and_congr_right fun _ => enat_mul_ne_top (by omega)
      · simp [hl]
    · unfold lenN lenH
      have hl : lev ω r (d a) = lev ω r (d b) := by
        by_contra hl
        exact hab.2 (by simp [lenH, hl])
      rw [ite_eq_left hl, toNat_mul]
  rw [hd] at h1 h2
  exact oracle_nat hE h1 h2

end Global

section Inv

variable {n : ℕ} {σ : Type} {B : ℕ} {A : Algorithm (Fin n) (OracleIn (Fin n)) σ B}
  {outA : Fin n → σ → ℕ∞} {T : ℕ} {N : Net (Fin n)} {ℓ : Fin n → Fin n → ℕ∞} {φ : Fin n → ℕ∞}
  {W W' E D t : ℕ}

theorem toNat_le_of_valid (hV : OracleValid N 1 W ℓ φ) (hφ : ∀ v, φ v ≠ ⊤) (v : Fin n) :
    (φ v).toNat ≤ W := by
  rcases hV.2 v with h | h
  · exact absurd h (hφ v)
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (hφ v)
    rw [← hm] at h ⊢
    simpa using h

theorem ωS_le (t i : ℕ) : ωS t i ≤ ωS t 0 := by
  unfold ωS hS δS
  have : 2 ^ (t - i) ≤ 2 ^ (t - 0) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have := Nat.mul_le_mul_left t this
  have := Nat.mul_le_mul_left (5 * t + 3) this
  omega

/-- **The estimates of the steps** start at most `8 t` times the offsets, stay smooth, do not fall
below `4 t` times the distance and do not grow. -/
theorem dG_inv (hora : ApproxOracleOK n W' E D T A outA) (hP : N.toRot.Planar) (hD : N.DiamLE D)
    (hV : OracleValid N 1 W ℓ φ) (hφ : ∀ v, φ v ≠ ⊤) (ht : 0 < t) (hE : 30 * t + 14 ≤ E)
    (hW1 : 5 * t * W ≤ W') (hW2 : ωS t 0 ≤ W') (hW3 : 8 * W ≤ 2 ^ t) :
    (∀ v, dG A outA T N ℓ φ t 0 v ≤ 8 * t * (φ v).toNat) ∧
    ∀ i, i ≤ t → Smooth (adjT N.G.Adj ℓ) (lenN ℓ) (dG A outA T N ℓ φ t i) (4 * t + i) (δS t i) ∧
      (∀ v, 4 * t * ndsrc (adjT N.G.Adj ℓ) (lenN ℓ) (fun a => (φ a).toNat) v ≤
        dG A outA T N ℓ φ t i v) ∧
      ∀ v, dG A outA T N ℓ φ t i v ≤ dG A outA T N ℓ φ t 0 v := by
  have hE0 : 0 < E := by omega
  have hUW : 4 * t * W ≤ W' := le_trans (Nat.mul_le_mul_right _ (by omega)) hW1
  have hfirst := fun v => first_spec (A := A) (outA := outA) (T := T) hora hP hD hV hφ (U := 4 * t)
    (by omega) hUW hE0 v
  have h0 : ∀ v, dG A outA T N ℓ φ t 0 v ≤ 8 * t * (φ v).toNat := fun v => by
    obtain ⟨-, h2⟩ := hfirst v
    have h3 := ndsrc_le_off (adj := adjT N.G.Adj ℓ) (x := lenN ℓ) (y := fun a => (φ a).toNat) v
    have key : ∀ X : ℕ, (E + 1) * X ≤ E * (2 * X) := fun X =>
      calc (E + 1) * X ≤ (2 * E) * X := Nat.mul_le_mul_right X (by omega)
        _ = E * (2 * X) := by ring
    have h4 : E * dG A outA T N ℓ φ t 0 v ≤
        E * (2 * (4 * t * ndsrc (adjT N.G.Adj ℓ) (lenN ℓ) (fun a => (φ a).toNat) v)) :=
      h2.trans (key _)
    have h5 := Nat.le_of_mul_le_mul_left h4 hE0
    have h6 := Nat.mul_le_mul_left (8 * t) h3
    linarith
  refine ⟨h0, ?_⟩
  refine iter_inv (adj := adjT N.G.Adj ℓ) (x := lenN ℓ) ht hE (fun a => (φ a).toNat)
    (d := dG A outA T N ℓ φ t)
    (e₀ := fun i => oraAns A outA T N (lenH ℓ (dG A outA T N ℓ φ t i) (4 * t + i + 1) (ωS t i) 0)
      (offH (dG A outA T N ℓ φ t i) (ωS t i) 0))
    (e₁ := fun i => oraAns A outA T N (lenH ℓ (dG A outA T N ℓ φ t i) (4 * t + i + 1) (ωS t i) (hS t i))
      (offH (dG A outA T N ℓ φ t i) (ωS t i) (hS t i)))
    (fun i => rfl) (fun i hi => ?_) ?_ (fun v => (hfirst v).1)
  · have hA : (4 * t + i + 1) * W ≤ W' := le_trans (Nat.mul_le_mul_right _ (by omega)) hW1
    have hω : 0 < ωS t i := by
      unfold ωS hS
      have := δS_pos ht i
      positivity
    have hωW : ωS t i ≤ W' := (ωS_le t i).trans hW2
    exact ⟨fun v => (level_spec hora hP hD hV _ 0 (by omega) hA hω hωW hE0 v).1,
      fun v => (level_spec hora hP hD hV _ 0 (by omega) hA hω hωW hE0 v).2,
      fun v => (level_spec hora hP hD hV _ (hS t i) (by omega) hA hω hωW hE0 v).1,
      fun v => (level_spec hora hP hD hV _ (hS t i) (by omega) hA hω hωW hE0 v).2⟩
  · refine smooth_of_le (M := 8 * t * W) (4 * t)
      (fun v => (h0 v).trans (Nat.mul_le_mul_left _ (toNat_le_of_valid hV hφ v))) ?_
    unfold δS
    rw [Nat.sub_zero]
    nlinarith

end Inv

/-! ### The program -/

section Prog

variable {n : ℕ}

/-- The lengths that a node reads from its input: those of its arcs, `⊤` elsewhere. -/
def lenLoc (v : Fin n) (x : OracleIn (Fin n)) (a b : Fin n) : ℕ∞ :=
  if a = v then x.lenOut b else if b = v then x.lenIn a else ⊤

theorem lenLoc_out (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞) {v u : Fin n}
    (h : N.G.Adj v u) : lenLoc v (N.oracleIn ℓ φ v) v u = ℓ v u := by
  simp [lenLoc, Net.oracleIn, h]

theorem lenLoc_in (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞) {v u : Fin n}
    (h : N.G.Adj v u) : lenLoc v (N.oracleIn ℓ φ v) u v = ℓ u v := by
  have hne : u ≠ v := (N.G.ne_of_adj h).symm
  simp [lenLoc, Net.oracleIn, hne, h]

/-- The estimate of step `i` from the memory. -/
noncomputable def dM (t : ℕ) (m : Mem) : ℕ → ℕ
  | 0 => (decE (m 0 0)).toNat
  | i + 1 => min (dM t m i) (min (candS (ωS t i) 0 (dM t m i) (decE (m (3 * i + 2) 0)).toNat)
      (candS (ωS t i) (hS t i) (dM t m i) (decE (m (3 * i + 3) 0)).toNat))

/-- The estimates of step `i` at a node and its neighbours, as the node stores them. -/
noncomputable def valM (t : ℕ) (v : Fin n) (m : Mem) (i : ℕ) (u : Fin n) : ℕ :=
  if u = v then dM t m i else m (3 * i + 1) (u + 1)

/-- The input of the oracle at a node in step `i` with the shift `r`. -/
noncomputable def oraS (t : ℕ) (v : Fin n) (x : OracleIn (Fin n)) (m : Mem) (i r : ℕ) :
    OracleIn (Fin n) :=
  mkOra x.nbrs v (fun a b => if lev (ωS t i) r (valM t v m i a) = lev (ωS t i) r (valM t v m i b) then
      ((4 * t + i + 1 : ℕ) : ℕ∞) * lenLoc v x a b else ⊤) (frc (ωS t i) r (dM t m i) : ℕ∞)

/-- **The program of a node.** Phase `0` calls the oracle on the scaled network, and step `i` takes
three phases: an exchange of the estimates and one call on each level graph. -/
noncomputable def progS (t k : ℕ) (v : Fin n) (x : OracleIn (Fin n)) (m : Mem) :
    OracleIn (Fin n) ⊕ RelaxIn (Fin n) ⊕ OracleIn (Fin n) :=
  if k = 0 then
    .inl (mkOra x.nbrs v (fun a b => ((4 * t : ℕ) : ℕ∞) * lenLoc v x a b) (((4 * t : ℕ) : ℕ∞) * x.offset))
  else if (k - 1) % 3 = 0 then
    .inr (.inl (passIn (dM t m ((k - 1) / 3)) (fun y _ => y) (fun _ => dM t m ((k - 1) / 3))))
  else if (k - 1) % 3 = 1 then .inl (oraS t v x m ((k - 1) / 3) 0)
  else .inl (oraS t v x m ((k - 1) / 3) (hS t ((k - 1) / 3)))

variable (t : ℕ) (v : Fin n) (x : OracleIn (Fin n)) (m : Mem)

theorem progS_zero : progS t 0 v x m =
    .inl (mkOra x.nbrs v (fun a b => ((4 * t : ℕ) : ℕ∞) * lenLoc v x a b) (((4 * t : ℕ) : ℕ∞) * x.offset)) := by
  unfold progS
  rw [ite_eq_left rfl]

theorem progS_ex (i : ℕ) : progS t (3 * i + 1) v x m =
    .inr (.inl (passIn (dM t m i) (fun y _ => y) (fun _ => dM t m i))) := by
  unfold progS
  rw [ite_eq_right (by omega), ite_eq_left (by omega), show (3 * i + 1 - 1) / 3 = i by omega]

theorem progS_o0 (i : ℕ) : progS t (3 * i + 2) v x m = .inl (oraS t v x m i 0) := by
  unfold progS
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
    show (3 * i + 2 - 1) / 3 = i by omega]

theorem progS_o1 (i : ℕ) : progS t (3 * i + 3) v x m = .inl (oraS t v x m i (hS t i)) := by
  unfold progS
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
    show (3 * i + 3 - 1) / 3 = i by omega]

end Prog

/-! ### The run -/

section Run

theorem dM_succ (t : ℕ) (m : Mem) (i : ℕ) : dM t m (i + 1) = min (dM t m i)
    (min (candS (ωS t i) 0 (dM t m i) (decE (m (3 * i + 2) 0)).toNat)
      (candS (ωS t i) (hS t i) (dM t m i) (decE (m (3 * i + 3) 0)).toNat)) := rfl

/-- The estimate of step `i` reads only the entries before `3 i + 1`. -/
theorem dM_congr (t : ℕ) {m m' : Mem} : ∀ i, (∀ j, j ≤ 3 * i → m j = m' j) → dM t m i = dM t m' i
  | 0, h => by
    show (decE (m 0 0)).toNat = (decE (m' 0 0)).toNat
    rw [h 0 (by omega)]
  | i + 1, h => by
    rw [dM_succ, dM_succ, dM_congr t i fun j hj => h j (by omega), h (3 * i + 2) (by omega),
      h (3 * i + 3) (by omega)]

variable {n : ℕ} {σ : Type} {B B' : ℕ} (A : Algorithm (Fin n) (OracleIn (Fin n)) σ B) (hB : B ≤ B')
  (outA : Fin n → σ → ℕ∞) (T t : ℕ) (N : Net (Fin n)) (ℓ : Fin n → Fin n → ℕ∞) (φ : Fin n → ℕ∞)

/-- **The algorithm of the nodes**: `3 t + 1` phases of `T + 1` rounds on the machine. -/
noncomputable def smoothAlg :=
  ((mach (A.widen hB) (A.widen hB) T 1 T (T + 1) (progS t) (resO outA) (resO outA)).stopAt
    ((3 * t + 1) * (T + 1))).premap fun _ (i : OracleIn (Fin n)) =>
      ((i, 0, fun _ _ => 0) : OracleIn (Fin n) × ℕ × Mem)

/-- The memory of a node after `k` phases. -/
noncomputable def memS (k : ℕ) (v : Fin n) : Mem :=
  memAt (A.widen hB) (A.widen hB) T 1 T (T + 1) (progS t) (resO outA) (resO outA) N.G
    (fun u => N.oracleIn ℓ φ u) k v

theorem run_smoothAlg {R : ℕ} (hR : (3 * t + 1) * (T + 1) ≤ R) (v : Fin n) :
    ((smoothAlg A hB outA T t).run N.G (N.oracleIn ℓ φ) R v).2.1.2.2 =
      memS A hB outA T t N ℓ φ (3 * t + 1) v := by
  unfold smoothAlg
  rw [run_premap, run_stopAt, min_eq_right hR]
  exact run_mach (A.widen hB) (A.widen hB) T 1 T (T + 1) (progS t) (resO outA) (resO outA) N.G
    (fun u => N.oracleIn ℓ φ u) (by omega) (3 * t + 1) v

theorem memS_stable {j k : ℕ} (h : j < k) (v : Fin n) :
    memS A hB outA T t N ℓ φ k v j = memS A hB outA T t N ℓ φ (j + 1) v j :=
  mem_stable (A.widen hB) (A.widen hB) T 1 T (T + 1) (progS t) (resO outA) (resO outA) N.G
    (fun u => N.oracleIn ℓ φ u) h v

theorem memS_ora {k : ℕ} (ia : Fin n → OracleIn (Fin n))
    (h : ∀ w, progS t k w (N.oracleIn ℓ φ w) (memS A hB outA T t N ℓ φ k w) = .inl (ia w))
    (v : Fin n) : memS A hB outA T t N ℓ φ (k + 1) v k 0 = encE (outA v (A.run N.G ia T v)) := by
  have e := congrFun (mem_agg (A.widen hB) (A.widen hB) T 1 T (T + 1) (progS t) (resO outA)
    (resO outA) N.G (fun u => N.oracleIn ℓ φ u) ia h (by omega) v) 0
  rw [run_widen] at e
  exact e

theorem memS_relax {k : ℕ} (ir : Fin n → RelaxIn (Fin n))
    (h : ∀ w, progS t k w (N.oracleIn ℓ φ w) (memS A hB outA T t N ℓ φ k w) = .inr (.inl (ir w)))
    (v : Fin n) : memS A hB outA T t N ℓ φ (k + 1) v k = relaxSt B' N.G ir 1 v :=
  mem_relax (A.widen hB) (A.widen hB) T 1 T (T + 1) (progS t) (resO outA) (resO outA) N.G
    (fun u => N.oracleIn ℓ φ u) ir h (by omega) v

theorem progS_first (w : Fin n) (m : Mem) : progS t 0 w (N.oracleIn ℓ φ w) m =
    .inl (N.oracleIn (fun a b => ((4 * t : ℕ) : ℕ∞) * ℓ a b) (fun a => ((4 * t : ℕ) : ℕ∞) * φ a) w) := by
  rw [progS_zero]
  congr 1
  exact mkOra_eq N (fun u hu => ⟨by simp only [lenLoc_out N ℓ φ hu], by simp only [lenLoc_in N ℓ φ hu]⟩)
    rfl

/-- **The call on a level graph** that a node makes, from its estimate and those of its
neighbours. -/
theorem oraS_eq (i r : ℕ) (d : Fin n → ℕ) {w : Fin n} {m : Mem} (h0 : dM t m i = d w)
    (h1 : ∀ u, N.G.Adj w u → m (3 * i + 1) (u + 1) = d u) :
    oraS t w (N.oracleIn ℓ φ w) m i r =
      N.oracleIn (lenH ℓ d (4 * t + i + 1) (ωS t i) r) (offH d (ωS t i) r) w := by
  have hv : valM t w m i w = d w := by
    unfold valM
    rw [ite_eq_left rfl, h0]
  have hu : ∀ u, N.G.Adj w u → valM t w m i u = d u := fun u hu => by
    unfold valM
    rw [ite_eq_right (N.G.ne_of_adj hu).symm, h1 u hu]
  unfold oraS
  refine mkOra_eq N (fun u hu' => ⟨?_, ?_⟩) ?_
  · simp only [hv, hu u hu', lenLoc_out N ℓ φ hu', lenH]
  · simp only [hv, hu u hu', lenLoc_in N ℓ φ hu', lenH]
  · simp only [offH, h0]

/-- **The memory holds the estimates.** From phase `3 i + 1` on, a node reads the estimate of step
`i` from its memory, if the estimates fit into the messages. -/
theorem dM_eq (hx : ∀ i, i < t → ∀ u, dG A outA T N ℓ φ t i u < 2 ^ B') :
    ∀ i, i ≤ t → ∀ k, 3 * i + 1 ≤ k → ∀ v,
      dM t (memS A hB outA T t N ℓ φ k v) i = dG A outA T N ℓ φ t i v := by
  intro i
  induction i with
  | zero =>
    intro _ k hk v
    have e := memS_ora A hB outA T t N ℓ φ (k := 0) _ (fun w => progS_first t N ℓ φ w _) v
    show (decE (memS A hB outA T t N ℓ φ k v 0 0)).toNat = _
    rw [memS_stable A hB outA T t N ℓ φ (show 0 < k by omega), e, decE_encE]
    rfl
  | succ i ih =>
    intro hi k hk v
    have hd : ∀ k, 3 * i + 1 ≤ k → ∀ w,
        dM t (memS A hB outA T t N ℓ φ k w) i = dG A outA T N ℓ φ t i w := ih (by omega)
    have hex : ∀ w, memS A hB outA T t N ℓ φ (3 * i + 1 + 1) w (3 * i + 1) =
        relaxSt B' N.G (fun w => passIn (dG A outA T N ℓ φ t i w) (fun y _ => y)
          (fun _ => dG A outA T N ℓ φ t i w)) 1 w :=
      memS_relax A hB outA T t N ℓ φ (k := 3 * i + 1) _ fun w => by
        rw [progS_ex, hd (3 * i + 1) le_rfl w]
    have hnb : ∀ k, 3 * i + 2 ≤ k → ∀ w u, N.G.Adj w u →
        memS A hB outA T t N ℓ φ k w (3 * i + 1) (u + 1) = dG A outA T N ℓ φ t i u := by
      intro k hk w u hu
      rw [memS_stable A hB outA T t N ℓ φ (show 3 * i + 1 < k by omega), hex]
      exact (exch_one N.G _ (hx i (by omega)) w).2 u hu.symm
    have h0 := memS_ora A hB outA T t N ℓ φ (k := 3 * i + 2)
      (N.oracleIn (lenH ℓ (dG A outA T N ℓ φ t i) (4 * t + i + 1) (ωS t i) 0)
        (offH (dG A outA T N ℓ φ t i) (ωS t i) 0))
      (fun w => by rw [progS_o0, oraS_eq t N ℓ φ i 0 _ (hd (3 * i + 2) (by omega) w)
        (hnb (3 * i + 2) le_rfl w)]) v
    have h1 := memS_ora A hB outA T t N ℓ φ (k := 3 * i + 3)
      (N.oracleIn (lenH ℓ (dG A outA T N ℓ φ t i) (4 * t + i + 1) (ωS t i) (hS t i))
        (offH (dG A outA T N ℓ φ t i) (ωS t i) (hS t i)))
      (fun w => by rw [progS_o1, oraS_eq t N ℓ φ i (hS t i) _ (hd (3 * i + 3) (by omega) w)
        (hnb (3 * i + 3) (by omega) w)]) v
    rw [dM_succ, hd k (by omega) v, memS_stable A hB outA T t N ℓ φ (show 3 * i + 2 < k by omega),
      memS_stable A hB outA T t N ℓ φ (show 3 * i + 3 < k by omega), h0, h1, decE_encE, decE_encE]
    rfl

/-- **The bounds of the smoothing** after at least `(3 t + 1)(T + 1)` rounds. -/
theorem smooth_run {W W' E D R : ℕ} (hora : ApproxOracleOK n W' E D T A outA) (hP : N.toRot.Planar)
    (hD : N.DiamLE D) (hV : OracleValid N 1 W ℓ φ) (hφ : ∀ v, φ v ≠ ⊤) (ht : 0 < t)
    (hE : 30 * t + 14 ≤ E) (hW1 : 5 * t * W ≤ W') (hW2 : ωS t 0 ≤ W') (hW3 : 8 * W ≤ 2 ^ t)
    (hW4 : 8 * t * W < 2 ^ B') (hR : (3 * t + 1) * (T + 1) ≤ R) :
    let d := fun v => outR t (dM t ((smoothAlg A hB outA T t).run N.G (N.oracleIn ℓ φ) R v).2.1.2.2 t)
    (∀ v, 2 * N.dsrcTop ℓ φ v ≤ (d v : ℝ≥0∞)) ∧
      (∀ a b, N.G.Adj a b → (d b : ℕ∞) ≤ d a + 4 * ℓ a b) ∧ ∀ v, (d v : ℕ∞) ≤ 4 * φ v := by
  intro d
  obtain ⟨h0, hinv⟩ := dG_inv hora hP hD hV hφ ht hE hW1 hW2 hW3
  obtain ⟨hs, hnd, hle⟩ := hinv t le_rfl
  have hx : ∀ i, i < t → ∀ u, dG A outA T N ℓ φ t i u < 2 ^ B' := fun i hi u =>
    (((hinv i hi.le).2.2 u).trans ((h0 u).trans
      (Nat.mul_le_mul_left _ (toNat_le_of_valid hV hφ u)))).trans_lt hW4
  have hd : ∀ v, d v = outR t (dG A outA T N ℓ φ t t v) := fun v => by
    show outR t (dM t ((smoothAlg A hB outA T t).run N.G (N.oracleIn ℓ φ) R v).2.1.2.2 t) = _
    rw [run_smoothAlg A hB outA T t N ℓ φ hR v, dM_eq A hB outA T t N ℓ φ hx t le_rfl _ le_rfl v]
  have hφe : ∀ a, φ a = ((φ a).toNat : ℕ∞) := fun a => (ENat.natCast_toNat (hφ a)).symm
  refine ⟨fun v => ?_, fun a b hab => ?_, fun v => ?_⟩
  · have hoff : offTop φ = offTop fun a => (((φ a).toNat : ℕ) : ℕ∞) := by
      funext a
      simp only [offTop, ENat.natCast_toNat (hφ a)]
    have e : N.dsrcTop ℓ φ v =
        (ndsrc (adjT N.G.Adj ℓ) (lenN ℓ) (fun a => (φ a).toNat) v : ℝ≥0∞) := by
      unfold Net.dsrcTop
      rw [hoff, dsrc_eq_ndsrc]
    rw [hd v, e]
    exact_mod_cast out_lo ht (fun a => (φ a).toNat) hnd v
  · rw [hd a, hd b]
    by_cases hℓ : ℓ a b = ⊤
    · rw [hℓ, ENat.mul_top (show (4 : ℕ∞) ≠ 0 by norm_num), add_top]
      exact le_top
    · have hs' : Smooth (adjT N.G.Adj ℓ) (lenN ℓ) (dG A outA T N ℓ φ t t) (5 * t) t := by
        have e1 : 4 * t + t = 5 * t := by ring
        have e2 : δS t t = t := by simp [δS]
        rw [e1, e2] at hs
        exact @hs
      have hx1 : 1 ≤ lenN ℓ a b := by
        rcases hV.1 a b hab with h | ⟨h1, -⟩
        · exact absurd h hℓ
        · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hℓ
          unfold lenN
          rw [← hm] at h1 ⊢
          simpa using h1
      have h := out_arc ht hs' (show adjT N.G.Adj ℓ a b from ⟨hab, hℓ⟩) hx1
      rw [show ℓ a b = ((lenN ℓ a b : ℕ) : ℕ∞) from (ENat.natCast_toNat hℓ).symm]
      exact_mod_cast h
  · rw [hd v, hφe v]
    exact_mod_cast out_off ht ((hle v).trans (h0 v))

end Run

/-! ### The numbers and the end results -/

/-- The numbers of the smoothing for the exponent `K` of the weights, with `X = n + 2` and
`L = logN n`. -/
theorem smooth_nums {K L t X : ℕ} (hL1 : 1 ≤ L) (hX : 2 ≤ X) (hP : X < 2 ^ L) (hQ : 2 ^ L ≤ 2 * X)
    (hLX : L ≤ X) (ht : t = K * L + 3) :
    30 * t + 14 ≤ (30 * K + 104) * L ∧ 5 * t * X ^ K ≤ X ^ (30 * K + 104) ∧
      ωS t 0 ≤ X ^ (30 * K + 104) ∧ 8 * X ^ K ≤ 2 ^ t ∧
      8 * t * X ^ K < 2 ^ ((30 * K + 104) * L) ∧
      ∀ T D : ℕ, (3 * t + 1) * (T + 1) ≤ (30 * K + 104) * L * (T + D + 1) := by
  subst ht
  have hKL := Nat.zero_le (K * L)
  have e1 : X ^ K ≤ 2 ^ (K * L) := by
    rw [mul_comm K L, pow_mul]
    exact Nat.pow_le_pow_left hP.le K
  have e2 : 2 ^ (K * L + 3) = 2 ^ (K * L) * 8 := by
    rw [pow_add]
    norm_num
  have h4 : 8 * X ^ K ≤ 2 ^ (K * L + 3) := by
    rw [e2]
    omega
  have h1 : 30 * (K * L + 3) + 14 ≤ (30 * K + 104) * L := by nlinarith
  have bt : K * L + 3 ≤ X ^ (K + 4) := by
    have a1 : K * L ≤ X ^ (K + 1) := pb_mul (pb_const hX K) (show L ≤ X ^ 1 by rw [pow_one]; exact hLX)
    have a2 : 3 ≤ X ^ 2 := (by norm_num : 3 ≤ 2 ^ 2).trans (Nat.pow_le_pow_left hX 2)
    exact pb_le hX (pb_add hX a1 a2) (by omega)
  have b5 : 5 * (K * L + 3) ≤ X ^ (K + 9) := pb_le hX (pb_mul (pb_const hX 5) bt) (by omega)
  have h2 : 5 * (K * L + 3) * X ^ K ≤ X ^ (30 * K + 104) :=
    pb_le hX (pb_mul b5 le_rfl) (by omega)
  have b2t : 2 ^ (K * L + 3) ≤ X ^ (2 * K + 3) := by
    have a1 : 2 ^ (K * L) ≤ X ^ (2 * K) :=
      calc 2 ^ (K * L) = (2 ^ L) ^ K := by rw [mul_comm K L, pow_mul]
        _ ≤ (2 * X) ^ K := Nat.pow_le_pow_left hQ K
        _ = 2 ^ K * X ^ K := mul_pow 2 X K
        _ ≤ X ^ K * X ^ K := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hX K)
        _ = X ^ (2 * K) := by ring
    have a2 : 8 ≤ X ^ 3 := (by norm_num : 8 ≤ 2 ^ 3).trans (Nat.pow_le_pow_left hX 3)
    rw [e2]
    calc 2 ^ (K * L) * 8 ≤ X ^ (2 * K) * X ^ 3 := Nat.mul_le_mul a1 a2
      _ = X ^ (2 * K + 3) := by rw [← pow_add]
  have h3 : ωS (K * L + 3) 0 ≤ X ^ (30 * K + 104) := by
    unfold ωS hS δS
    rw [Nat.sub_zero]
    have a1 : 5 * (K * L + 3) + 3 ≤ X ^ (K + 13) :=
      pb_le hX (pb_add hX b5 (pb_const hX 3)) (by omega)
    exact pb_le hX (pb_mul (pb_const hX 2) (pb_mul a1 (pb_mul bt b2t))) (by omega)
  have h5 : 8 * (K * L + 3) * X ^ K < 2 ^ ((30 * K + 104) * L) := by
    have a1 : K * L + 3 < 2 ^ (K * L + 3) := Nat.lt_two_pow_self
    have a3 : 8 * (K * L + 3) * X ^ K < 2 ^ (K * L + 3) * 2 ^ (K * L + 3) :=
      calc 8 * (K * L + 3) * X ^ K = (K * L + 3) * (8 * X ^ K) := by ring
        _ ≤ (K * L + 3) * 2 ^ (K * L + 3) := Nat.mul_le_mul_left _ h4
        _ < 2 ^ (K * L + 3) * 2 ^ (K * L + 3) := Nat.mul_lt_mul_of_pos_right a1 (by positivity)
    have a4 : 2 ^ (K * L + 3) * 2 ^ (K * L + 3) ≤ 2 ^ ((30 * K + 104) * L) := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    exact lt_of_lt_of_le a3 a4
  refine ⟨h1, h2, h3, h4, h5, fun T D => ?_⟩
  have a1 : 3 * (K * L + 3) + 1 ≤ (30 * K + 104) * L := by nlinarith
  exact Nat.mul_le_mul a1 (by omega)

/-- **The smoothing of [3]** in the message model, with `C = 30 K + 104` and `c = 1`. -/
theorem smoothingBox : SmoothingBox := by
  intro K
  refine ⟨30 * K + 104, 1, fun n D T B σ A outA hA => ?_⟩
  have hB : B ≤ B + (30 * K + 104) * logN n ^ 1 := Nat.le_add_right _ _
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := smooth_nums (K := K) (one_le_logN n) (show 2 ≤ n + 2 by omega)
    (lt_two_pow_logN n) (two_pow_logN_le n) (logN_le n) rfl
  refine ⟨_, smoothAlg A hB outA T (K * logN n + 3),
    fun v s => outR (K * logN n + 3) (dM (K * logN n + 3) s.2.1.2.2 (K * logN n + 3)), ?_⟩
  intro N ℓ φ hP hD hV hφ
  exact smooth_run A hB outA T (K * logN n + 3) N ℓ φ hA hP hD hV hφ (by omega) h1 h2 h3 h4
    (h5.trans_le (Nat.pow_le_pow_right (by norm_num) (by rw [pow_one]; exact Nat.le_add_left _ _)))
    (h6 T D)

/-- **Exact shortest paths** in `Õ(D)` rounds, from the realization of metrics, distance labels and
the names of the faces. -/
theorem exactSssp_of_cited {Cr Cl cl : ℕ} (hC : RealizationBox Cr) (hL : DistanceLabelBox Cl cl)
    (hF : FaceIdBox) : ExactSsspBound :=
  exactSssp_of_boxes hC hL hF aggBox smoothingBox

/-- **Negative weights and maximum flow** with the factor `(log n)^c`, from the same results and a
reduction with this factor. -/
theorem negFlow_polylog_of_cited (c : ℕ) {Cr Cl cl : ℕ} (hC : RealizationBox Cr)
    (hL : DistanceLabelBox Cl cl) (hF : FaceIdBox) (hR : NegReduction (tauPolylog c)) :
    NegSsspBound (tauPolylog c) ∧ MaxFlowBound (tauPolylog c) :=
  negFlow_polylog_of_boxes c hC hL hF aggBox smoothingBox hR

/-- **Negative weights and maximum flow** with the factor `(log n)^(C √log n)`, from the same
results and a reduction with this factor. -/
theorem negFlow_subpoly_of_cited (C : ℕ) {Cr Cl cl : ℕ} (hC : RealizationBox Cr)
    (hL : DistanceLabelBox Cl cl) (hF : FaceIdBox) (hR : NegReduction (tauSubpoly C)) :
    NegSsspBound (tauSubpoly C) ∧ MaxFlowBound (tauSubpoly (12 * C)) :=
  negFlow_subpoly_of_boxes C hC hL hF aggBox smoothingBox hR

/-- **Negative weights and maximum flow** with the factor `logᶜ n`, from the realization of
metrics, distance labels, the names of the faces and the decomposition. -/
theorem negFlow_of_cited {Cr Cl cl : ℕ} (hC : RealizationBox Cr) (hL : DistanceLabelBox Cl cl)
    (hF : FaceIdBox) (hD : LDDBox) :
    ∃ c, NegSsspBound (tauPolylog c) ∧ MaxFlowBound (tauPolylog c) :=
  negFlow_of_ldd hC hL hF aggBox smoothingBox hD

end SsspFlow.Congest
