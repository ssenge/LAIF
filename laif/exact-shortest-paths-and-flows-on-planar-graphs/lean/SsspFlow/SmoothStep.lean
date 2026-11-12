import SsspFlow.NegWalk

/-!
# Smoothing in natural numbers

An estimate `d` is `(A, δ)`-smooth for the lengths `x` if `d v ≤ d u + A |p| + δ` for every walk `p`
from `u` to `v` (`Smooth`). One step of the smoothing of [3, Alg. 4] cuts the values of `d` into levels
of width `ω = 2 h` at the shifts `0` and `h` (`lev`, `frc`), and reads two answers of an oracle on the
arcs inside one level, with lengths `(A + 1) x` and offsets `frc` (`adjL`). The new estimate `stepD` is
the least of `d v` and the two candidates (`candS`).

* `step_lo`: every new value is at least `d u + (A + 1) |p|` for some walk `p` from `u`.
* `step_hi`: every new value is at most `d u + (A + 1) |p| + δ / 2` for every walk `p` from `u`. A walk
  that would break this is short (`smoothing_walk`), so its values fit into one level of one of the
  two shifts (`fit`).
* `step_smooth`: so the new estimate is `(A + 1, δ / 2)`-smooth.
* `iter_inv`: `t` steps with `A = 4 t + i` and `δ = t 2^(t - i)` give a `(5 t, t)`-smooth estimate.
* `out_lo`, `out_arc`, `out_off`: rounded up in units of `2 t`, it does not fall below twice the
  distance, it grows by at most four times the length of an arc, and it is at most four times the offset.
-/

set_option autoImplicit false

namespace SsspFlow.Congest

section Smooth

variable {V : Type} (adj : V → V → Prop) (x : V → V → ℕ)

/-- `d` is `(A, δ)`-smooth. -/
def Smooth (d : V → ℕ) (A δ : ℕ) : Prop :=
  ∀ {u v : V} (p : Walk adj u v), d v ≤ d u + A * p.nwt x + δ

/-- The level of a value at the shift `r`. -/
def lev (ω r a : ℕ) : ℕ := (a + r) / ω

/-- The place of a value inside its level. -/
def frc (ω r a : ℕ) : ℕ := (a + r) % ω

/-- The arcs inside one level. -/
def adjL (d : V → ℕ) (ω r : ℕ) (a b : V) : Prop := adj a b ∧ lev ω r (d a) = lev ω r (d b)

/-- The candidate from an answer `e` of the oracle on the level graph. -/
def candS (ω r a e : ℕ) : ℕ := ω * lev ω r a + e - r

/-- The new estimate. -/
def stepD (ω h : ℕ) (d e₀ e₁ : V → ℕ) (v : V) : ℕ :=
  min (d v) (min (candS ω 0 (d v) (e₀ v)) (candS ω h (d v) (e₁ v)))

theorem lev_add_frc (ω r a : ℕ) : ω * lev ω r a + frc ω r a = a + r := Nat.div_add_mod (a + r) ω

variable {adj x}

theorem nwt_mul (c : ℕ) : ∀ {a b : V} (p : Walk adj a b), p.nwt (fun a b => c * x a b) = c * p.nwt x
  | _, _, .nil _ => by simp
  | _, _, .cons e p => by simp [nwt_mul c p, Nat.mul_add]

/-- A walk inside one level ends in the level where it starts. -/
theorem lev_walk {d : V → ℕ} {ω r : ℕ} : ∀ {a b : V}, Walk (adjL adj d ω r) a b →
    lev ω r (d a) = lev ω r (d b)
  | _, _, .nil _ => rfl
  | _, _, .cons e q => e.2.trans (lev_walk q)

/-- A walk whose vertices lie in one level is a walk inside the level. -/
theorem walkL {d : V → ℕ} {ω r c : ℕ} : ∀ {a b : V} (p : Walk adj a b),
    (∀ w ∈ p.support, lev ω r (d w) = c) → ∃ q : Walk (adjL adj d ω r) a b, q.nwt x = p.nwt x
  | _, _, .nil a, _ => ⟨.nil a, rfl⟩
  | _, _, @Walk.cons _ _ a m _ e p, h => by
    simp only [Walk.support_cons, List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨q, hq⟩ := walkL p h.2
    exact ⟨.cons ⟨e, h.1.trans (h.2 m p.start_mem).symm⟩ q, by
      show x a m + q.nwt x = x a m + p.nwt x
      rw [hq]⟩

/-- Cut a walk at a visited vertex. -/
theorem split_nwt {a b w : V} (p : Walk adj a b) (hw : w ∈ p.support) :
    ∃ (p₁ : Walk adj a w) (p₂ : Walk adj w b), p₁.nwt x + p₂.nwt x = p.nwt x := by
  induction p with
  | nil a =>
    obtain rfl : w = a := by simpa using hw
    exact ⟨.nil w, .nil w, rfl⟩
  | cons e p ih =>
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ⟨.nil w, .cons e p, by simp⟩
    · obtain ⟨p₁, p₂, h⟩ := ih hw
      exact ⟨.cons e p₁, p₂, by simp [← h, Nat.add_assoc]⟩

/-- The distance from the virtual source grows by at most the length of a walk. -/
theorem ndsrc_walk (y : V → ℕ) {u v : V} (p : Walk adj u v) :
    ndsrc adj x y v ≤ ndsrc adj x y u + p.nwt x := by
  obtain ⟨a, q, hq⟩ := ndsrc_spec adj x y u
  have := ndsrc_le (x := x) (y := y) (q.append p)
  rw [Walk.nwt_append] at this
  omega

/-- An interval shorter than `h` lies in one level of width `2 h` at the shift `0` or `h`. -/
theorem fit {lo hi h : ℕ} (hh : 0 < h) (hlt : hi < lo + h) :
    (∀ y, lo ≤ y → y ≤ hi → y / (2 * h) = lo / (2 * h)) ∨
      ∀ y, lo ≤ y → y ≤ hi → (y + h) / (2 * h) = (lo + h) / (2 * h) := by
  by_cases hq : hi / (2 * h) = lo / (2 * h)
  · left
    intro y h1 h2
    exact le_antisymm (hq ▸ Nat.div_le_div_right h2) (Nat.div_le_div_right h1)
  by_cases hlh : hi < lo
  · left
    intro y h1 h2
    omega
  right
  have hω : 0 < 2 * h := by omega
  have hle : lo / (2 * h) < hi / (2 * h) :=
    lt_of_le_of_ne (Nat.div_le_div_right (by omega)) (Ne.symm hq)
  set q := hi / (2 * h) with hqdef
  have hm1 : lo < q * (2 * h) := by
    have h1 : lo < (lo / (2 * h) + 1) * (2 * h) := by
      rw [Nat.succ_mul]
      have := Nat.lt_div_mul_add (a := lo) hω
      omega
    exact lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ hle)
  have hm2 : q * (2 * h) ≤ hi := Nat.div_mul_le_self hi (2 * h)
  have key : ∀ y, lo ≤ y → y ≤ hi → (y + h) / (2 * h) = q := by
    intro y h1 h2
    refine Nat.div_eq_of_lt_le (by omega) ?_
    rw [Nat.succ_mul]
    omega
  intro y h1 h2
  rw [key y h1 h2, key lo le_rfl (by omega)]

/-- **A walk that breaks the bound is short**, and its values lie close to the value at its start. -/
theorem smoothing_walk {d : V → ℕ} {A δ : ℕ} (hs : Smooth adj x d A δ) {u v : V} (p : Walk adj u v)
    (hstr : d u + (A + 1) * p.nwt x < d v) :
    p.nwt x < δ ∧ ∀ w ∈ p.support, d u ≤ d w + δ ∧ d w ≤ d u + A * p.nwt x + δ := by
  have h1 := hs p
  rw [Nat.succ_mul] at hstr
  refine ⟨by omega, fun w hw => ?_⟩
  obtain ⟨p₁, p₂, hsum⟩ := split_nwt (x := x) p hw
  have h2 := hs p₁
  have h3 := hs p₂
  have h4 : A * p.nwt x = A * p₁.nwt x + A * p₂.nwt x := by rw [← hsum, Nat.mul_add]
  omega

variable {d : V → ℕ} {ω r A' : ℕ} {e : V → ℕ} {v : V}

/-- **The lower bound of a candidate.** -/
theorem candS_lo
    (hlo : ndsrc (adjL adj d ω r) (fun a b => A' * x a b) (fun a => frc ω r (d a)) v ≤ e v) :
    ∃ u, ∃ p : Walk adj u v, d u + A' * p.nwt x ≤ candS ω r (d v) (e v) := by
  obtain ⟨u, q, hq⟩ := ndsrc_spec (adjL adj d ω r) (fun a b => A' * x a b) (fun a => frc ω r (d a)) v
  refine ⟨u, q.lift fun _ _ h => h.1, ?_⟩
  rw [Walk.nwt_lift, ← nwt_mul, candS, ← lev_walk q]
  have := lev_add_frc ω r (d u)
  omega

/-- **The upper bound of a candidate** along a walk inside one level. -/
theorem candS_hi {E δ' : ℕ} (hE : 0 < E)
    (hhi : E * e v ≤ (E + 1) * ndsrc (adjL adj d ω r) (fun a b => A' * x a b) (fun a => frc ω r (d a)) v)
    {u : V} (p : Walk adj u v) (hp : ∀ w ∈ p.support, lev ω r (d w) = lev ω r (d u))
    (hX : frc ω r (d u) + A' * p.nwt x ≤ E * δ') :
    candS ω r (d v) (e v) ≤ d u + A' * p.nwt x + δ' := by
  obtain ⟨q, hq⟩ := walkL (x := x) p hp
  have h1 := ndsrc_le (x := fun a b => A' * x a b) (y := fun a => frc ω r (d a)) q
  rw [nwt_mul, hq] at h1
  have h2 : E * e v ≤ E * (frc ω r (d u) + A' * p.nwt x + δ') := by
    calc E * e v ≤ (E + 1) * (frc ω r (d u) + A' * p.nwt x) :=
          hhi.trans (Nat.mul_le_mul_left _ h1)
      _ = E * (frc ω r (d u) + A' * p.nwt x) + (frc ω r (d u) + A' * p.nwt x) := by ring
      _ ≤ E * (frc ω r (d u) + A' * p.nwt x) + E * δ' := by omega
      _ = E * (frc ω r (d u) + A' * p.nwt x + δ') := by ring
  have h3 := Nat.le_of_mul_le_mul_left h2 hE
  have h4 : lev ω r (d v) = lev ω r (d u) := hp v p.end_mem
  rw [candS, h4]
  have := lev_add_frc ω r (d u)
  omega

end Smooth

section Step

variable {V : Type} {adj : V → V → Prop} {x : V → V → ℕ} {d e₀ e₁ : V → ℕ} {ω h A δ δ' E : ℕ}

/-- The hypotheses of one step: the answers of the oracle on the two level graphs. -/
structure StepOK (adj : V → V → Prop) (x : V → V → ℕ) (d e₀ e₁ : V → ℕ) (ω h A' E : ℕ) : Prop where
  lo₀ : ∀ v, ndsrc (adjL adj d ω 0) (fun a b => A' * x a b) (fun a => frc ω 0 (d a)) v ≤ e₀ v
  hi₀ : ∀ v, E * e₀ v ≤ (E + 1) * ndsrc (adjL adj d ω 0) (fun a b => A' * x a b) (fun a => frc ω 0 (d a)) v
  lo₁ : ∀ v, ndsrc (adjL adj d ω h) (fun a b => A' * x a b) (fun a => frc ω h (d a)) v ≤ e₁ v
  hi₁ : ∀ v, E * e₁ v ≤ (E + 1) * ndsrc (adjL adj d ω h) (fun a b => A' * x a b) (fun a => frc ω h (d a)) v

theorem stepD_le (v : V) : stepD ω h d e₀ e₁ v ≤ d v := min_le_left _ _

/-- **The lower bound of a step.** -/
theorem step_lo {A' : ℕ} (hok : StepOK adj x d e₀ e₁ ω h A' E) (v : V) :
    ∃ u, ∃ p : Walk adj u v, d u + A' * p.nwt x ≤ stepD ω h d e₀ e₁ v := by
  obtain ⟨u₀, p₀, h₀⟩ := candS_lo (hok.lo₀ v)
  obtain ⟨u₁, p₁, h₁⟩ := candS_lo (hok.lo₁ v)
  unfold stepD
  rcases le_total (d v) (min (candS ω 0 (d v) (e₀ v)) (candS ω h (d v) (e₁ v))) with hm | hm
  · rw [min_eq_left hm]
    exact ⟨v, .nil v, by simp⟩
  · rw [min_eq_right hm]
    rcases le_total (candS ω 0 (d v) (e₀ v)) (candS ω h (d v) (e₁ v)) with hc | hc
    · rw [min_eq_left hc]
      exact ⟨u₀, p₀, h₀⟩
    · rw [min_eq_right hc]
      exact ⟨u₁, p₁, h₁⟩

/-- **The upper bound of a step.** -/
theorem step_hi (hs : Smooth adj x d A δ) (hδ : δ = 2 * δ') (hδ0 : 0 < δ) (hω : ω = 2 * h)
    (hh : (A + 3) * δ ≤ h) (hX : 2 * h + (A + 1) * δ ≤ E * δ') (hE : 0 < E)
    (hok : StepOK adj x d e₀ e₁ ω h (A + 1) E) {u v : V} (p : Walk adj u v) :
    stepD ω h d e₀ e₁ v ≤ d u + (A + 1) * p.nwt x + δ' := by
  by_cases hstr : d u + (A + 1) * p.nwt x < d v
  swap
  · exact (stepD_le v).trans (by omega)
  obtain ⟨hL, hw⟩ := smoothing_walk hs p hstr
  have hAL : A * p.nwt x ≤ A * δ := Nat.mul_le_mul_left _ hL.le
  have hAL' : (A + 1) * p.nwt x ≤ (A + 1) * δ := Nat.mul_le_mul_left _ hL.le
  have hh' : A * δ + 3 * δ ≤ h := by rw [← Nat.add_mul]; exact hh
  have hpos : 0 < h := by omega
  have hlt : d u + A * p.nwt x + δ < (d u - δ) + h := by omega
  have hin : ∀ w ∈ p.support, d u - δ ≤ d w ∧ d w ≤ d u + A * p.nwt x + δ := fun w hw' => by
    have := hw w hw'
    omega
  have hfr : ∀ r, frc ω r (d u) + (A + 1) * p.nwt x ≤ E * δ' := fun r => by
    have : frc ω r (d u) < ω := Nat.mod_lt _ (by omega)
    omega
  rcases fit hpos hlt with hf | hf
  · have hlev : ∀ w ∈ p.support, lev ω 0 (d w) = lev ω 0 (d u) := fun w hw' => by
      simp only [lev, Nat.add_zero, hω]
      rw [hf _ (hin w hw').1 (hin w hw').2, hf _ (hin u p.start_mem).1 (hin u p.start_mem).2]
    exact (min_le_right _ _).trans ((min_le_left _ _).trans
      (candS_hi hE (hok.hi₀ v) p hlev (hfr 0)))
  · have hlev : ∀ w ∈ p.support, lev ω h (d w) = lev ω h (d u) := fun w hw' => by
      simp only [lev, hω]
      rw [hf _ (hin w hw').1 (hin w hw').2, hf _ (hin u p.start_mem).1 (hin u p.start_mem).2]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      (candS_hi hE (hok.hi₁ v) p hlev (hfr h)))

/-- **A step is `(A + 1, δ / 2)`-smooth.** -/
theorem step_smooth (hs : Smooth adj x d A δ) (hδ : δ = 2 * δ') (hδ0 : 0 < δ) (hω : ω = 2 * h)
    (hh : (A + 3) * δ ≤ h) (hX : 2 * h + (A + 1) * δ ≤ E * δ') (hE : 0 < E)
    (hok : StepOK adj x d e₀ e₁ ω h (A + 1) E) : Smooth adj x (stepD ω h d e₀ e₁) (A + 1) δ' := by
  intro v w p
  obtain ⟨u, q, hq⟩ := step_lo hok v
  have := step_hi hs hδ hδ0 hω hh hX hE hok (q.append p)
  rw [Walk.nwt_append, Nat.mul_add] at this
  omega

/-- **A step does not fall below `U` times the distance**, if `d` does not and `U ≤ A'`. -/
theorem step_nd {A' U : ℕ} (y : V → ℕ) (hok : StepOK adj x d e₀ e₁ ω h A' E) (hU : U ≤ A')
    (hd : ∀ v, U * ndsrc adj x y v ≤ d v) (v : V) : U * ndsrc adj x y v ≤ stepD ω h d e₀ e₁ v := by
  obtain ⟨u, p, hp⟩ := step_lo hok v
  have h1 := Nat.mul_le_mul_left U (ndsrc_walk (x := x) y p)
  have h2 := hd u
  have h3 : U * p.nwt x ≤ A' * p.nwt x := Nat.mul_le_mul_right _ hU
  rw [Nat.mul_add] at h1
  omega

/-- A bounded estimate is smooth with a large `δ`. -/
theorem smooth_of_le {M : ℕ} (A : ℕ) (hd : ∀ v, d v ≤ M) (hM : M ≤ δ) : Smooth adj x d A δ :=
  fun {_ v} _ => (hd v).trans (hM.trans (Nat.le_add_left _ _))

end Step

section Iter

/-- The slack of step `i` out of `t`. -/
def δS (t i : ℕ) : ℕ := t * 2 ^ (t - i)

/-- Half the width of the levels of step `i`. -/
def hS (t i : ℕ) : ℕ := (5 * t + 3) * δS t i

/-- The width of the levels of step `i`. -/
def ωS (t i : ℕ) : ℕ := 2 * hS t i

theorem δS_succ {t i : ℕ} (hi : i < t) : δS t i = 2 * δS t (i + 1) := by
  unfold δS
  obtain ⟨k, hk⟩ : ∃ k, t - i = k + 1 := ⟨t - i - 1, by omega⟩
  rw [hk, show t - (i + 1) = k by omega, pow_succ]
  ring

theorem δS_pos {t : ℕ} (ht : 0 < t) (i : ℕ) : 0 < δS t i := Nat.mul_pos ht (Nat.two_pow_pos _)

variable {V : Type} {adj : V → V → Prop} {x : V → V → ℕ}

/-- **The steps of the smoothing.** With `A = 4 t + i` and `δ = t 2^(t - i)` at step `i`, the
estimates stay smooth, do not fall below `4 t` times the distance and do not grow. -/
theorem iter_inv {t E : ℕ} (ht : 0 < t) (hE : 30 * t + 14 ≤ E) (y : V → ℕ) {d e₀ e₁ : ℕ → V → ℕ}
    (hd : ∀ i, d (i + 1) = stepD (ωS t i) (hS t i) (d i) (e₀ i) (e₁ i))
    (hok : ∀ i, i < t → StepOK adj x (d i) (e₀ i) (e₁ i) (ωS t i) (hS t i) (4 * t + i + 1) E)
    (h0 : Smooth adj x (d 0) (4 * t) (δS t 0)) (hnd : ∀ v, 4 * t * ndsrc adj x y v ≤ d 0 v) :
    ∀ i, i ≤ t → Smooth adj x (d i) (4 * t + i) (δS t i) ∧
      (∀ v, 4 * t * ndsrc adj x y v ≤ d i v) ∧ ∀ v, d i v ≤ d 0 v := by
  intro i
  induction i with
  | zero => exact fun _ => ⟨h0, hnd, fun _ => le_rfl⟩
  | succ i ih =>
    intro hi
    obtain ⟨hs, hn, hle⟩ := ih (by omega)
    have hδ := δS_succ (show i < t by omega)
    have hδ0 := δS_pos ht i
    have hh : (4 * t + i + 3) * δS t i ≤ hS t i := Nat.mul_le_mul_right _ (by omega)
    have hX : 2 * hS t i + (4 * t + i + 1) * δS t i ≤ E * δS t (i + 1) := by
      have h1 : 2 * hS t i + (4 * t + i + 1) * δS t i ≤ (30 * t + 14) * δS t (i + 1) := by
        unfold hS
        rw [hδ]
        have : (4 * t + i + 1) * (2 * δS t (i + 1)) ≤ (10 * t + 2) * δS t (i + 1) := by
          rw [← mul_assoc]
          exact Nat.mul_le_mul_right _ (by omega)
        nlinarith
      exact h1.trans (Nat.mul_le_mul_right _ hE)
    rw [hd i]
    exact ⟨step_smooth hs hδ hδ0 rfl hh hX (by omega) (hok i (by omega)),
      step_nd y (hok i (by omega)) (by omega) hn, fun v => (stepD_le v).trans (hle v)⟩

/-- The output: an estimate rounded up in units of `2 t`. -/
def outR (t a : ℕ) : ℕ := (a + (2 * t - 1)) / (2 * t)

theorem le_outR {t : ℕ} (ht : 0 < t) (a : ℕ) : a ≤ 2 * t * outR t a := by
  unfold outR
  have := Nat.div_add_mod (a + (2 * t - 1)) (2 * t)
  have := Nat.mod_lt (a + (2 * t - 1)) (show 0 < 2 * t by omega)
  omega

theorem outR_le {t a k : ℕ} (ht : 0 < t) (h : a ≤ 2 * t * k) : outR t a ≤ k := by
  unfold outR
  rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
  omega

/-- **Twice the distance is a lower bound.** -/
theorem out_lo {t : ℕ} (ht : 0 < t) (y : V → ℕ) {d : V → ℕ} (hnd : ∀ v, 4 * t * ndsrc adj x y v ≤ d v)
    (v : V) : 2 * ndsrc adj x y v ≤ outR t (d v) := by
  have h1 := le_outR ht (d v)
  have h2 := hnd v
  have : 2 * t * (2 * ndsrc adj x y v) ≤ 2 * t * outR t (d v) := by
    calc 2 * t * (2 * ndsrc adj x y v) = 4 * t * ndsrc adj x y v := by ring
      _ ≤ _ := h2.trans h1
  exact Nat.le_of_mul_le_mul_left this (by omega)

/-- **The output grows by at most four times the length of an arc.** -/
theorem out_arc {t : ℕ} (ht : 0 < t) {d : V → ℕ} (hs : Smooth adj x d (5 * t) t) {a b : V} (e : adj a b)
    (hx : 1 ≤ x a b) : outR t (d b) ≤ outR t (d a) + 4 * x a b := by
  apply outR_le ht
  have h1 := hs (.cons e (.nil b))
  simp only [Walk.nwt_cons, Walk.nwt_nil, Nat.add_zero] at h1
  have h2 := le_outR ht (d a)
  have h3 : t ≤ 3 * t * x a b := by nlinarith
  nlinarith

/-- **The output is at most four times the offset**, if the first estimate is at most `8 t` times it. -/
theorem out_off {t : ℕ} (ht : 0 < t) {a φ : ℕ} (h : a ≤ 8 * t * φ) : outR t a ≤ 4 * φ :=
  outR_le ht (by nlinarith)

end Iter

end SsspFlow.Congest
