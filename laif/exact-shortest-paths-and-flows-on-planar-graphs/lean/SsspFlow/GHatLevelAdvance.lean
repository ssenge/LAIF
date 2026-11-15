import SsspFlow.GHatLevelPT
import SsspFlow.GHatLevelNext
import SsspFlow.GHatLevelState
import SsspFlow.GHatRun

/-!
# One level of the recursion as one algorithm

After the run of a level and the tests of its new corners, every node updates the states of the
corners of the darts into it and its own input of the level, and sends the new states of the
corners to the tails of the darts. Then every node holds its stored state of the next level.

* `RData.encV`, `RData.decV`, `RData.cstCode`, `RData.cstDec`: the codes of the state and the value
  of a corner as numbers.
* `RData.lv_inc_succ`, `RData.lv_cut_succ`: the incised darts and the cut corners of the next level.
* `RData.lvV8_lt`: the codes of the target corners are below `M`.
* `RData.levelAdvance_local`: one level as one algorithm, from the stored state of a level to the stored
  state of the next level.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

/-- The code of a value: `0` for values at least `M`, and `v + 1` for values `v < M`. -/
noncomputable def encV (M : ℕ) (v : ℕ∞) : ℕ := if v < M then v.toNat + 1 else 0

/-- The value of a code. -/
def decV (y : ℕ) : ℕ∞ := if y = 0 then ⊤ else ((y - 1 : ℕ) : ℕ∞)

theorem encV_le (M : ℕ) (v : ℕ∞) : encV M v ≤ M := by
  unfold encV
  split_ifs with h
  · have h' : v ≠ ⊤ := ne_top_of_lt h
    have : v.toNat < M := by
      rw [← ENat.natCast_toNat h'] at h
      exact_mod_cast h
    omega
  · omega

theorem decV_encV {M : ℕ} {v : ℕ∞} (h : v = ⊤ ∨ v < M) : decV (encV M v) = v := by
  rcases h with rfl | h
  · simp [encV, decV]
  · simp [encV, decV, h, ENat.natCast_toNat (ne_top_of_lt h)]

/-- The code of the state and the value of a corner: five bits and the code of the value. -/
noncomputable def cstCode (M : ℕ) (c : CSt × ℕ∞) : ℕ :=
  bit2 c.1.inΓ (bit2 c.1.cA (bit2 c.1.cB (bit2 c.1.src (bit2 c.1.tgt (encV M c.2)))))

/-- The state and the value of a corner from its code. -/
def cstDec (x : ℕ) : CSt × ℕ∞ :=
  (⟨dbit x 0, dbit x 1, dbit x 2, dbit x 3, dbit x 4⟩, decV (x / 32))

theorem bit2_div2 (b : Bool) (x : ℕ) : bit2 b x / 2 = x := by
  cases b <;> simp [bit2]; omega

theorem cstDec_code {M : ℕ} {c : CSt × ℕ∞} (h : c.2 = ⊤ ∨ c.2 < M) : cstDec (cstCode M c) = c := by
  have e : ∀ x : ℕ, x / 32 = x / 2 / 2 / 2 / 2 / 2 := fun x => by omega
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, v⟩ := c
  simp only [cstDec, cstCode, e, bit2_div2, dbit_bit2_zero, dbit_bit2_succ, decV_encV h]

theorem cstCode_lt {M h : ℕ} (hM : M < 2 ^ h) (c : CSt × ℕ∞) : cstCode M c < 2 ^ (h + 5) := by
  have h0 : encV M c.2 < 2 ^ h := (encV_le M c.2).trans_lt hM
  unfold cstCode
  exact bit2_lt (bit2_lt (bit2_lt (bit2_lt (bit2_lt h0))))

variable {n : ℕ} {N : Net (Fin n)} (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath}
  {cc : N.G.Dart → ℕ} {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
  {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
  {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}

/-- The codes of the target corners are below `M`. -/
theorem lvV8_lt (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) (z : N.G.Dart × Bool) {M : ℕ}
    (hM8 : (Cp.m + 2) ^ 8 ≤ M) : lvV8 r ℓ z = ⊤ ∨ lvV8 r ℓ z < M := by
  have h1 : 1 ≤ (Cp.m + 2) ^ 8 := Nat.one_le_pow _ _ (by omega)
  suffices h : lvV8 r ℓ z = ⊤ ∨ lvV8 r ℓ z ≤ ((M - 1 : ℕ) : ℕ∞) by
    rcases h with h | h
    · exact .inl h
    · exact .inr (h.trans_lt (by exact_mod_cast (show M - 1 < M by omega)))
  unfold lvV8
  refine ENat.iInf_top_or_le fun q => ENat.iInf_top_or_le fun hq => ENat.iInf_top_or_le fun _ => .inr ?_
  obtain ⟨e1, e2⟩ := rngA_le r ℓ hq
  have e3 := pair_lt_sq (a := (rngA r ℓ q.1).1) (b := (rngA r ℓ q.1).2) (Y := Cp.m + 1) (by omega) (by omega)
  have e4 : (Cp.m + 1) ^ 2 ≤ (Cp.m + 2) ^ 8 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  exact_mod_cast (show Nat.pair (rngA r ℓ q.1).1 (rngA r ℓ q.1).2 ≤ M - 1 by omega)

variable (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d)
  (hE : ExactSsspBound) (K D M : ℕ) (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ)

/-- The cut corners are the same at every level. -/
theorem lv_cut_succ : (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1)).cut = (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).cut := by
  ext c
  simp [lvS, CutPath.Run.data, RData.ofCorners, CutPath.Run.not_true_steps]

theorem lv_inc_iff (r : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ' : ℕ) (d : N.G.Dart) :
    d ∈ (lvS modeL hostT hhost r ℓ').inc ↔ (d, false) ∈ Γ₀ ∪ r.steps ℓ' := by
  simp [lvS, CutPath.Run.data, RData.ofCorners]

variable (hpick : ∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
    Nonempty {d : CutPath.NodeData s.1.2 s.2.1.1 s.2.1.2 //
      lvPof hN modeL hostT hhost hE K D M ℓ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) s.1 ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts})
include hpick

/-- **The incised darts of the next level** are those of the level and the darts of the steps of the
level, in either direction. -/
theorem lv_inc_succ (d : N.G.Dart) :
    d ∈ (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1)).inc ↔ d ∈ (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).inc ∨ ∃ β, lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ (d, β) ∨ lvStepDart hN modeL hostT hhost hE K D M r₀ ℓ (N.toRot.dual.rev d, β) := by
  rw [lv_inc_iff modeL hostT hhost, lv_inc_iff modeL hostT hhost, Finset.mem_union, Finset.mem_union,
    lv_steps_succ hN modeL hostT hhost hE K D M r₀ ℓ hpick]
  constructor
  · rintro (h | h | ⟨z, hz, h⟩)
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · right
      rcases h with h | h <;> simp only [Prod.mk.injEq, and_true] at h
      · subst h
        exact ⟨z.2, .inl hz⟩
      · subst h
        exact ⟨z.2, .inr (by rw [N.toRot.dual.rev_rev]; exact hz)⟩
  · rintro ((h | h) | ⟨β, h | h⟩)
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr ⟨(d, β), h, .inl rfl⟩)
    · exact .inr (.inr ⟨(N.toRot.dual.rev d, β), h, .inr (by rw [N.toRot.dual.rev_rev])⟩)

omit hpick

end RData

namespace RData

open Cslib.Congest.Algorithm

open Classical in
/-- **One level as one algorithm.** Every node starts with its stored state of level `ℓ`, whose input
of the level has both sources at the star centre of `w₀`. After the run, every node holds its stored
state of level `ℓ + 1`: its input of the next level, the same number `m`, base values and indices of
the top annulus, and the states and codes of the corners of the next level at the darts from it and
into it. -/
theorem levelAdvance_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LvX n) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (xN : Fin n → σ → LvX n),
    T ≤ 32 + 19 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
    ∀ (N : Net (Fin n)) (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath} {cc : N.G.Dart → ℕ}
      {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
      {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
      {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}
      (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d) (M : ℕ)
      (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) (X : Fin n → LvX n) (w₀ : Fin n),
      (∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
        Nonempty {d : CutPath.NodeData s.1.2 s.2.1.1 s.2.1.2 //
          lvPof hN modeL hostT hhost hE K D M ℓ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) s.1 ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts}) →
      N.toRot.Planar → N.toRot.Connected → (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).NoConflict → (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).cut.card ≤ 3 → N.DiamLE D →
      (∀ d, 1 ≤ cc d) → (∀ d, cc (N.toRot.rev d) = cc d) → (∀ d, cc d ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, Cp.lamD (Nat.cast ∘ cc) q.2 < M) → (Cp.m + 2) ^ 8 ≤ M →
      (∀ w, (X w).1 = (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).starV hN w₀) w) → (∀ w, (X w).2.1 = Cp.m) →
      (∀ k, k ≤ 3 → ∀ (d : N.G.Dart) b, ((X d.fst).2.2.1 k).1 d.snd b = gsBase Cp k (d, b) ∧
        ((X d.snd).2.2.1 k).2 d.fst b = gsBase Cp k (d, b)) →
      (∀ (d : N.G.Dart) b, (X d.fst).2.2.2.2.1 d.snd b = (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b), lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b)) ∧
        (X d.snd).2.2.2.2.2 d.fst b = (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b), lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b))) →
      (∀ (d : N.G.Dart) b t, ((((X d.snd).2.2.2.1 d.fst b).1 t = true ↔ (d, b) = L₀.κ0 t) ∧
        (((X d.snd).2.2.2.1 d.fst b).2 t = true ↔ (d, b) = L₀.κ1 t))) →
      let st := A.run N.G X T
      (∀ w, (xN w (st w)).1 = (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1)).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1))) M ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1)).starV hN w₀) w) ∧
      (∀ w, (xN w (st w)).2.1 = (X w).2.1) ∧ (∀ w, (xN w (st w)).2.2.1 = (X w).2.2.1) ∧
      (∀ w, (xN w (st w)).2.2.2.1 = (X w).2.2.2.1) ∧
      (∀ (d : N.G.Dart) b, (xN d.fst (st d.fst)).2.2.2.2.1 d.snd b = (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) (d, b), lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) (d, b)) ∧
        (xN d.snd (st d.snd)).2.2.2.2.2 d.fst b = (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) (d, b), lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) (d, b))) := by
  obtain ⟨C, c, hPT⟩ := levelPT_local hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ₁, A₁, T₁, oT, oS, fA, fB, pA, pB, dg, F, xO, hT₁, hA₁⟩ := hPT n D
  let J := LvX n
  let pre : Fin n → σ₁ → J := fun w s =>
    ((xO w s).1.next (fun u => F w s u && decide (u ∈ (xO w s).1.rot)), (xO w s).2.1, (xO w s).2.2.1,
      (xO w s).2.2.2.1, ((xO w s).2.2.2.2.1, fun u b => cstNext (xO w s).1.bnd (oT w s u b) (oS w s u b)
        ((xO w s).2.2.2.2.2 u b).1 (fA w s u b) (pA w s u b) (fB w s u b) (pB w s u b) (dg w s u b)
        ((xO w s).2.2.2.1 u b).1 ((xO w s).2.2.2.1 u b).2))
  let msgOf : J → Fin n → ℕ := fun x u =>
    Nat.pair (cstCode x.1.bnd (x.2.2.2.2.2 u false)) (cstCode x.1.bnd (x.2.2.2.2.2 u true))
  let B₂ := (exchTo (Fin n) (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5))).keep (fun _ (x : J) => msgOf x)
  refine ⟨_, A₁.seq T₁ pre B₂, T₁ + 1, fun w s => Sum.elim (fun p => xO w p.2)
    (fun q => (q.1.1, q.1.2.1, q.1.2.2.1, q.1.2.2.2.1, (fun u b => cstDec (if b then (Nat.unpair ((q.2.2 u).getD 0)).2
      else (Nat.unpair ((q.2.2 u).getD 0)).1), q.1.2.2.2.2.2))) s, by omega, ?_⟩
  intro N hN Cp cc hR hC hgc Γ₀ L₀ j k modeL hostT hhost M r₀ ℓ X w₀ hpick hP hc hS hcut hD hc1 hcr hcb hM hQM hM8
    hX1 hX2 hXb hXc hXk
  have hPT' := hA₁ N hN modeL hostT hhost M r₀ ℓ X ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).starV hN w₀) hpick hP hc hS hcut hD hc1 hcr hcb hM hQM hM8
    hX1 hX2 hXb hXc
  dsimp only at hPT'
  obtain ⟨⟨payT, payS, h_in, h_guard, h_pay⟩, hts, hxO⟩ := hPT'
  set st₁ := A₁.run N.G X T₁ with hst₁
  have hbnd : ∀ w, (pre w (st₁ w)).1.bnd = M := fun w => by
    show (xO w (st₁ w)).1.bnd = M
    rw [hxO w, hX1 w]
    rfl
  have hMb : M < 2 ^ (K * logN (n * (n * 21)) + 1) := lam_lt_pow hM
  have hmsg : ∀ u w, msgOf (pre u (st₁ u)) w < 2 ^ (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)) := fun u w => by
    have e1 := cstCode_lt hMb ((pre u (st₁ u)).2.2.2.2.2 w false)
    have e2 := cstCode_lt hMb ((pre u (st₁ u)).2.2.2.2.2 w true)
    rw [← hbnd u] at e1 e2
    have e3 := pair_lt_sq (Y := 2 ^ (K * logN (n * (n * 21)) + 1 + 5)) (Nat.succ_le_of_lt e1) (Nat.succ_le_of_lt e2)
    refine e3.trans_le ?_
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hrun : (A₁.seq T₁ pre B₂).run N.G X (T₁ + 1) = fun w => .inr (pre w (st₁ w),
      (msgOf (pre w (st₁ w)), fun u => if N.G.Adj u w then some (msgOf (pre u (st₁ u)) w) else none)) := by
    funext w
    simp only [B₂, run_seq, run_keep]
    rw [← hst₁, run_exchTo N.G _ hmsg]
  have hin : ∀ (d : N.G.Dart) b, (pre d.snd (st₁ d.snd)).2.2.2.2.2 d.fst b =
      (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) (d, b), lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) (d, b)) := fun d b => by
    show cstNext (xO d.snd (st₁ d.snd)).1.bnd _ _ ((xO d.snd (st₁ d.snd)).2.2.2.2.2 d.fst b).1 _ _ _ _ _
      ((xO d.snd (st₁ d.snd)).2.2.2.1 d.fst b).1 ((xO d.snd (st₁ d.snd)).2.2.2.1 d.fst b).2 = _
    rw [hxO d.snd, (hXc d b).2]
    rw [hX1 d.snd]
    exact lvCSt_next hN modeL hostT hhost hE K D M r₀ ℓ hpick payT payS
      (fun z => oT z.1.snd (st₁ z.1.snd) z.1.fst z.2) (fun z => oS z.1.snd (st₁ z.1.snd) z.1.fst z.2) M
      h_in h_guard h_pay (d, b) _ _ _ _ _ _ _ (hts d b).1 (hts d b).2.1 (hts d b).2.2.1 (hts d b).2.2.2.1
      (hts d b).2.2.2.2.1 (fun t => (hXk d b t).1) (fun t => (hXk d b t).2)
  dsimp only
  rw [hrun]
  simp only [Sum.elim_inr]
  refine ⟨fun w => ?_, fun w => by show (xO w (st₁ w)).2.1 = _; rw [hxO w],
    fun w => by show (xO w (st₁ w)).2.2.1 = _; rw [hxO w], fun w => by show (xO w (st₁ w)).2.2.2.1 = _; rw [hxO w], fun d b => ⟨?_, hin d b⟩⟩
  · show (xO w (st₁ w)).1.next _ = _
    rw [hxO w, hX1 w]
    refine levelIn_next (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ) (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1)) hN (fun w u => F w (st₁ w) u && decide (u ∈ N.rotList w)) ?_ ?_
      (lv_cut_succ hN modeL hostT hhost hE K D M r₀ ℓ) rfl rfl cc _ _ (fun _ => rfl) (fun _ => rfl) M w₀ w
    · intro w u h
      rw [Bool.and_eq_true, decide_eq_true_iff] at h
      exact (N.mem_rotList w u).1 h.2
    · intro d
      rw [lv_inc_succ hN modeL hostT hhost hE K D M r₀ ℓ hpick d, Bool.and_eq_true, decide_eq_true_iff,
        (hts d false).2.2.2.2.2]
      exact or_congr Iff.rfl ⟨fun h => ⟨h, (N.mem_rotList _ _).2 d.adj⟩, fun h => h.1⟩
  · simp only [d.adj.symm, ↓reduceIte, Option.getD_some, msgOf, Nat.unpair_pair]
    rw [hbnd d.snd]
    have hv := lvV8_lt (lvSeq hN modeL hostT hhost hE K D M r₀ (ℓ + 1)) (ℓ + 1) (d, b) hM8
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hin d false]
      exact cstDec_code hv
    · simp only [↓reduceIte]
      rw [hin d true]
      exact cstDec_code hv

end RData

end RotSystem

end SsspFlow
