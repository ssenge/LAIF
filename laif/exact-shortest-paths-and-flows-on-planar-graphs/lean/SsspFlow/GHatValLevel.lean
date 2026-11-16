import SsspFlow.GHatValSel
import SsspFlow.GHatValRun

/-!
# The lengths of the cut computed at one level, as one algorithm

After the run of a level and the tests (`levelPT_local`), every corner of the component of an
annulus that is not a leaf holds the values of the annulus. Three rules read an index from them: the
middle index, `i1` and `i2`, each kept when it lies strictly inside the range. For each rule the
corners decide locally whether they are source or target corners, and one run of the oracle
(`levelQRun_local`) gives every node the least `λ_t` of the targets it hosts. The three runs are one
repetition of a fixed algorithm, and the nodes keep the least value.

* `RData.pk`: the three rules.
* `RData.selB`: the local test of a corner for a rule.
* `RData.levelVals_local`: the algorithm and its output.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

/-- The three rules: the middle index, `i1` and `i2`. -/
def pk : Fin 3 → ℕ × ℕ × ℕ × ℕ → Bool × Bool → Option ℕ
  | 0 => fun p _ => some ((p.1 + p.2.1) / 2)
  | 1 => fun p _ => some p.2.2.1
  | 2 => fun p _ => some p.2.2.2

/-- The local test of a corner for a rule, from its two values and its indices of the top annulus. -/
def selB (pick : ℕ × ℕ × ℕ × ℕ → Bool × Bool → Option ℕ) (vT vS : ℕ∞) (kap : ℕ → Bool) : Prop :=
  ∃ t, pick (decT vT.toNat) (decS vS.toNat) = some t ∧ (decT vT.toNat).1 < t ∧
    t < (decT vT.toNat).2.1 ∧ kap t = true

open Classical in
/-- The flag of a corner for a rule: `0` if its values are below `M` and it passes the test. -/
noncomputable def selFlag (M : ℕ) (pick : ℕ × ℕ × ℕ × ℕ → Bool × Bool → Option ℕ) (vT vS : ℕ∞)
    (kap : ℕ → Bool) : ℕ∞ :=
  if vT < M ∧ vS < M ∧ selB pick vT vS kap then 0 else ⊤

open Classical Cslib.Congest.Algorithm in
/-- **The lengths of the cut at one level, as one algorithm.** Every node starts with its stored state
of level `ℓ`. After `T` rounds every node holds the least `λ_t` over the three rules and the annuli of
the list of the rule whose target copy it hosts. -/
theorem levelVals_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LvX n) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (vo : Fin n → σ → ℕ∞),
    T ≤ 37 + 22 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
    ∀ (N : Net (Fin n)) (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath} {cc : N.G.Dart → ℕ}
      {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
      {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
      {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}
      (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d) (M : ℕ)
      (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) (X : Fin n → LvX n) (u₀ : (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).hRot.Vertex),
      (∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
        Nonempty {d : CutPath.NodeData s.1.2 s.2.1.1 s.2.1.2 //
          lvPof hN modeL hostT hhost hE K D M ℓ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) s.1 ((s.2.1.1 + s.2.1.2) / 2) d.q d.S.darts}) →
      N.toRot.Planar → N.toRot.Connected → (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).NoConflict → (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).cut.card ≤ 3 → N.DiamLE D →
      (∀ d, 1 ≤ cc d) → (∀ d, cc (N.toRot.rev d) = cc d) → (∀ d, cc d ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ t, t ≤ Cp.m → Cp.lamD (Nat.cast ∘ cc) t < M) → (Cp.m + 2) ^ 8 ≤ M →
      (∀ w, (X w).1 = (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M u₀ w) → (∀ w, (X w).2.1 = Cp.m) →
      (∀ k, k ≤ 3 → ∀ (d : N.G.Dart) b, ((X d.fst).2.2.1 k).1 d.snd b = gsBase Cp k (d, b) ∧
        ((X d.snd).2.2.1 k).2 d.fst b = gsBase Cp k (d, b)) →
      (∀ (d : N.G.Dart) b, (X d.fst).2.2.2.2.1 d.snd b = (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b), lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b)) ∧
        (X d.snd).2.2.2.2.2 d.fst b = (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b), lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (d, b))) →
      (∀ (d : N.G.Dart) b t, ((((X d.snd).2.2.2.1 d.fst b).1 t = true ↔ (d, b) = L₀.κ0 t) ∧
        (((X d.snd).2.2.2.1 d.fst b).2 t = true ↔ (d, b) = L₀.κ1 t))) →
      ∃ payT payS : (Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live (Nat.cast ∘ cc) Γ') × ℕ → ℕ,
        (∀ s ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).subs ℓ, s.2.1.1 + 2 ≤ s.2.1.2 →
          ∀ kk i1 i2, lvDat hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk i1 i2 →
            decT (payT (s.1, (s.2.1.1 + s.2.1.2) / 2)) = (s.2.1.1, s.2.1.2, i1, i2) ∧
            decS (payS (s.1, (s.2.1.1 + s.2.1.2) / 2)) = lvBits hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ s kk ∧
            payT (s.1, (s.2.1.1 + s.2.1.2) / 2) < M ∧ payS (s.1, (s.2.1.1 + s.2.1.2) / 2) < M) ∧
        ∀ w, (vo w (A.run N.G X T w) : ℝ≥0∞) =
          ⨅ i : Fin 3, ⨅ q ∈ selQ (pk i) payT payS ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ),
            ⨅ (_ : hostOf (((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN).ι
              (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV (q.1.2.κ1 q.2)))) = w),
              Cp.lamD (Nat.cast ∘ cc) q.2 := by
  obtain ⟨C₁, c₁, hPT⟩ := levelPT_local hE K
  obtain ⟨C₂, c₂, hQR⟩ := levelQRun_local hE K
  refine ⟨C₁ + C₂, c₁ + c₂, fun n D => ?_⟩
  have hL : 1 ≤ logN (n * (n * 21)) := by unfold logN; omega
  have hp₁ : logN (n * (n * 21)) ^ c₁ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hp₂ : logN (n * (n * 21)) ^ c₂ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hm₁ := Nat.mul_le_mul (show C₁ ≤ C₁ + C₂ by omega) hp₁
  have hm₂ := Nat.mul_le_mul (show C₂ ≤ C₁ + C₂ by omega) hp₂
  have w₁ : 4 * (C₁ * logN (n * (n * 21)) ^ c₁ + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤
      4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by omega
  have w₂ : 4 * (C₂ * logN (n * (n * 21)) ^ c₂) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤
      4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by omega
  obtain ⟨σ₁, A₁, T₁, oT, oS, _fA, _fB, _pA, _pB, _dg, _F, xO, hT₁, hA₁⟩ := hPT n D
  obtain ⟨σ₂, A₂, vmin, hA₂⟩ := hQR n D
  set T₂ := 2 + C₂ * logN (n * (n * 21)) ^ c₂ * (12 * D + 16) with hT₂
  let J := LevelIn n × (Fin 3 → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)) × ℕ × ℕ∞
  let fl : Fin n → σ₁ → Fin 3 → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞) := fun w s i =>
    (fun u b => selFlag (xO w s).1.bnd (pk i) (oT w s u b) (oS w s u b) ((xO w s).2.2.2.1 u b).1,
      fun u b => selFlag (xO w s).1.bnd (pk i) (oT w s u b) (oS w s u b) ((xO w s).2.2.2.1 u b).2)
  let f₁ : Fin n → σ₁ → J := fun w s => ((xO w s).1, fl w s, 0, ⊤)
  let gI : Fin n → J → LevelIn n × (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞) := fun _ x =>
    (x.1, (x.2.1 ⟨x.2.2.1 % 3, Nat.mod_lt _ (by norm_num)⟩).1, (x.2.1 ⟨x.2.2.1 % 3, Nat.mod_lt _ (by norm_num)⟩).2)
  let uI : Fin n → J → σ₂ → J := fun v x s => (x.1, x.2.1, x.2.2.1 + 1, min x.2.2.2 (vmin v s))
  let A₃ := (A₂.widen w₂).iter T₂ gI uI
  refine ⟨_, (A₁.widen w₁).seq T₁ f₁ A₃, T₁ + 3 * T₂,
    fun _ s => match s with
      | .inr s' => s'.1.2.2.2
      | .inl _ => ⊤, ?_, ?_⟩
  · have h : C₁ * logN (n * (n * 21)) ^ c₁ * (12 * D + 16) ≤ (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₁
    have h' : C₂ * logN (n * (n * 21)) ^ c₂ * (12 * D + 16) ≤ (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₂
    omega
  intro N hN Cp cc hR hC hgc Γ₀ L₀ j k modeL hostT hhost M r₀ ℓ X u₀ hpick hP hc hS hcut hD hc1 hcr hcb hM hMl hM8
    hX1 hX2 hXb hXc hXk
  have hQM : ∀ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, Cp.lamD (Nat.cast ∘ cc) q.2 < M := fun q hq =>
    hMl _ ((((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ_range ℓ q hq).2.2.2.1).trans q.1.2.xb_le)
  have hPT1 := hA₁ N hN modeL hostT hhost M r₀ ℓ X u₀ hpick hP hc hS hcut hD hc1 hcr hcb hM hQM hM8 hX1 hX2 hXb hXc
  dsimp only at hPT1
  obtain ⟨⟨payT, payS, hreg, hguard, hpay⟩, -, hxO⟩ := hPT1
  refine ⟨payT, payS, hpay, fun w => ?_⟩
  set st := (A₁.widen w₁).run N.G X T₁ with hst
  have hst' : st = A₁.run N.G X T₁ := run_widen _ _ _ _ _
  let F : Fin n → Fin 3 → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞) := fun v => fl v (st v)
  let Lv : Fin n → LevelIn n := fun v => (xO v (st v)).1
  let a : Fin 3 → Fin n → ℕ∞ := fun i v => vmin v (A₂.run N.G (fun v => (Lv v, (F v i).1, (F v i).2)) T₂ v)
  let j₀ : Fin n → J := fun v => f₁ v (st v)
  have hT₂p : 0 < T₂ := by rw [hT₂]; omega
  have hD1 : iterData (A₂.widen w₂) T₂ gI uI N.G j₀ 1 = fun v => (Lv v, F v, 1, min ⊤ (a 0 v)) := by
    funext v
    simp only [iterData, j₀, f₁, uI, run_widen]
    rfl
  have hD2 : iterData (A₂.widen w₂) T₂ gI uI N.G j₀ 2 = fun v => (Lv v, F v, 2, min (min ⊤ (a 0 v)) (a 1 v)) := by
    funext v
    rw [iterData, hD1]
    simp only [uI, run_widen]
    rfl
  have hD3 : iterData (A₂.widen w₂) T₂ gI uI N.G j₀ 3 =
      fun v => (Lv v, F v, 3, min (min (min ⊤ (a 0 v)) (a 1 v)) (a 2 v)) := by
    funext v
    rw [iterData, hD2]
    simp only [uI, run_widen]
    rfl
  have hrun : ((A₁.widen w₁).seq T₁ f₁ A₃).run N.G X (T₁ + 3 * T₂) w =
      .inr (iterData (A₂.widen w₂) T₂ gI uI N.G j₀ 3 w, 0,
        (A₂.widen w₂).run N.G (fun v => gI v (iterData (A₂.widen w₂) T₂ gI uI N.G j₀ 3 v)) 0 w) := by
    rw [run_seq]
    exact congrArg Sum.inr (congrFun (run_iter (A₂.widen w₂) gI uI N.G j₀ hT₂p 3 0 hT₂p) w)
  rw [hrun, hD3]
  dsimp only
  -- the three runs of the oracle
  have hXw : ∀ v, xO v (st v) = X v := fun v => by rw [hst']; exact hxO v
  have hLv : ∀ v, Lv v = (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M u₀ v := fun v => by
    simp only [Lv, hXw]; exact hX1 v
  have hbnd : ∀ v, (xO v (st v)).1.bnd = M := fun v => by
    rw [show (xO v (st v)).1 = Lv v from rfl, hLv]; rfl
  have hkap : ∀ (d : N.G.Dart) b t (τ : Fin 2),
      ((if τ = 0 then ((xO d.snd (st d.snd)).2.2.2.1 d.fst b).1 else ((xO d.snd (st d.snd)).2.2.2.1 d.fst b).2) t = true ↔
        (d, b) = qEnd τ (⟨Γ₀, L₀⟩, t)) := by
    intro d b t τ
    rw [hXw]
    unfold qEnd
    split_ifs
    · exact (hXk d b t).1
    · exact (hXk d b t).2
  have hflag : ∀ (i : Fin 3) (τ : Fin 2) (d : N.G.Dart) b,
      selFlag M (pk i) (oT d.snd (st d.snd) d.fst b) (oS d.snd (st d.snd) d.fst b)
        ((if τ = 0 then ((xO d.snd (st d.snd)).2.2.2.1 d.fst b).1 else ((xO d.snd (st d.snd)).2.2.2.1 d.fst b).2)) =
      if ∃ q ∈ selQ (pk i) payT payS ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ), (d, b) = qEnd τ q then 0 else ⊤ := by
    intro i τ d b
    unfold selFlag
    refine if_congr ?_ rfl rfl
    rw [← selQ_corner_iff hN modeL hostT hhost hE K D M r₀ ℓ hpick (pk i) payT payS hpay
      (fun z => oT z.1.snd (st z.1.snd) z.1.fst z.2) (fun z => oS z.1.snd (st z.1.snd) z.1.fst z.2)
      (by rw [hst']; exact hreg) (by rw [hst']; exact hguard) τ (d, b)]
    unfold selB
    refine and_congr Iff.rfl (and_congr Iff.rfl (exists_congr fun t => ?_))
    rw [hkap d b t τ]
  have hrunI : ∀ i : Fin 3, ((a i w : ℕ∞) : ℝ≥0∞) =
      ⨅ q ∈ selQ (pk i) payT payS ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ),
        ⨅ (_ : hostOf (((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN).ι (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV (q.1.2.κ1 q.2)))) = w), Cp.lamD (Nat.cast ∘ cc) q.2 := by
    intro i
    have e : (fun v => (Lv v, (F v i).1, (F v i).2)) =
        fun v => ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M u₀ v, (F v i).1, (F v i).2) := funext fun v => by rw [hLv]
    simp only [a, e]
    refine hA₂ N (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ) hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M u₀ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ cc _
      (fun v => (F v i).1) (fun v => (F v i).2) hP hc hS hcut hD (fun x => hcb x.1.1) hM hcr (fun _ => rfl)
      (fun _ => rfl) ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).data_Γ ℓ modeL hostT _)
      (selQ_range hN modeL hostT hhost hE K D M r₀ ℓ hpick (pk i) payT payS hpay hMl)
      (selQ_uniq hN modeL hostT hhost hE K D M r₀ ℓ hpick (pk i) payT payS hpay) (fun d b => ?_) (fun d b => ?_) w
    · have := hflag i 0 d b
      simp only [ite_true] at this
      simp only [F, fl, hbnd]
      exact this
    · have := hflag i 1 d b
      simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false] at this
      simp only [F, fl, hbnd]
      exact this
  simp only [ENat.toENNReal_min, top_inf_eq, hrunI]
  refine le_antisymm (le_iInf fun i => ?_) (le_min (le_min (iInf_le _ 0) (iInf_le _ 1)) (iInf_le _ 2))
  fin_cases i
  · exact (min_le_left _ _).trans (min_le_left _ _)
  · exact (min_le_left _ _).trans (min_le_right _ _)
  · exact min_le_right _ _

end RData

end RotSystem

end SsspFlow
