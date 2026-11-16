import SsspFlow.GHatOvSide
import SsspFlow.GHatLevelPT

/-!
# Both overlap sides of a level, as one algorithm

Every node starts with its stored state of level `ℓ`. The run of the level gives the values of the
annuli at their corners and the flags and offsets at the identifiers; one round tells every node the
records of the darts of its neighbours. Then the algorithm of one side (`levelOvSide_local`) runs for
the side `0` and for the side `1`, and every node keeps the least value.

* `RData.levelOv_local`: the algorithm and its output.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

open Classical Cslib.Congest.Algorithm in
/-- **Both overlap sides of a level, as one algorithm.** Every node starts with its stored state of
level `ℓ`. After `T` rounds every node `w` holds the least `λ_μ` over the two sides, the annuli of the
list of the level and the indices `μ` that pass the test of the side with the values of the annulus
and whose corner `κ1(μ)` is hosted at `w`. The values of the annuli hold the range and the least and
greatest index of the chain of the annulus, and its bits. -/
theorem levelOv_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LvX n) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (vo : Fin n → σ → ℕ∞),
    T ≤ 41 + 27 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
    ∀ (N : Net (Fin n)) (hN : ∀ u, ∃ w, N.G.Adj u w) {Cp : N.toRot.dual.CutPath} {cc : N.G.Dart → ℕ}
      {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
      {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
      {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live (Nat.cast ∘ cc) Γ₀} {j k : ℕ}
      (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d) (M : ℕ)
      (r₀ : CutPath.Run hR hC hgc Γ₀ L₀ j k) (ℓ : ℕ) (X : Fin n → LvX n) (u₀ : (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).hRot.Vertex),
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
          ⨅ σs : Fin 2, ⨅ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, ⨅ μ, ⨅ (_ : ovIn σs (decT (payT q)) (decS (payS q)) μ),
            ⨅ (_ : (q.1.2.κ1 μ).1.snd = w), Cp.lamD (Nat.cast ∘ cc) μ := by
  obtain ⟨C₁, c₁, hPy⟩ := levelPay_local hE K
  obtain ⟨C₂, c₂, hOv⟩ := levelOvSide_local hE K
  refine ⟨C₁ + C₂, c₁ + c₂, fun n D => ?_⟩
  obtain ⟨σ₁, A₁, T₁, rr, r₂, r₃, rA, rB, o1, o2, offO, flgO, cflO, outT, outS, hT₁, hA₁⟩ := hPy n D
  obtain ⟨σ₂, A₂, T₂, val, hT₂, hA₂⟩ := hOv n D
  have hL : 1 ≤ logN (n * (n * 21)) := by unfold logN; omega
  have hp₁ : logN (n * (n * 21)) ^ c₁ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hp₂ : logN (n * (n * 21)) ^ c₂ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hm₁ := Nat.mul_le_mul (show C₁ ≤ C₁ + C₂ by omega) hp₁
  have hm₂ := Nat.mul_le_mul (show C₂ ≤ C₁ + C₂ by omega) hp₂
  have w₁ : 4 * (C₁ * logN (n * (n * 21)) ^ c₁ + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤
      4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by omega
  have w₂ : 4 * (C₂ * logN (n * (n * 21)) ^ c₂ + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤
      4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by omega
  let Bw := 4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)
  let b := K * logN (n * (n * 21)) + 1
  let B₁ := (A₁.widen w₁).keep (fun _ (x : LvX n) => (x.1, x.2.1, valsOf x))
  let Aex := (exchTo (Fin n) Bw).keep (fun _ (y : LvX n × σ₁) => y.1.1.msg b)
  let mk : Fin n → (LvX n × σ₁) × ((Fin n → ℕ) × (Fin n → Option ℕ)) → OvIn n := fun w y =>
    { lv := y.1.1.1, inn := LevelIn.inn b y.2.2,
      off := fun a => offO a y.1.2, tg := fun a => (flgO a y.1.2).1, cf := fun a => cflO a y.1.2,
      pT := fun u β => outT (idEquiv (cornerName y.1.1.1.rot y.1.1.1.own w u β)) y.1.2,
      pS := fun u β => outS (idEquiv (cornerName y.1.1.1.rot y.1.1.1.own w u β)) y.1.2,
      k0 := fun u β => (y.1.1.2.2.2.1 u β).1, k1 := fun u β => (y.1.1.2.2.2.1 u β).2, sd := 0 }
  let gI : Fin n → OvIn n × ℕ × ℕ∞ → OvIn n := fun _ x =>
    { x.1 with sd := ⟨x.2.1 % 2, Nat.mod_lt _ (by norm_num)⟩ }
  let uI : Fin n → OvIn n × ℕ × ℕ∞ → ℕ × σ₂ → OvIn n × ℕ × ℕ∞ := fun v x s =>
    (x.1, x.2.1 + 1, min x.2.2 (val v s.2))
  let A₃ := ((A₂.stopAt T₂).widen w₂).iter (T₂ + 1) gI uI
  refine ⟨_, B₁.seq T₁ (fun _ s => s) (Aex.seq 1 (fun w y => (mk w y, 0, ⊤)) A₃), T₁ + (1 + (2 * (T₂ + 1) + 0)),
    fun _ s => match s with
      | .inr (.inr s') => s'.1.2.2
      | _ => ⊤, ?_, ?_⟩
  · have h : C₁ * logN (n * (n * 21)) ^ c₁ * (12 * D + 16) ≤ (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₁
    have h' : C₂ * logN (n * (n * 21)) ^ c₂ * (12 * D + 16) ≤ (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₂
    omega
  intro N hN Cp cc hR hC hgc Γ₀ L₀ j k modeL hostT hhost M r₀ ℓ X u₀ hP hc hS hcut hD hc1 hcr hcb hM hMl hM8
    hX1 hX2 hXb hXc hXk
  have hQM : ∀ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, Cp.lamD (Nat.cast ∘ cc) q.2 < M := fun q hq =>
    hMl _ ((((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ_range ℓ q hq).2.2.2.1).trans q.1.2.xb_le)
  have hm2 : Cp.m + 2 ≤ (Cp.m + 2) ^ 8 := Nat.le_self_pow (by norm_num) _
  have hM1 : 1 ≤ M := by omega
  have hmM : Cp.m < M := by omega
  have hin1 : (fun w => ((X w).1, (X w).2.1, valsOf (X w))) = fun w => ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M u₀ w, Cp.m, valsOf (X w)) :=
    funext fun w => by rw [hX1 w, hX2 w]
  -- the run of the level
  let gs : ℕ → N.G.Dart × Bool → ℕ∞ := fun k z =>
    if k ≤ 3 then gsBase Cp k z else gsOf k (lvCSt (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ z, lvV8 (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ z)
  have hmB : Cp.m ≤ (n * (n * 21) + 2) ^ K := by omega
  have hgs : ∀ k z, gs k z = ⊤ ∨ gs k z ≤ (n * (n * 21) + 2) ^ K := by
    intro k z
    simp only [gs]
    split_ifs with hk
    · unfold gsBase
      split_ifs
      · exact ENat.iInf_top_or_le fun r => ENat.iInf_top_or_le fun hr => .inr (by exact_mod_cast hr.1.trans hmB)
      · exact ENat.iInf_top_or_le fun r => ENat.iInf_top_or_le fun _ =>
          .inr (by exact_mod_cast (Nat.sub_le _ _).trans hmB)
      · unfold flagVal; split_ifs <;> simp
      · unfold flagVal; split_ifs <;> simp
    · unfold gsOf
      split_ifs <;> try simp
      unfold lvV8
      refine ENat.iInf_top_or_le fun q => ENat.iInf_top_or_le fun hq => ENat.iInf_top_or_le fun _ => .inr ?_
      obtain ⟨e1, e2⟩ := rngA_le (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ hq
      have e3 := pair_lt_sq (a := (rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1).1) (b := (rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1).2) (Y := Cp.m + 1) (by omega) (by omega)
      have e4 : (Cp.m + 1) ^ 2 ≤ (Cp.m + 2) ^ 8 :=
        (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
      have e5 : Nat.pair (rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1).1 (rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1).2 ≤ (n * (n * 21) + 2) ^ K := by omega
      exact_mod_cast e5
  have hvo : ∀ k (d : N.G.Dart) b, (valsOf (X d.fst) k).1 d.snd b = gs k (d, b) := by
    intro k d b
    simp only [valsOf, gs]
    split_ifs with hk
    · exact (hXb k hk d b).1
    · show gsOf k ((X d.fst).2.2.2.2.1 d.snd b) = _
      rw [(hXc d b).1]
  have hvi : ∀ k (d : N.G.Dart) b, (valsOf (X d.snd) k).2 d.fst b = gs k (d, b) := by
    intro k d b
    simp only [valsOf, gs]
    split_ifs with hk
    · exact (hXb k hk d b).2
    · show gsOf k ((X d.snd).2.2.2.2.2 d.fst b) = _
      rw [(hXc d b).2]
  have h0 : gs 0 = fun z => ⨅ r ∈ cornerIdx Cp z, (r : ℕ∞) := funext fun z => by simp [gs, gsBase]
  have h1 : gs 1 = fun z => ⨅ r ∈ cornerIdx Cp z, ((Cp.m - r : ℕ) : ℕ∞) := funext fun z => by simp [gs, gsBase]
  have h2 : gs 2 = flagVal Cp 0 := funext fun z => by simp [gs, gsBase]
  have h3 : gs 3 = flagVal Cp 1 := funext fun z => by simp [gs, gsBase]
  have h4 : gs 4 = fun z => if ∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, q.1.2.CornerA z then 0 else ⊤ := by
    rw [← lvG4_eq (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ]; funext z; simp [gs, gsOf]
  have h5 : gs 5 = fun z => if ∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, q.1.2.CornerB z then 0 else ⊤ := by
    rw [← lvG5_eq (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ]; funext z; simp [gs, gsOf]
  have h6 : gs 6 = fun z => if ∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, z = qEnd 0 q then 0 else ⊤ := by
    rw [← lvG6_eq (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ]; funext z; simp [gs, gsOf]
  have h7 : gs 7 = fun z => if ∃ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, z = qEnd 1 q then 0 else ⊤ := by
    rw [← lvG7_eq (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ]; funext z; simp [gs, gsOf]
  have h8 : gs 8 = fun z => ⨅ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, ⨅ (_ : z = qEnd 1 q),
      ((Nat.pair (rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1).1 (rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1).2 : ℕ) : ℕ∞) := funext fun z => by
    simp only [gs, gsOf, Nat.reduceLeDiff, Nat.reduceEqDiff, ↓reduceIte]
    rfl
  have hPay := hA₁ N (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ) hN (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M cc u₀ (fun w => valsOf (X w)) gs (fun q => rngA (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ q.1) hP hc hS hcut
    hD (fun x => hcb x.1.1) hM hc1 hcr (fun _ => rfl) (fun _ => rfl) ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).data_Γ ℓ modeL hostT _) hQM hM1 hmM hgs
    hvo hvi h0 h1 h2 h3 h4 h5 h6 h7 h8 (fun q hq => rngA_le (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ hq) hM8
  obtain ⟨⟨payT, payS, hpA, hpB, hpC, -⟩, hloc, hspec, hReq, -, -, hall⟩ := hPay
  set st₁ := A₁.run N.G (fun w => ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelIn hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M u₀ w, Cp.m, valsOf (X w))) T₁ with hst₁
  have hRl : (fun a => rr a (st₁ (hostOf a))) = lvR hN modeL hostT hhost hE K D M (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ := hReq
  have hbr := lvPay_bridge hN modeL hostT hhost hE K D M r₀ ℓ _ hRl payT payS
    (fun z => outT (((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN).ι (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV z))) (st₁ z.1.snd))
    (fun z => outS (((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN).ι (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV z))) (st₁ z.1.snd)) hpA hpB hpC
  refine ⟨payT, payS, hbr.2.2, fun w => ?_⟩
  -- the exchange
  have hb : ∀ x, lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ) x < 2 ^ b := fun x => lam_lt_pow (hcb x.1.1)
  have hmsg : ∀ u v, (X u).1.msg b v < 2 ^ Bw := fun u v => by
    rw [hX1 u]
    exact (DInfo.pack_lt _ ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).lamAt_lt _ hb _ _ _) ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).lamAt_lt _ hb _ _ _) ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).lamAt_lt _ hb _ _ _)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hB₁ : B₁.run N.G X T₁ = fun v => (X v, st₁ v) := by
    funext v
    simp only [B₁, run_keep, run_widen]
    rw [hin1]
  have hEx : ∀ v, Aex.run N.G (fun v => (X v, st₁ v)) 1 v =
      ((X v, st₁ v), ((X v).1.msg b, fun u => if N.G.Adj u v then some ((X u).1.msg b v) else none)) := by
    intro v
    show ((exchTo (Fin n) Bw).keep _).run N.G _ 1 v = _
    rw [run_keep]
    dsimp only
    rw [run_exchTo N.G _ hmsg]
  let Y : Fin n → OvIn n := fun v => mk v (Aex.run N.G (fun v => (X v, st₁ v)) 1 v)
  have hYv : ∀ v, Y v = mk v ((X v, st₁ v),
      ((X v).1.msg b, fun u => if N.G.Adj u v then some ((X u).1.msg b v) else none)) := fun v => by
    show mk v _ = _
    rw [hEx v]
  let j₀ : Fin n → OvIn n × ℕ × ℕ∞ := fun v => (Y v, 0, ⊤)
  let Xs : Fin 2 → Fin n → OvIn n := fun σ v => { Y v with sd := σ }
  -- the two sides
  have hstop : ∀ inp : Fin n → OvIn n, ((A₂.stopAt T₂).widen w₂).run N.G inp (T₂ + 1) =
      fun v => (T₂, A₂.run N.G inp T₂ v) := fun inp => by
    rw [run_widen, run_stopAt, Nat.min_eq_right (Nat.le_succ T₂)]
  have hD1 : iterData ((A₂.stopAt T₂).widen w₂) (T₂ + 1) gI uI N.G j₀ 1 =
      fun v => (Y v, 1, min ⊤ (val v (A₂.run N.G (Xs 0) T₂ v))) := by
    funext v
    simp only [iterData, hstop]
    rfl
  have hD2 : iterData ((A₂.stopAt T₂).widen w₂) (T₂ + 1) gI uI N.G j₀ 2 =
      fun v => (Y v, 2, min (min ⊤ (val v (A₂.run N.G (Xs 0) T₂ v))) (val v (A₂.run N.G (Xs 1) T₂ v))) := by
    funext v
    rw [iterData, hD1]
    simp only [hstop]
    rfl
  have hrun : (B₁.seq T₁ (fun _ s => s) (Aex.seq 1 (fun w y => (mk w y, 0, ⊤)) A₃)).run N.G X
      (T₁ + (1 + (2 * (T₂ + 1) + 0))) w =
      .inr (.inr (iterData ((A₂.stopAt T₂).widen w₂) (T₂ + 1) gI uI N.G j₀ 2 w, 0,
        ((A₂.stopAt T₂).widen w₂).run N.G (fun v => gI v (iterData ((A₂.stopAt T₂).widen w₂) (T₂ + 1) gI uI N.G j₀ 2 v)) 0 w)) := by
    rw [run_seq]
    dsimp only
    rw [hB₁, run_seq]
    exact congrArg (fun x => Sum.inr (Sum.inr x))
      (congrFun (run_iter ((A₂.stopAt T₂).widen w₂) gI uI N.G j₀ (by omega) 2 0 (by omega)) w)
  have hside : ∀ σ : Fin 2, ((val w (A₂.run N.G (Xs σ) T₂ w) : ℕ∞) : ℝ≥0∞) =
      ⨅ q ∈ (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).levelQ ℓ, ⨅ μ, ⨅ (_ : ovIn σ (decT (payT q)) (decS (payS q)) μ),
        ⨅ (_ : (q.1.2.κ1 μ).1.snd = w), Cp.lamD (Nat.cast ∘ cc) μ := by
    intro σ
    refine hA₂ N (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ) hN (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ σ (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M u₀ (Xs σ)
      (fun z => outT (((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN).ι (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV z))) (st₁ z.1.snd))
      (fun z => outS (((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).levelPad hN).ι (.inl ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).endV z))) (st₁ z.1.snd)) payT payS
      hP hc hS hcut hD hcr (fun _ => rfl) hcb hM hM1 hhost ((lvSeq hN modeL hostT hhost hE K D M r₀ ℓ).data_Γ ℓ modeL hostT _) hMl
      (fun v => ?_) (fun v => ?_) (fun _ => rfl) (fun a => ?_) (fun a => ?_) (fun a => ?_) (fun d β => ?_)
      (fun d β t => ?_) hpB (fun z hz _ => ?_) ?_ ?_ (fun At hAt => ?_) w
    · show (Y v).lv = _
      rw [hYv v]
      exact hX1 v
    · show (Y v).inn = _
      rw [hYv v]
      show LevelIn.inn b (fun u => if N.G.Adj u v then some ((X u).1.msg b v) else none) = _
      simp only [hX1]
      exact (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).inn_recv hN (lvLam cc (lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ)) M hb u₀ v
    · show (Y (hostOf a)).off a = _
      rw [hYv]
      exact (hloc a).1
    · show (Y (hostOf a)).tg a = _
      rw [hYv]
      show (flgO a (st₁ (hostOf a))).1 = _
      rw [(hloc a).2.1]
    · show (Y (hostOf a)).cf a = _
      rw [hYv]
      show cflO a (st₁ (hostOf a)) = _
      rw [(hloc a).2.2]
    · show (Y d.snd).pT d.fst β = _ ∧ (Y d.snd).pS d.fst β = _
      rw [hYv]
      show outT (idEquiv (cornerName (X d.snd).1.rot (X d.snd).1.own d.snd d.fst β)) (st₁ d.snd) = _ ∧
        outS (idEquiv (cornerName (X d.snd).1.rot (X d.snd).1.own d.snd d.fst β)) (st₁ d.snd) = _
      rw [hX1]
      exact ⟨congrArg (outT · _) ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).cornerName_eq hN d β), congrArg (outS · _) ((lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ ℓ) ℓ).cornerName_eq hN d β)⟩
    · show ((Y d.snd).k0 d.fst β t = true ↔ _) ∧ ((Y d.snd).k1 d.fst β t = true ↔ _)
      rw [hYv]
      exact hXk d β t
    · obtain ⟨q, hq, hg, -⟩ := hpC z hz
      exact ⟨q, hq, hg⟩
    · rw [← hReq]
      exact hspec
    · rw [← hReq]
      exact hpA
    · obtain ⟨kk, i1, i2, -, e1, e2, e3, -, -, -, -, e8, e9, e10, -⟩ := hall At hAt
      rw [← hReq]
      exact ⟨kk, i1, i2, e1, e2, e3, e8, e9, e10⟩
  rw [hrun, hD2]
  dsimp only
  simp only [ENat.toENNReal_min, top_inf_eq, hside]
  refine le_antisymm (le_iInf fun i => ?_) (le_min (iInf_le _ 0) (iInf_le _ 1))
  fin_cases i
  · exact min_le_left _ _
  · exact min_le_right _ _

end RData

end RotSystem

end SsspFlow
