import SsspFlow.GHatFaceData
import SsspFlow.GHatPieceRun
import SsspFlow.GHatCornerId
import SsspFlow.GHatLevelAdvance
import SsspFlow.GHatLevelI12Spec

/-!
# The least value over a face, as one algorithm

The data with no incision have the faces as their pieces (`RData.faceData_pieceAt_iff`). Their inputs
are computed at each node from the inputs of any level. So a value of each corner, known at the head of
its dart, gives in one algorithm the least value over the corners at the face of each corner: one round
in which the head of each dart sends the two values of its corners to the tail, then the run on the
pieces of the data with no incision.

* `pairCode`, `pairDec`: two values below `M` as one number.
* `LevelIn.toFace`: the inputs of the data with no incision, from the inputs of a level.
* `RData.toFace_levelIn`: they are the inputs of the data with no incision.
* `RData.facePair_local`: the algorithm and its output at every corner, capped at `M`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

/-- Two values below `M` as one number. -/
noncomputable def pairCode (M : ℕ) (v0 v1 : ℕ∞) : ℕ := RData.encV M v0 + (M + 1) * RData.encV M v1

/-- The two values of a number. -/
def pairDec (M : ℕ) (x : ℕ) : ℕ∞ × ℕ∞ := (RData.decV (x % (M + 1)), RData.decV (x / (M + 1)))

theorem pairDec_code (M : ℕ) (v0 v1 : ℕ∞) :
    pairDec M (pairCode M v0 v1) = (RData.decV (RData.encV M v0), RData.decV (RData.encV M v1)) := by
  have h0 : RData.encV M v0 < M + 1 := Nat.lt_succ_of_le (RData.encV_le M v0)
  unfold pairDec pairCode
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0, Nat.add_mul_div_left _ _ (Nat.succ_pos M),
    Nat.div_eq_of_lt h0, zero_add]

theorem pairCode_lt (M : ℕ) (v0 v1 : ℕ∞) : pairCode M v0 v1 < (M + 1) * (M + 1) := by
  have h0 := RData.encV_le M v0
  have h1 := RData.encV_le M v1
  unfold pairCode
  nlinarith

/-- A value capped at `M`: itself below `M`, `⊤` otherwise. -/
theorem decV_encV_eq (M : ℕ) (v : ℕ∞) :
    RData.decV (RData.encV M v) = if v < M then v else ⊤ := by
  split_ifs with h
  · exact RData.decV_encV (.inr h)
  · simp [RData.encV, RData.decV, h]

/-- Capping the values at `M` keeps their least value capped at `M`. -/
theorem min_iInf_cap {ι : Sort*} {P : ι → Prop} (a : ι → ℕ∞) (M : ℕ) :
    min (⨅ i, ⨅ (_ : P i), ((if a i < M then a i else ⊤ : ℕ∞) : ℝ≥0∞)) M =
      min (⨅ i, ⨅ (_ : P i), (a i : ℝ≥0∞)) M := by
  refine le_antisymm (le_min (le_iInf₂ fun i hi => ?_) (min_le_right _ _))
    (le_min (le_iInf₂ fun i hi => ?_) (min_le_right _ _))
  · by_cases h : a i < M
    · exact (min_le_left _ _).trans (iInf₂_le_of_le i hi (by rw [if_pos h]))
    · refine (min_le_right _ _).trans ?_
      rw [← ENat.toENNReal_coe]
      exact ENat.toENNReal_le.2 (not_lt.1 h)
  · by_cases h : a i < M
    · rw [if_pos h]
      exact (min_le_left _ _).trans (iInf₂_le i hi)
    · rw [if_neg h]
      exact le_top

namespace LevelIn

variable {n : ℕ}

/-- **The inputs of the data with no incision**, from the inputs of a level: no dart is incised and
no corner is cut, the token lengths are `0`, and the source is the star centre of the host of the
source. -/
def toFace (j : LevelIn n) : LevelIn n :=
  ⟨j.me, j.rot, fun u => ⟨false, false, (j.own u).modeL, (j.own u).hostT, false⟩, fun _ _ => 0, j.bnd,
    RData.idEquiv (RData.hostOf j.src, RData.hostOf j.src, 0)⟩

end LevelIn

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- **The inputs of the data with no incision are local.** -/
theorem toFace_levelIn (hh : ∀ d, S.hostT (N.toRot.rev d) = !S.hostT d) (lam : S.Tok → ℕ) (M : ℕ)
    (u₀ : S.hRot.Vertex) (w : Fin n) :
    (S.levelIn hN lam M u₀ w).toFace = (faceData S.modeL S.hostT hh).levelIn hN (fun _ => 0) M
      ((faceData S.modeL S.hostT hh).starV hN (hostOf ((S.levelPad hN).ι (.inl u₀)))) w := by
  unfold LevelIn.toFace levelIn
  rw [starV_name]
  congr 1
  · funext u
    unfold dinfoAt
    split_ifs with h
    · simp [dinfo, MovB, h, faceData]
    · simp [h]; rfl
  · funext u l
    unfold lamAt
    split_ifs <;> rfl

open Cslib.Congest.Algorithm in
/-- **The least value over a face, as one algorithm.** Assuming the Exact SSSP bound, one algorithm of
the message model on `N`, fixed before the network, starts from the inputs of a level and, at each node
`w`, the values `va w u b` of the corners `((u, w), b)` of the darts into it. After
`3 + C log^c n' · (12 D + 16)` rounds the head of every dart holds, for each of its two corners, the
least value over the corners at the face of that corner, capped at `M`. -/
theorem facePair_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LevelIn n × (Fin n → Bool → ℕ∞)) σ
        (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (out : Fin n → σ → Fin n → Bool → ℕ∞),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex) (hh : ∀ d, S.hostT (N.toRot.rev d) = !S.hostT d)
      (a : N.G.Dart × Bool → ℕ∞) (va : Fin n → Fin n → Bool → ℕ∞),
      N.toRot.Planar → N.toRot.Connected → N.DiamLE D → 1 ≤ M → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ (d : N.G.Dart) b, va d.snd d.fst b = a (d, b)) →
      ∀ (d : N.G.Dart) (b : Bool),
        min (out d.snd (A.run N.G (fun w => (S.levelIn hN lam M u₀ w, va w))
          (1 + (1 + (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16)))) d.snd) d.fst b : ℝ≥0∞) M =
          min (⨅ z, ⨅ (_ : N.toRot.dual.tail z.1 = N.toRot.dual.tail d), (a z : ℝ≥0∞)) M := by
  obtain ⟨C, c, hP⟩ := levelPieceVal_local hE K
  refine ⟨C, c, fun n D => ?_⟩
  set b := K * logN (n * (n * 21)) + 1 with hb
  set Bw := 4 * (C * logN (n * (n * 21)) ^ c) + (3 * b + 5) with hBw
  obtain ⟨σP, AP, outP, hAP⟩ := hP n D
  let J₀ := LevelIn n × (Fin n → Bool → ℕ∞)
  let A₀ := (exchTo (Fin n) Bw).keep (fun _ (x : J₀) => fun u => pairCode x.1.bnd (x.2 u false) (x.2 u true))
  let f₁ : Fin n → J₀ × ((Fin n → ℕ) × (Fin n → Option ℕ)) →
      LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)) := fun _ s =>
    (s.1.1.toFace, (fun u β => match s.2.2 u with
        | some x => if β then (pairDec s.1.1.bnd x).2 else (pairDec s.1.1.bnd x).1
        | none => ⊤,
      fun u β => decV (encV s.1.1.bnd (s.1.2 u β))))
  let A₂ := AP.keep (fun _ (x : LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) => x)
  refine ⟨_, A₀.seq 1 f₁ A₂, fun w s u β => match s with
    | .inr s' => outP (idEquiv (cornerName s'.1.1.rot s'.1.1.own w u β)) s'.2
    | .inl _ => ⊤, ?_⟩
  intro N S hN lam M u₀ hh a va hPl hc hD hM1 hM hva d β
  set S' := faceData S.modeL S.hostT hh with hS'
  set u₀' := S'.starV hN (hostOf ((S.levelPad hN).ι (.inl u₀)))
  have hMb : M < 2 ^ b := lam_lt_pow hM
  have hmsg : ∀ u v, pairCode (S.levelIn hN lam M u₀ u).bnd (va u v false) (va u v true) < 2 ^ Bw := fun u v => by
    show pairCode M _ _ < _
    refine (pairCode_lt M _ _).trans_le ?_
    have e : (M + 1) * (M + 1) ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul hMb hMb
    rw [← pow_add] at e
    exact e.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  let vo : Fin n → Fin n → Bool → ℕ∞ := fun v u β =>
    if N.G.Adj u v then decV (encV M (va u v β)) else ⊤
  let vi : Fin n → Fin n → Bool → ℕ∞ := fun v u β => decV (encV M (va v u β))
  have hinp : (fun v => f₁ v (A₀.run N.G (fun w => (S.levelIn hN lam M u₀ w, va w)) 1 v)) =
      fun v => (S'.levelIn hN (fun _ => 0) M u₀' v, (vo v, vi v)) := by
    funext v
    show f₁ v (((exchTo (Fin n) Bw).keep _).run N.G _ 1 v) = _
    rw [run_keep]
    dsimp only
    rw [run_exchTo N.G _ hmsg]
    simp only [f₁]
    rw [S.toFace_levelIn hN hh lam M u₀ v]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    funext u β
    have e1 : (S.levelIn hN lam M u₀ v).bnd = M := rfl
    have e2 : (S.levelIn hN lam M u₀ u).bnd = M := rfl
    simp only [vo]
    by_cases h : N.G.Adj u v
    · simp only [h, if_true, e1, e2, pairDec_code]
      cases β <;> rfl
    · simp only [h, if_false]
  have hrun : (A₀.seq 1 f₁ A₂).run N.G (fun w => (S.levelIn hN lam M u₀ w, va w))
      (1 + (1 + (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16)))) d.snd =
      .inr ((S'.levelIn hN (fun _ => 0) M u₀' d.snd, (vo d.snd, vi d.snd)),
        AP.run N.G (fun v => (S'.levelIn hN (fun _ => 0) M u₀' v, (vo v, vi v)))
          (1 + (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))) d.snd) := by
    rw [run_seq, hinp]
    simp only [A₂, run_keep]
  rw [hrun]
  dsimp only
  have hname := S'.cornerName_eq hN d β
  have hhost := S'.hostOf_endV hN (d, β)
  have key := hAP N S' hN (fun _ => 0) M u₀' (fun z => decV (encV M (a z))) vo vi hPl hc
    (faceData_noConflict _ _ _) (faceData_cut_card _ _ _) hD (fun _ => Nat.zero_le _) hM1 hM
    (fun z => by
      rw [decV_encV_eq]
      split_ifs with h
      · refine .inr ?_
        exact h.le.trans (by exact_mod_cast hM)
      · exact .inl rfl)
    (fun d' β' => by
      simp only [vo]
      rw [if_pos d'.adj.symm, hva])
    (fun d' β' => by simp only [vi]; rw [hva])
    (S'.endV (d, β)) (S'.endV_end _)
  rw [hhost, S'.pieceOf_endV] at key
  simp only [levelIn]
  rw [hname]
  refine key.trans ?_
  simp only [decV_encV_eq, ENat.toENNReal_iInf]
  rw [min_iInf_cap]
  congr 1
  exact iInf_congr fun z => iInf_congr_Prop (faceData_pieceAt_iff S.modeL S.hostT hh z (d, β)) fun _ => rfl

end RData

end RotSystem

end SsspFlow
