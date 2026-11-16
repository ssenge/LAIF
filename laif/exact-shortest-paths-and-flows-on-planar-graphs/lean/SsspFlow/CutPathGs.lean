import SsspFlow.CutPathPiece
import SsspFlow.GHatFacePair
import SsspFlow.GHatLevelX0

/-!
# The base values of the cut path at the nodes

The base values `k = 0, 1, 2, 3` are least values over the pieces of the data of level `0`
(`RData.gsBase_eq_piece`). Each is one repetition of a fixed algorithm: the run on the pieces of
`RData.levelPieceVal_local`, whose value of a corner every node reads at the copy of the corner that
it hosts (`cornerName_eq`), then one round in which the head of every dart sends the two values of its
corners to the tail. Four repetitions give every node the base values of the corners of its darts.

* `X0In.withGs`, `X0In.gsIn`: the local data with other base values, and the input of a repetition.
* `gsRep`, `gsNew`, `gsAlg`: one repetition, the values it gives, and the four repetitions.
* `RData.gsAlg_spec`: after the four repetitions every node holds its local data with the base values.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest Cslib.Congest.Algorithm
open scoped ENNReal

namespace RotSystem

namespace X0In

variable {n : ℕ}

/-- The local data with other base values. -/
def withGs (x : X0In n) (G : ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)) : X0In n :=
  { x with gs := G }

@[simp] theorem withGs_gs (x : X0In n) (G : ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)) :
    (x.withGs G).gs = G := rfl

/-- The input of the run on the pieces for the base value `k`. -/
noncomputable def gsIn (k : ℕ) (x : X0In n) :
    LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)) :=
  (x.lvIn, (fun u b => RData.locOf x.m (x.kapO u b) k, fun u b => RData.locOf x.m (x.kapI u b) k))

end X0In

/-- A value capped below `M` from its least value with `M`. -/
theorem cap_of_min {M : ℕ} {o G : ℕ∞} (h : min (o : ℝ≥0∞) M = min (G : ℝ≥0∞) M)
    (hG : G = ⊤ ∨ G < M) : (if o < M then o else ⊤) = G := by
  have h' : min o (M : ℕ∞) = min G M := by
    apply ENat.toENNReal_inj.1
    rw [ENat.toENNReal_min, ENat.toENNReal_min, ENat.toENNReal_coe]
    exact h
  rcases hG with rfl | hG
  · rw [min_eq_right (le_top : ((M : ℕ) : ℕ∞) ≤ ⊤)] at h'
    split_ifs with ho
    · rw [min_eq_left ho.le] at h'
      exact absurd (h' ▸ ho) (lt_irrefl _)
    · rfl
  · rw [min_eq_left hG.le] at h'
    split_ifs with ho
    · rw [min_eq_left ho.le] at h'
      exact h'
    · rw [min_eq_right (not_lt.1 ho)] at h'
      exact absurd (h' ▸ hG) (lt_irrefl _)

section Phase

variable {n : ℕ} {σ : Type} {B : ℕ}
  (AP : Cslib.Congest.Algorithm (Fin n) (LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) σ B)
  (outP : Fin (n * (n * 21)) → σ → ℕ∞) (Tp : ℕ)

/-- The values of the corners of the darts into a node, read at the copies that it hosts. -/
noncomputable def gsVals (w : Fin n) (s : (LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) × σ) :
    (LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) × (Fin n → Bool → ℕ∞) :=
  (s.1, fun u b => RData.decV (RData.encV s.1.1.bnd
    (outP (RData.idEquiv (cornerName s.1.1.rot s.1.1.own w u b)) s.2)))

/-- **One repetition**: the run on the pieces, then one round in which the head of every dart sends the
two values of its corners to the tail. -/
noncomputable def gsRep :=
  (AP.keep (fun _ (j : LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) => j)).seq Tp
    (gsVals outP)
    ((exchTo (Fin n) B).keep
      (fun _ (p : (LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) × (Fin n → Bool → ℕ∞)) =>
        fun u => pairCode p.1.1.bnd (p.2 u false) (p.2 u true)))

/-- The base values that a node takes from the state of a repetition: the values received from the
heads of the darts out of it, and its own values of the darts into it. -/
def gsNew {α β γ : Type} (M : ℕ) :
    α ⊕ ((β × (Fin n → Bool → ℕ∞)) × (γ × (Fin n → Option ℕ))) →
      (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)
  | .inr p => (fun u b => match p.2.2 u with
      | some c => if b then (pairDec M c).2 else (pairDec M c).1
      | none => ⊤, p.1.2)
  | .inl _ => (fun _ _ => ⊤, fun _ _ => ⊤)

/-- **The four repetitions.** The data hold the number of the repetition and the local data, into which
each repetition writes its base values. -/
noncomputable def gsAlg :=
  (gsRep AP outP Tp).iter (Tp + 1) (fun _ (j : ℕ × X0In n) => X0In.gsIn j.1 j.2)
    (fun _ j s => (j.1 + 1, j.2.withGs fun k => if k = j.1 then gsNew j.2.bnd s else j.2.gs k))

/-- The data after `k` repetitions. -/
theorem gs_iterData (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → X0In n) :
    ∀ k, Cslib.Congest.Algorithm.iterData (gsRep AP outP Tp) (Tp + 1)
        (fun _ (j : ℕ × X0In n) => X0In.gsIn j.1 j.2)
        (fun _ j s => (j.1 + 1, j.2.withGs fun k => if k = j.1 then gsNew j.2.bnd s else j.2.gs k))
        G (fun w => (0, x w)) k =
      fun w => (k, (x w).withGs fun k' => if k' < k then
        gsNew (x w).bnd ((gsRep AP outP Tp).run G (fun v => X0In.gsIn k' (x v)) (Tp + 1) w)
        else (x w).gs k')
  | 0 => by
    funext w
    simp only [Nat.not_lt_zero, ite_false]
    rfl
  | k + 1 => by
    funext w
    rw [Cslib.Congest.Algorithm.iterData, gs_iterData G x k]
    show (k + 1, _) = (k + 1, _)
    refine congrArg (fun G' => (k + 1, (x w).withGs G')) (funext fun k' => ?_)
    by_cases h1 : k' = k
    · subst h1
      simp only [lt_add_one, ite_true]
      rfl
    · by_cases h2 : k' < k
      · simp only [h1, ite_false, h2, ite_true, show k' < k + 1 by omega, X0In.withGs_gs]
      · simp only [h1, ite_false, h2, show ¬ k' < k + 1 by omega, X0In.withGs_gs]

end Phase

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- **One repetition.** If the run on the pieces holds at every copy with an end the least value of `g`
over its piece, capped at `M`, and these least values are `⊤` or below `M`, then after one repetition
the tail and the head of every dart hold them for the two corners of the dart. -/
theorem gsRep_new {σ : Type} {B : ℕ}
    (AP : Cslib.Congest.Algorithm (Fin n) (LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) σ B)
    (outP : Fin (n * (n * 21)) → σ → ℕ∞) (Tp : ℕ) (lam : S.Tok → ℕ) (M : ℕ) (u₀ : S.hRot.Vertex)
    (g gt : N.G.Dart × Bool → ℕ∞) (vo vi : Fin n → Fin n → Bool → ℕ∞)
    (hAP : ∀ (v : S.hRot.Vertex) (hv : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy v)),
      min (outP ((S.levelPad hN).ι (.inl v))
        (AP.run N.G (fun w => (S.levelIn hN lam M u₀ w, (vo w, vi w))) Tp
          (hostOf ((S.levelPad hN).ι (.inl v)))) : ℝ≥0∞) M =
        min (((⨅ z, ⨅ (_ : S.pieceAt z = S.pieceOf ⟨S.vcopy v, hv⟩), g z : ℕ∞)) : ℝ≥0∞) M)
    (hg : ∀ z, (⨅ z', ⨅ (_ : S.pieceAt z' = S.pieceAt z), g z') = gt z) (hgt : ∀ z, gt z = ⊤ ∨ gt z < M)
    (hB : (M + 1) * (M + 1) ≤ 2 ^ B) (d : N.G.Dart) (b : Bool) :
    (gsNew M ((gsRep AP outP Tp).run N.G (fun w => (S.levelIn hN lam M u₀ w, (vo w, vi w))) (Tp + 1)
        d.fst)).1 d.snd b = gt (d, b) ∧
      (gsNew M ((gsRep AP outP Tp).run N.G (fun w => (S.levelIn hN lam M u₀ w, (vo w, vi w))) (Tp + 1)
        d.snd)).2 d.fst b = gt (d, b) := by
  set inp := fun w => (S.levelIn hN lam M u₀ w, (vo w, vi w)) with hinp
  set val : Fin n → Fin n → Bool → ℕ∞ := fun w u b => decV (encV M
    (outP (idEquiv (cornerName (N.rotList w) (S.dinfoAt w) w u b)) (AP.run N.G inp Tp w))) with hval
  have key : ∀ (d : N.G.Dart) b, val d.snd d.fst b = gt (d, b) := fun d b => by
    simp only [hval]
    rw [S.cornerName_eq hN d b, decV_encV_eq]
    have h := hAP (S.endV (d, b)) (S.endV_end (d, b))
    rw [S.pieceOf_endV, hg, S.hostOf_endV hN (d, b)] at h
    exact cap_of_min h (hgt _)
  have hmsg : ∀ u w, pairCode M (val u w false) (val u w true) < 2 ^ B := fun u w =>
    (pairCode_lt M _ _).trans_le hB
  have hrun : ∀ w, (gsRep AP outP Tp).run N.G inp (Tp + 1) w =
      .inr (((inp w, val w), (fun u => pairCode M (val w u false) (val w u true),
        fun u => if N.G.Adj u w then some (pairCode M (val u w false) (val u w true)) else none))) := by
    intro w
    simp only [gsRep]
    rw [run_seq]
    simp only [run_keep]
    exact congrArg Sum.inr (Prod.ext rfl (run_exchTo N.G _ hmsg w))
  have hc : ∀ z, (if gt z < M then gt z else ⊤) = gt z := fun z => by
    rcases hgt z with h | h
    · rw [h]; simp
    · simp [h]
  constructor
  · rw [hrun]
    simp only [gsNew, if_pos d.adj.symm, pairDec_code, key d, decV_encV_eq, hc]
    cases b <;> rfl
  · rw [hrun]
    exact key d b

theorem φOf_le {m k r : ℕ} (hr : r ≤ m) : φOf m k r ≤ m := by
  unfold φOf
  split_ifs
  · exact_mod_cast hr
  · exact_mod_cast Nat.sub_le m r
  · exact bot_le

theorem locIdx_top_or_le {N : Net (Fin n)} (C : N.toRot.dual.CutPath) (k : ℕ) (z : N.G.Dart × Bool) :
    locIdx C k z = ⊤ ∨ locIdx C k z ≤ C.m :=
  ENat.iInf_top_or_le fun _ => ENat.iInf_top_or_le fun hr => .inr (φOf_le hr.1)

open Classical Cslib.Congest.Algorithm in
/-- **The base values at the nodes.** Assuming the Exact SSSP bound, there is an algorithm of the message
model that starts from the local data of level `0` without base values and after
`4 (3 + C log^c n' · (12 D + 16))` rounds holds at every node the same local data with the base values
`k ≤ 3` of the corners of its darts, for every run on a shortest cut path with `m < M`. -/
theorem gsAlg_spec (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (ℕ × X0In n) σ
        (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (out : Fin n → σ → X0In n),
    ∀ (N : Net (Fin n)) (hN : ∀ u, ∃ w, N.G.Adj u w) (Cp : N.toRot.dual.CutPath) (cc : N.G.Dart → ℕ)
      {hR : N.toRot.dual.Planar} {hC : N.toRot.dual.Connected}
      {hgc : ∀ x, (Nat.cast ∘ cc : N.G.Dart → ℝ≥0∞) (N.toRot.dual.rev x) = (Nat.cast ∘ cc) x}
      (modeL hostT : N.G.Dart → Bool) (hhost : ∀ d, hostT (N.toRot.rev d) = !hostT d) (M : ℕ)
      (r₀ : CutPath.Run hR hC hgc Cp.Γ (Cp.liveOne (Nat.cast ∘ cc)) 0 Cp.m) (x : Fin n → X0In n)
      (w₀ : Fin n),
      N.toRot.Planar → N.toRot.Connected → N.DiamLE D →
      (∀ d, cc d ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K → Cp.m < M →
      (∀ w, (x w).me = w) → (∀ w, (x w).rot = N.rotList w) →
      (∀ d : N.G.Dart, (x d.fst).cw d.snd = cc d) → (∀ d : N.G.Dart, (x d.fst).mL d.snd = modeL d) →
      (∀ d : N.G.Dart, (x d.fst).hT d.snd = hostT d) → (∀ w, (x w).bnd = M) →
      (∀ w, (x w).m = Cp.m) → (∀ w, (x w).src = w₀) →
      (∀ (d : N.G.Dart) b t, ((((x d.snd).kapI d.fst b).1 t = true ↔ (d, b) = Cp.k 0 t) ∧
        (((x d.snd).kapI d.fst b).2 t = true ↔ (d, b) = Cp.k 1 t))) →
      (∀ (d : N.G.Dart) b t, ((((x d.fst).kapO d.snd b).1 t = true ↔ (d, b) = Cp.k 0 t) ∧
        (((x d.fst).kapO d.snd b).2 t = true ↔ (d, b) = Cp.k 1 t))) →
      (∀ w, (out w (A.run N.G (fun w => (0, x w))
          (4 * (1 + (1 + (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))))) w)).withGs (x w).gs = x w) ∧
      ∀ k, k ≤ 3 → ∀ (d : N.G.Dart) b,
        ((out d.fst (A.run N.G (fun w => (0, x w))
          (4 * (1 + (1 + (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))))) d.fst)).gs k).1 d.snd b =
            gsBase Cp k (d, b) ∧
        ((out d.snd (A.run N.G (fun w => (0, x w))
          (4 * (1 + (1 + (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))))) d.snd)).gs k).2 d.fst b =
            gsBase Cp k (d, b) := by
  obtain ⟨C, c, hC⟩ := levelPieceVal_local hE K
  refine ⟨C, c, fun n D => ?_⟩
  obtain ⟨σ, AP, outP, hAP⟩ := hC n D
  set Tp := 1 + (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16)) with hTp
  refine ⟨_, gsAlg AP outP Tp, fun _ s => s.1.2, ?_⟩
  intro N hN Cp cc hR hC hgc modeL hostT hhost M r₀ x w₀ hP hc hD hcb hM hmM hme hrot hcw hmL hhT hb hm hsrc
    hkI hkO
  have hrun := run_iter (gsRep AP outP Tp) (fun _ (j : ℕ × X0In n) => X0In.gsIn j.1 j.2)
    (fun _ j s => (j.1 + 1, j.2.withGs fun k => if k = j.1 then gsNew j.2.bnd s else j.2.gs k))
    N.G (fun w => (0, x w)) (Nat.succ_pos Tp) 4 0 (Nat.succ_pos Tp)
  rw [gs_iterData] at hrun
  have hT4 : 4 * (1 + Tp) = 4 * (Tp + 1) + 0 := by ring
  have hst : ∀ w, ((gsAlg AP outP Tp).run N.G (fun w => (0, x w)) (4 * (1 + Tp)) w).1.2 =
      (x w).withGs fun k' => if k' < 4 then
        gsNew (x w).bnd ((gsRep AP outP Tp).run N.G (fun v => X0In.gsIn k' (x v)) (Tp + 1) w)
        else (x w).gs k' := fun w => by
    rw [hT4]
    exact congrArg (fun f => (f w).1.2) hrun
  refine ⟨fun w => by beta_reduce; rw [hst]; rfl, fun k hk d b => ?_⟩
  beta_reduce
  simp only [hst, X0In.withGs_gs, show k < 4 by omega, ite_true, hb]
  -- the data of level `0`
  set S := lvS modeL hostT hhost (lvSeq hN modeL hostT hhost hE K D M r₀ 0) 0 with hS
  have hincS : ∀ d, d ∈ S.inc ↔ (d, false) ∈ Cp.Γ := fun d => by
    simp [hS, lvS, CutPath.Run.data, RData.ofCorners, CutPath.Run.steps_zero]
  have hcutS : ∀ c, c ∈ S.cut ↔ (c, true) ∈ Cp.Γ := fun c => by
    simp [hS, lvS, CutPath.Run.data, RData.ofCorners, CutPath.Run.steps_zero]
  have hΓ : S.Γ = Cp.Γ := by
    ext ⟨d', b'⟩
    cases b'
    · rw [S.mem_Γ_false, hincS]
    · rw [S.mem_Γ_true, hcutS]
  have hNC : S.NoConflict := CutPath.Run.noConflict _ 0 modeL hostT _
  have hcut : S.cut.card ≤ 3 := by
    refine (Finset.card_le_card (t := {Cp.cs, Cp.ct}) fun c hc => ?_).trans
      (Finset.card_le_two.trans (by norm_num))
    rcases CutPath.Run.cut_data _ 0 modeL hostT _ hc with rfl | rfl <;> simp
  have hL := lvIn_of_local hN modeL hostT hhost hE K D M r₀ w₀ x hme hrot hcw hmL hhT hb hm hsrc hkO
  set vo : Fin n → Fin n → Bool → ℕ∞ := fun v u b => locOf (x v).m ((x v).kapO u b) k with hvo
  set vi : Fin n → Fin n → Bool → ℕ∞ := fun v u b => locOf (x v).m ((x v).kapI u b) k with hvi
  have hin : (fun v => X0In.gsIn k (x v)) = fun w => (S.levelIn hN (lvLam cc S) M (S.starV hN w₀) w, (vo w, vi w)) :=
    funext fun v => Prod.ext (hL v) rfl
  have hvo' : ∀ (d : N.G.Dart) b, vo d.fst d.snd b = locIdx Cp k (d, b) := fun d b => by
    simp only [hvo, hm]; exact locOf_eq Cp (hkO d b) k
  have hvi' : ∀ (d : N.G.Dart) b, vi d.snd d.fst b = locIdx Cp k (d, b) := fun d b => by
    simp only [hvi, hm]; exact locOf_eq Cp (hkI d b) k
  have hg : ∀ z, locIdx Cp k z = ⊤ ∨ locIdx Cp k z ≤ (n * (n * 21) + 2) ^ K := fun z => by
    rcases locIdx_top_or_le Cp k z with h | h
    · exact .inl h
    · refine .inr (h.trans ?_)
      exact_mod_cast (hmM.trans_le hM).le
  have hAP' := hAP N S hN (lvLam cc S) M (S.starV hN w₀) (locIdx Cp k) vo vi hP hc hNC hcut hD
    (fun y => hcb y.1.1) (by omega) hM hg hvo' hvi'
  have hgt : ∀ z, gsBase Cp k z = ⊤ ∨ gsBase Cp k z < M := fun z => by
    rw [← gsBase_eq_piece S Cp hΓ hk z]
    rcases ENat.iInf_top_or_le (B := (Cp.m : ℕ∞)) (g := fun z' => ⨅ (_ : S.pieceAt z' = S.pieceAt z),
        locIdx Cp k z') (fun z' => ENat.iInf_top_or_le fun _ => locIdx_top_or_le Cp k z') with h | h
    · exact .inl h
    · exact .inr (h.trans_lt (by exact_mod_cast hmM))
  have hMb : M < 2 ^ (K * logN (n * (n * 21)) + 1) := lam_lt_pow hM
  have hB : (M + 1) * (M + 1) ≤ 2 ^ (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)) := by
    have e : (M + 1) * (M + 1) ≤ 2 ^ (K * logN (n * (n * 21)) + 1) * 2 ^ (K * logN (n * (n * 21)) + 1) :=
      Nat.mul_le_mul hMb hMb
    rw [← pow_add] at e
    exact e.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [hin]
  exact S.gsRep_new hN AP outP Tp (lvLam cc S) M (S.starV hN w₀) (locIdx Cp k) (gsBase Cp k) vo vi hAP'
    (gsBase_eq_piece S Cp hΓ hk) hgt hB d b

end RData

end RotSystem

end SsspFlow
