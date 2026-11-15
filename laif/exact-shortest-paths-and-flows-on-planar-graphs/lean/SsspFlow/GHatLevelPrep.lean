import SsspFlow.GHatLevelFlags

/-!
# The inputs of the run of the nodes of a level, as one algorithm

One algorithm of the message model runs the run on the pieces six times, on the values of the corners
for the least index of the cut path, the greatest index, the flags of the corners for `0` and `1`, and
the flags of the corners of the two sides of the annuli of a list. Then one round of exchange gives
every node the records of the darts into it. From these each node computes, at the identifiers it
hosts, the inputs of `RData.levelNode_run`: the offsets of the sources, the flags of the targets and of
the nodes, the two indices and the flags of the corners of the sides.

* `RData.cpId_host`: the copy of an identifier is hosted with it.
* `RData.PrepData`, `RData.iterData_prep`: the data after `k` runs on the pieces.
* `RData.levelPrep_local`: the inputs of the run of the nodes of a level from one algorithm.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

include hN in
/-- **The copy of an identifier is hosted with it.** -/
theorem cpId_host (a : Fin (n * (n * 21))) :
    hostOf (cpIdL (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a))
      (hostOf a) ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)) = hostOf a := by
  unfold cpIdL
  have hw : ∀ (w u : Fin n) (k : Fin 21), hostOf (idEquiv (w, u, k)) = w := fun w u k => by
    unfold hostOf; rw [Equiv.symm_apply_apply]
  by_cases hr : rawReal (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a))
      (hostOf a) ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2) = true
  · rw [ite_eq_left hr]
    by_cases hk : ((idEquiv.symm a).2.2).val < 5
    · rw [ite_eq_left hk, hw]
    · rw [ite_eq_right hk]
      obtain ⟨y, hy⟩ := (S.real_iff hN a).1 hr
      rcases y with v | x
      · exfalso
        apply hk
        rw [← hy, S.levelPad_ι, Equiv.symm_apply_apply]
        exact N.nameC_kind _
      · rw [← S.levelNet_rotList_raw hN a, ← hy, S.levelNet_rotList_dart]
        show hostOf ((S.levelPad hN).ι (.inl (S.hRot.tail x))) = hostOf ((S.levelPad hN).ι (.inr x))
        rw [S.hostOf_ι, S.hostOf_ι]
        rfl
  · rw [ite_eq_right hr, hw]

/-- The data of the iterated runs on the pieces: the inputs of the level, the values of the corners
for each run, the number of finished runs and the outputs of the finished runs. -/
abbrev PrepData (n : ℕ) : Type :=
  LevelIn n × (ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)) × ℕ × (ℕ → Fin (n * (n * 21)) → ℕ∞)

/-- The inputs of the next run on the pieces. -/
def prepIn {n : ℕ} (_w : Fin n) (j : PrepData n) : LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)) :=
  (j.1, j.2.1 j.2.2.1)

/-- The data after a run on the pieces with outputs `o`. -/
def prepNext {n : ℕ} {σ : Type} (o : Fin (n * (n * 21)) → σ → ℕ∞) (_w : Fin n) (j : PrepData n) (s : σ) :
    PrepData n :=
  (j.1, j.2.1, j.2.2.1 + 1, Function.update j.2.2.2 j.2.2.1 fun a => o a s)

/-- **The data after `k` runs on the pieces.** -/
theorem iterData_prep {B : ℕ} {σ : Type} (A : Cslib.Congest.Algorithm (Fin n)
      (LevelIn n × ((Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) σ B)
    (o : Fin (n * (n * 21)) → σ → ℕ∞) (T : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lin : Fin n → LevelIn n) (vals : Fin n → ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)) :
    ∀ k, Cslib.Congest.Algorithm.iterData A T prepIn (prepNext o) G
        (fun w => (lin w, vals w, 0, fun _ _ => ⊤)) k =
      fun w => (lin w, vals w, k, fun i => if i < k then fun a => o a (A.run G (fun w' => (lin w', vals w' i)) T w)
        else fun _ => ⊤)
  | 0 => by
    funext w
    simp [Cslib.Congest.Algorithm.iterData]
  | k + 1 => by
    have ih := iterData_prep A o T G lin vals k
    funext w
    show prepNext o w (Cslib.Congest.Algorithm.iterData A T prepIn (prepNext o) G _ k w)
      (A.run G (fun w => prepIn w (Cslib.Congest.Algorithm.iterData A T prepIn (prepNext o) G _ k w)) T w) = _
    rw [ih]
    simp only [prepNext, prepIn]
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_))
    dsimp only
    funext i
    by_cases hik : i = k
    · subst hik
      simp
    · rw [Function.update_of_ne hik]
      by_cases hi : i < k
      · rw [ite_eq_left hi, ite_eq_left (by omega)]
      · rw [ite_eq_right hi, ite_eq_right (by omega)]


open Classical Cslib.Congest.Algorithm in
/-- **The inputs of the run of the nodes of a level, as one algorithm.** There are constants `C` and
`c` such that for all `n` and `D` one algorithm of the message model on `N`, fixed before the network,
starts from the inputs of a level and, at each node, values at the corners of the darts out of it and
into it, numbered `0` to `7`. Let these be the least index and `m` minus the greatest index of the cut
path at a corner, the flags of the corners for `0` and `1`, the flags of the corners of the two sides
of the annuli of a list `Q`, and the flags of their source and target corners. After
`6 (2 + C log^c n' (12 D + 16)) + 1` rounds each node holds, at the identifiers it hosts, inputs of the
run of the nodes of a level for `Q`: the least index and `m` minus the greatest index at the piece of
each copy, `⊤` away from copies, the offsets of the sources, the flags of the targets and of the nodes,
and the flags of the corners of the sides. -/
theorem levelPrep_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n)
        (LevelIn n × (ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) σ
      (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (off : Fin n → σ → Fin (n * (n * 21)) → ℕ∞)
      (flg : Fin n → σ → Fin (n * (n * 21)) → Bool × Bool × Bool)
      (ixL jxL : Fin n → σ → Fin (n * (n * 21)) → ℕ∞)
      (cfl : Fin n → σ → Fin (n * (n * 21)) → Bool × Bool),
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex) (vals : Fin n → ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))
      (gs : ℕ → N.G.Dart × Bool → ℕ∞) {Cp : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}
      (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live g Γ') × ℕ)),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → 1 ≤ M → M ≤ (n * (n * 21) + 2) ^ K → Cp.m < M →
      (∀ k z, gs k z = ⊤ ∨ gs k z ≤ (n * (n * 21) + 2) ^ K) →
      (∀ k (d : N.G.Dart) b, (vals d.fst k).1 d.snd b = gs k (d, b)) →
      (∀ k (d : N.G.Dart) b, (vals d.snd k).2 d.fst b = gs k (d, b)) →
      gs 0 = (fun z => ⨅ r ∈ cornerIdx Cp z, (r : ℕ∞)) →
      gs 1 = (fun z => ⨅ r ∈ cornerIdx Cp z, ((Cp.m - r : ℕ) : ℕ∞)) →
      gs 2 = flagVal Cp 0 → gs 3 = flagVal Cp 1 →
      gs 4 = (fun z => if ∃ q ∈ Q, q.1.2.CornerA z then 0 else ⊤) →
      gs 5 = (fun z => if ∃ q ∈ Q, q.1.2.CornerB z then 0 else ⊤) →
      gs 6 = (fun z => if ∃ q ∈ Q, z = qEnd 0 q then 0 else ⊤) →
      gs 7 = (fun z => if ∃ q ∈ Q, z = qEnd 1 q then 0 else ⊤) →
      let st := A.run N.G (fun w => (S.levelIn hN lam M u₀ w, vals w))
        (6 * (1 + (1 + C * logN (n * (n * 21)) ^ c * (12 * D + 16))) + 1)
      (∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) →
        ixL (hostOf z) (st (hostOf z)) z = ⊤ ∧ jxL (hostOf z) (st (hostOf z)) z = ⊤) ∧
      (∀ z, (ixL (hostOf z) (st (hostOf z)) z = ⊤ ∨
          ixL (hostOf z) (st (hostOf z)) z ≤ (n * (n * 21) + 2) ^ K) ∧
        (jxL (hostOf z) (st (hostOf z)) z = ⊤ ∨
          jxL (hostOf z) (st (hostOf z)) z ≤ (n * (n * 21) + 2) ^ K)) ∧
      (∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
        ixL (hostOf ((S.levelPad hN).ι (.inl u))) (st (hostOf ((S.levelPad hN).ι (.inl u))))
          ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx Cp (⟨S.vcopy u, hu⟩ : S.EndCopy), (r' : ℕ∞)) ∧
      (∀ u (hu : ∃ x : S.Tok, S.IsEnd x.1 (S.vcopy u)),
        jxL (hostOf ((S.levelPad hN).ι (.inl u))) (st (hostOf ((S.levelPad hN).ι (.inl u))))
          ((S.levelPad hN).ι (.inl u)) = ⨅ r' ∈ S.cutIdx Cp (⟨S.vcopy u, hu⟩ : S.EndCopy), ((Cp.m - r' : ℕ) : ℕ∞)) ∧
      (∀ a, off (hostOf a) (st (hostOf a)) a = S.srcOff hN Q a) ∧
      (∀ a, flg (hostOf a) (st (hostOf a)) a =
        (S.tgtFlag hN Q a, decide (S.nodeFlag hN Cp 0 a), decide (S.nodeFlag hN Cp 1 a))) ∧
      (∀ a, cfl (hostOf a) (st (hostOf a)) a =
        (decide (S.cornerFlag hN Q (fun A c => A.2.CornerA c) a),
          decide (S.cornerFlag hN Q (fun A c => A.2.CornerB c) a))) := by
  obtain ⟨Cq, cq, hP⟩ := levelPieceVal_all hE K
  refine ⟨Cq, cq, fun n D => ?_⟩
  set b := K * logN (n * (n * 21)) + 1
  set Bw := 4 * (Cq * logN (n * (n * 21)) ^ cq) + (3 * b + 5)
  set Tp := 1 + (1 + Cq * logN (n * (n * 21)) ^ cq * (12 * D + 16))
  obtain ⟨σP, AP, outP, hAP⟩ := hP n D
  let AI := (AP.iter Tp prepIn (prepNext outP)).keep
    (fun _ (i : LevelIn n × (ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) =>
      ((i.1, i.2, 0, fun _ _ => ⊤) : PrepData n))
  let Aex := (exchTo (Fin n) Bw).keep (fun _ (j : PrepData n) => j.1.msg b)
  let cpI := fun (w : Fin n) (s' : PrepData n × ((Fin n → ℕ) × (Fin n → Option ℕ))) (a : Fin (n * (n * 21))) =>
    cpIdL s'.1.1.rot s'.1.1.own (LevelIn.inn b s'.2.2) w ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)
  let isC := fun (w : Fin n) (s' : PrepData n × ((Fin n → ℕ) × (Fin n → Option ℕ))) (a : Fin (n * (n * 21))) =>
    isCopyL s'.1.1.rot s'.1.1.own (LevelIn.inn b s'.2.2) w ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)
  refine ⟨_, AI.seq (6 * Tp) (fun _ s => s.2.1) Aex,
    fun w s a => match s with
      | .inr s' => u0Test b w s'.1.1 (s'.1.2.1 6).2 s'.2.2 a
      | .inl _ => ⊤,
    fun w s a => match s with
      | .inr s' => (decide (u0Test b w s'.1.1 (s'.1.2.1 7).2 s'.2.2 a = 0),
          decide (s'.1.2.2.2 2 (cpI w s' a) = 0), decide (s'.1.2.2.2 3 (cpI w s' a) = 0))
      | .inl _ => (false, false, false),
    fun w s a => match s with
      | .inr s' => ixOf s'.1.1.bnd (isC w s' a) (s'.1.2.2.2 0 a)
      | .inl _ => ⊤,
    fun w s a => match s with
      | .inr s' => ixOf s'.1.1.bnd (isC w s' a) (s'.1.2.2.2 1 a)
      | .inl _ => ⊤,
    fun w s a => match s with
      | .inr s' => (decide (s'.1.2.2.2 4 (cpI w s' a) = 0), decide (s'.1.2.2.2 5 (cpI w s' a) = 0))
      | .inl _ => (false, false), ?_⟩
  intro N S hN lam M u₀ vals gs Cp g Q hP' hc hS hcut hD hlam hM1 hM hmM hg hvo hvi h0 h1 h2 h3 h4 h5 h6 h7
  have hb : ∀ x, lam x < 2 ^ b := fun x => lam_lt_pow (hlam x)
  have hmsg : ∀ u w, (S.levelIn hN lam M u₀ u).msg b w < 2 ^ Bw := fun u w =>
    (DInfo.pack_lt _ (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _) (S.lamAt_lt lam hb _ _ _)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hTp : 0 < Tp := by omega
  let outK := fun (k : ℕ) (a : Fin (n * (n * 21))) =>
    outP a (AP.run N.G (fun w => (S.levelIn hN lam M u₀ w, vals w k)) Tp (hostOf a))
  have hpc : ∀ k v, min (outK k ((S.levelPad hN).ι (.inl v)) : ℝ≥0∞) M =
      min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ER (S.vcopy u) (S.vcopy v)),
        ((S.copyVal (gs k) (S.vcopy u) : ℕ∞) : ℝ≥0∞)) M := fun k v =>
    hAP N S hN lam M u₀ (gs k) (fun w => (vals w k).1) (fun w => (vals w k).2) hP' hc hS hcut hD hlam hM1 hM
      (hg k) (hvo k) (hvi k) v
  have hI : (fun v => ((AI.run N.G (fun w => (S.levelIn hN lam M u₀ w, vals w)) (6 * Tp) v).2.1 :
      PrepData n)) = fun v => (S.levelIn hN lam M u₀ v, vals v, 6, fun i => if i < 6 then
        fun a => outP a (AP.run N.G (fun w' => (S.levelIn hN lam M u₀ w', vals w' i)) Tp v) else fun _ => ⊤) := by
    funext v
    show (((AP.iter Tp prepIn (prepNext outP)).keep _).run N.G _ (6 * Tp) v).2.1 = _
    rw [run_keep]
    dsimp only
    have e := run_iter AP prepIn (prepNext outP) N.G
      (fun w => ((S.levelIn hN lam M u₀ w, vals w, 0, fun _ _ => ⊤) : PrepData n)) hTp 6 0 hTp
    rw [show 6 * Tp = 6 * Tp + 0 from rfl, e, iterData_prep]
  have hst : (AI.seq (6 * Tp) (fun _ s => s.2.1) Aex).run N.G (fun w => (S.levelIn hN lam M u₀ w, vals w))
      (6 * Tp + 1) = fun w => .inr ((S.levelIn hN lam M u₀ w, vals w, 6, fun i => if i < 6 then
        fun a => outP a (AP.run N.G (fun w' => (S.levelIn hN lam M u₀ w', vals w' i)) Tp w) else fun _ => ⊤),
        ((S.levelIn hN lam M u₀ w).msg b, S.levelRecv hN lam M b u₀ w)) := by
    rw [run_seq]
    funext w
    rw [hI]
    show Sum.inr (((exchTo (Fin n) Bw).keep _).run N.G _ 1 w) = _
    rw [run_keep]
    dsimp only
    rw [run_exchTo N.G _ hmsg]
    rfl
  intro st
  have hst' : st = _ := hst
  rw [hst']
  have hinn : ∀ w, LevelIn.inn b (S.levelRecv hN lam M b u₀ w) = fun u => S.dinfoAt u w :=
    S.inn_recv hN lam M hb u₀
  simp only [isC, cpI, hinn, Nat.reduceLT, ↓reduceIte]
  have hix := S.ixOf_spec hN Cp M (outK 0) (fun r => (r : ℕ∞)) (fun r hr => by exact_mod_cast hr) hmM
    (by rw [← h0]; exact hpc 0)
  have hjx := S.ixOf_spec hN Cp M (outK 1) (fun r => ((Cp.m - r : ℕ) : ℕ∞))
    (fun r _ => by exact_mod_cast Nat.sub_le _ _) hmM (by rw [← h1]; exact hpc 1)
  have hcp : ∀ k a, outK k (cpIdL (N.rotList (hostOf a)) (S.dinfoAt (hostOf a))
      (fun u => S.dinfoAt u (hostOf a)) (hostOf a) ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)) =
      outP (cpIdL (N.rotList (hostOf a)) (S.dinfoAt (hostOf a))
      (fun u => S.dinfoAt u (hostOf a)) (hostOf a) ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2))
        (AP.run N.G (fun w => (S.levelIn hN lam M u₀ w, vals w k)) Tp (hostOf a)) := fun k a => by
    show outP _ (AP.run N.G _ Tp (hostOf _)) = _
    rw [S.cpId_host hN a]
  have hflag : ∀ a k (P : Prop) [Decidable P],
      (outK k (cpIdL (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a))
        (hostOf a) ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)) = 0 ↔ P) →
      decide (outP (cpIdL (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a))
        (hostOf a) ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2))
          (AP.run N.G (fun w => (S.levelIn hN lam M u₀ w, vals w k)) Tp (hostOf a)) = 0) = decide P :=
    fun a k P _ h => by rw [← hcp k a]; exact decide_eq_decide.2 h
  refine ⟨fun z hz => ⟨hix.1 z hz, hjx.1 z hz⟩, fun z => ⟨?_, ?_⟩, fun u hu => hix.2.2 u hu,
    fun u hu => hjx.2.2 u hu, fun a => ?_, fun a => ?_, fun a => ?_⟩
  · rcases hix.2.1 z with h | h
    · exact .inl h
    · exact .inr (h.le.trans (by exact_mod_cast hM : (M : ℕ∞) ≤ (n * (n * 21) + 2) ^ K))
  · rcases hjx.2.1 z with h | h
    · exact .inl h
    · exact .inr (h.le.trans (by exact_mod_cast hM : (M : ℕ∞) ≤ (n * (n * 21) + 2) ^ K))
  · show u0Test b (hostOf a) (S.levelIn hN lam M u₀ (hostOf a)) (vals (hostOf a) 6).2
      (S.levelRecv hN lam M b u₀ (hostOf a)) a = _
    rw [S.locTest_eq hN lam M hb u₀ (gs 6) (fun w => (vals w 6).2) (hvi 6) a]
    exact S.srcOff_eq hN Q (gs 6) (fun z => by rw [h6]) a
  · refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show decide (u0Test b (hostOf a) (S.levelIn hN lam M u₀ (hostOf a)) (vals (hostOf a) 7).2
        (S.levelRecv hN lam M b u₀ (hostOf a)) a = 0) = _
      rw [S.locTest_eq hN lam M hb u₀ (gs 7) (fun w => (vals w 7).2) (hvi 7) a]
      exact S.tgtFlag_eq hN Q (gs 7) (fun z => by rw [h7]) a
    · exact hflag a 2 _ (S.nodeFlag_iff hN M (outK 2) 0 hM1 (by rw [← h2]; exact hpc 2) a)
    · exact hflag a 3 _ (S.nodeFlag_iff hN M (outK 3) 1 hM1 (by rw [← h3]; exact hpc 3) a)
  · refine Prod.ext ?_ ?_
    · exact hflag a 4 _ (S.cornerFlag_iff hN M (outK 4) Q (fun A c => A.2.CornerA c) hM1
        (by rw [← h4]; exact hpc 4) a)
    · exact hflag a 5 _ (S.cornerFlag_iff hN M (outK 5) Q (fun A c => A.2.CornerB c) hM1
        (by rw [← h5]; exact hpc 5) a)

end RData

end RotSystem

end SsspFlow
