import SsspFlow.GHatLevelMasks
import SsspFlow.GHatLevelU0Run
import SsspFlow.GHatChainSelf

/-!
# The flags and offsets of a level from local values

The inputs of the run of the nodes of a level are the offsets of the sources, the flags of the targets,
of the nodes for `0` and `1`, and of the corners of the two sides. Each is read at the host of an
identifier: the sources and targets from the values of the corners of the darts into the host, after
one exchange of the records, and the other flags at the copy of the identifier from runs on the
pieces with values `0` and `⊤`.

* `RData.locTest_eq`: the test of `RData.u0Test` for any values of the corners.
* `RData.srcOff_eq`, `RData.tgtFlag_eq`: the offsets of the sources and the flags of the targets of a
  list of annuli from the values `0` at their source or target corners.
* `RData.nodeFlag_iff`: the flag of a node for `σ` from a run on the pieces with the flags of the
  corners for `σ`.
* `RData.cornerFlag_iff`: the flag of a node for a choice of corners from a run on the pieces.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- **The test of the host, for any values.** -/
theorem locTest_eq (lam : S.Tok → ℕ) (M : ℕ) {b : ℕ} (hb : ∀ x, lam x < 2 ^ b) (u₀ : S.hRot.Vertex)
    (f : N.G.Dart × Bool → ℕ∞) (vi : Fin n → Fin n → Bool → ℕ∞)
    (hvi : ∀ (d : N.G.Dart) c, vi d.snd d.fst c = f (d, c)) (a : Fin (n * (n * 21))) :
    u0Test b (hostOf a) (S.levelIn hN lam M u₀ (hostOf a)) (vi (hostOf a))
        (S.levelRecv hN lam M b u₀ (hostOf a)) a =
      S.onCopies hN (fun u => S.copyVal0 f (S.vcopy u)) a := by
  unfold u0Test
  rw [S.inn_recv hN lam M hb u₀ (hostOf a)]
  show locCopy (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a)) (fun _ _ => ⊤) (vi (hostOf a))
    (idEquiv.symm a).2.2 (rawAt (N.rotList (hostOf a)) (S.dinfoAt (hostOf a))
      (fun u => S.dinfoAt u (hostOf a)) (hostOf a) ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)) = _
  rw [← S.levelNet_rotList_raw hN a]
  exact S.locCopy_eq0 hN f vi hvi a

variable {C : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞}

open Classical in
/-- **The offsets of the sources from their corners.** -/
theorem srcOff_eq (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (f : N.G.Dart × Bool → ℕ∞) (hf : ∀ z, f z = if ∃ q ∈ Q, z = qEnd 0 q then 0 else ⊤)
    (a : Fin (n * (n * 21))) :
    S.onCopies hN (fun u => S.copyVal0 f (S.vcopy u)) a = S.srcOff hN Q a := by
  rw [S.onCopies_endFlag hN f 0 Q hf a]
  unfold srcOff
  simp [qEnd]

open Classical in
/-- **The flags of the targets from their corners.** -/
theorem tgtFlag_eq (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (f : N.G.Dart × Bool → ℕ∞) (hf : ∀ z, f z = if ∃ q ∈ Q, z = qEnd 1 q then 0 else ⊤)
    (a : Fin (n * (n * 21))) :
    decide (S.onCopies hN (fun u => S.copyVal0 f (S.vcopy u)) a = 0) = S.tgtFlag hN Q a := by
  rw [S.onCopies_endFlag hN f 1 Q hf a]
  unfold tgtFlag
  have e : ∀ q : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ, qEnd 1 q = q.1.2.κ1 q.2 :=
    fun q => by simp [qEnd]
  simp only [e]
  split_ifs with h
  · simp [h]
  · simp [h]

variable (M : ℕ) (out : Fin (n * (n * 21)) → ℕ∞)

/-- **The flag of a node for `σ`.** -/
theorem nodeFlag_iff (σ : Fin 2) (hM : 1 ≤ M)
    (hpc : ∀ v, min (out ((S.levelPad hN).ι (.inl v)) : ℝ≥0∞) M =
      min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ER (S.vcopy u) (S.vcopy v)),
        ((S.copyVal (flagVal C σ) (S.vcopy u) : ℕ∞) : ℝ≥0∞)) M) (a : Fin (n * (n * 21))) :
    out (cpIdL (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a)) (hostOf a)
        ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)) = 0 ↔ S.nodeFlag hN C σ a := by
  classical
  rw [S.pieceFlag_iff hN M out (flagVal C σ) (fun z => ∃ t, t ≤ C.m ∧ C.cut.tail z = C.cut.tail (C.k σ t))
    (fun z => by unfold flagVal; split_ifs with h <;> simp [h])
    (fun z => by unfold flagVal; split_ifs <;> simp) hM hpc a]
  unfold nodeFlag CopyPiece
  refine exists_congr fun hy => ⟨?_, ?_⟩
  · rintro ⟨z, hz, t, ht, hc⟩
    exact ⟨t, ht, z, (S.tail_eq_vertexEquiv_iff z _).2 hz, hc⟩
  · rintro ⟨t, ht, z, hz, hc⟩
    exact ⟨z, (S.tail_eq_vertexEquiv_iff z _).1 hz, t, ht, hc⟩

open Classical in
/-- **The flag of a node for a choice of corners.** -/
theorem cornerFlag_iff (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') × ℕ))
    (P : (Σ Γ' : Finset (N.G.Dart × Bool), C.Live g Γ') → N.G.Dart × Bool → Prop) (hM : 1 ≤ M)
    (hpc : ∀ v, min (out ((S.levelPad hN).ι (.inl v)) : ℝ≥0∞) M =
      min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ER (S.vcopy u) (S.vcopy v)),
        ((S.copyVal (fun z => if ∃ q ∈ Q, P q.1 z then 0 else ⊤) (S.vcopy u) : ℕ∞) : ℝ≥0∞)) M)
    (a : Fin (n * (n * 21))) :
    out (cpIdL (N.rotList (hostOf a)) (S.dinfoAt (hostOf a)) (fun u => S.dinfoAt u (hostOf a)) (hostOf a)
        ((idEquiv.symm a).2.1, (idEquiv.symm a).2.2)) = 0 ↔ S.cornerFlag hN Q P a := by
  rw [S.pieceFlag_iff hN M out _ (fun z => ∃ q ∈ Q, P q.1 z)
    (fun z => by split_ifs with h <;> simp [h]) (fun z => by split_ifs <;> simp) hM hpc a]
  unfold cornerFlag
  constructor
  · rintro ⟨hy, z, hz, q, hq, hp⟩
    exact ⟨q, hq, z, hp, hy, ((S.tail_eq_vertexEquiv_iff z _).2 hz).symm⟩
  · rintro ⟨q, hq, c, hp, hy, hc⟩
    exact ⟨hy, c, (S.tail_eq_vertexEquiv_iff c _).1 hc.symm, q, hq, hp⟩

end RData

end RotSystem

end SsspFlow
