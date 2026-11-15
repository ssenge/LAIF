import SsspFlow.GHatLevelNodeRun
import SsspFlow.GHatLevelPrep

/-!
# The data of the nodes of a level from local values, as one algorithm

The algorithm of `RData.levelPrep_local` computes the inputs of the run of the nodes of a level from the
values at the corners of the darts out of each node and into it, and the algorithm of
`RData.levelNode_run` then runs on these inputs. Together they form one algorithm of the message model
whose inputs are the input of the level and these values.

* `RData.levelNode_local`: the data of the nodes of a level from the input of the level and the values
  at the corners, from one algorithm with a bound on its rounds.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

open Classical Cslib.Congest.Algorithm in
/-- **The data of the nodes of a level from local values, as one algorithm.** The statement of
`RData.levelNode_run`, with the inputs of the level computed by the algorithm of
`RData.levelPrep_local` from the values at the corners, numbered `0` to `7` as there. The flags of the
targets, of the nodes and of the corners of the sides are those of the list `Q`, and the algorithm
also gives them, with the offsets of the sources, at the host of each identifier. -/
theorem levelNode_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n)
        (LevelIn n × (ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (rr r₂ r₃ rA rB : Fin (n * (n * 21)) → σ → ℕ∞ × Option (Fin (n * (n * 21))))
      (o1 o2 : Fin (n * (n * 21)) → σ → ℕ∞) (offO : Fin (n * (n * 21)) → σ → ℕ∞)
      (flgO : Fin (n * (n * 21)) → σ → Bool × Bool × Bool) (cflO : Fin (n * (n * 21)) → σ → Bool × Bool),
    T ≤ 23 + 15 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
      {Cp : N.toRot.dual.CutPath} {g : N.G.Dart → ℝ≥0∞} {hR : N.toRot.dual.Planar}
      {hC : N.toRot.dual.Connected} {hg : ∀ x, g (N.toRot.dual.rev x) = g x}
      {Γ₀ : Finset (N.G.Dart × Bool)} {L₀ : Cp.Live g Γ₀} {j k : ℕ}
      (r : CutPath.Run hR hC hg Γ₀ L₀ j k) (ℓ : ℕ) (lam : S.Tok → ℕ) (M : ℕ) (cc : N.G.Dart → ℕ)
      (u₀ : S.hRot.Vertex) (Q : List ((Σ Γ' : Finset (N.G.Dart × Bool), Cp.Live g Γ') × ℕ))
      (vals : Fin n → ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞)) (gs : ℕ → N.G.Dart × Bool → ℕ∞),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ d, 1 ≤ cc d) → (∀ d, cc (N.toRot.rev d) = cc d) → (∀ x, lam x = cc x.1.1) →
      (∀ d, g d = cc d) → S.Γ = Γ₀ ∪ r.steps ℓ →
      (∀ q ∈ Q, q.1 ∈ r.nodes ℓ ∧ q.1.2.xa ≤ q.2 ∧ q.1.2.ya ≤ q.2 ∧ q.2 ≤ q.1.2.xb ∧
        q.2 ≤ q.1.2.yb ∧ Cp.lamD g q.2 < M) →
      (∀ q ∈ Q, ∀ q' ∈ Q, q.1 = q'.1 → q.2 = q'.2) →
      1 ≤ M → Cp.m < M → (∀ k z, gs k z = ⊤ ∨ gs k z ≤ (n * (n * 21) + 2) ^ K) →
      (∀ k (d : N.G.Dart) b, (vals d.fst k).1 d.snd b = gs k (d, b)) →
      (∀ k (d : N.G.Dart) b, (vals d.snd k).2 d.fst b = gs k (d, b)) →
      gs 0 = (fun z => ⨅ r ∈ cornerIdx Cp z, (r : ℕ∞)) →
      gs 1 = (fun z => ⨅ r ∈ cornerIdx Cp z, ((Cp.m - r : ℕ) : ℕ∞)) →
      gs 2 = flagVal Cp 0 → gs 3 = flagVal Cp 1 →
      gs 4 = (fun z => if ∃ q ∈ Q, q.1.2.CornerA z then 0 else ⊤) →
      gs 5 = (fun z => if ∃ q ∈ Q, q.1.2.CornerB z then 0 else ⊤) →
      gs 6 = (fun z => if ∃ q ∈ Q, z = qEnd 0 q then 0 else ⊤) →
      gs 7 = (fun z => if ∃ q ∈ Q, z = qEnd 1 q then 0 else ⊤) →
      let flg : Fin n → Fin (n * (n * 21)) → Bool × Bool × Bool := fun _ a =>
        (S.tgtFlag hN Q a, decide (S.nodeFlag hN Cp 0 a), decide (S.nodeFlag hN Cp 1 a))
      let cfl : Fin n → Fin (n * (n * 21)) → Bool × Bool := fun _ a =>
        (decide (S.cornerFlag hN Q (fun A c => A.2.CornerA c) a), decide (S.cornerFlag hN Q (fun A c => A.2.CornerB c) a))
      let st := A.run N.G (fun w => (S.levelIn hN lam M u₀ w, vals w)) T
      let R := fun a => rr a (st (hostOf a))
      (∀ a, offO a (st (hostOf a)) = S.srcOff hN Q a ∧ flgO a (st (hostOf a)) = flg (hostOf a) a ∧
        cflO a (st (hostOf a)) = cfl (hostOf a) a) ∧
      (S.levelNet hN).ExactSpec (S.levelLen hN lam M) (S.srcOff hN Q) R ∧
      R = hE.oracleRun K (12 * D + 16) (by omega) (S.levelNet hN) (S.levelLen hN lam M) (S.srcOff hN Q) ∧
      (S.levelNet hN).ExactSpec (Net.markLenW R fun a => (((flg (hostOf a) a).2.1).toNat : ℕ∞))
        (Net.markOffB fun a => (flg (hostOf a) a).1) (fun a => r₂ a (st (hostOf a))) ∧
      (S.levelNet hN).ExactSpec (Net.downLenW R fun a => (((flg (hostOf a) a).2.2).toNat : ℕ∞))
        (Net.markOffB fun a => (flg (hostOf a) a).2.1 && decide ((r₂ a (st (hostOf a))).1 = 0))
        (fun a => r₃ a (st (hostOf a))) ∧
      ∀ At ∈ Q, ∃ (kk i1 i2 : ℕ) (St : At.1.2.Step),
        At.1.2.Shortest At.2 (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk) ∧
        IsLeast (Cp.idx (At.1.2.κ0 At.2)
          (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk)) i1 ∧
        IsGreatest (Cp.idx (At.1.2.κ0 At.2)
          (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk)) i2 ∧
        min (o1 ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))
          (st (hostOf ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))) : ℝ≥0∞) M =
            min (i1 : ℝ≥0∞) M ∧
        min (o2 ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))
          (st (hostOf ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))) : ℝ≥0∞) M =
            min ((Cp.m - i2 : ℕ) : ℝ≥0∞) M ∧
        (∀ z, z ∈ (List.range St.n).map St.q ↔ ∃ l,
          Net.ParSteps R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) (l + 1) ∧
          (r₂ ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))
            (st (hostOf ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))))).1 = 0 ∧
          (flg (hostOf ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))))
            ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))).2.1 = false ∧
          (r₃ ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))
            (st (hostOf ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))))).1 = 0 ∧
          ∃ x, S.edgeTok hN ((Net.parOf R)^[l + 1] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))
              ((Net.parOf R)^[l] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))) = some x ∧
            z = N.toRot.tokDart x.1) ∧
        (∃ p₁ p₃, S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk =
          p₁ ++ (List.range St.n).map St.q ++ p₃) ∧
        (∀ c, At.1.2.Visits At.2 (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk) c ↔
          ∃ y, (∃ i, (Net.parOf R)^[i] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) = y) ∧
            ∃ hy : (∃ x : S.Tok, S.IsEnd x.1 (S.copyAt hN y)),
              S.vertexEquiv (S.pieceOf ⟨S.copyAt hN y, hy⟩) = S.dualSplit.tail c) ∧
        Net.ParSteps R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) kk ∧ (R ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))).2 = none ∧
        ((∃ c, At.1.2.CornerA c ∧ At.1.2.Visits At.2 (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk) c) ↔
          (rA ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))) (st (hostOf ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))))).1 ≠ 0 ∨ (cfl (hostOf ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))) ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))).1 = true) ∧
        ((∃ c, At.1.2.CornerB c ∧ At.1.2.Visits At.2 (S.chainDarts hN R ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))) 0 kk) c) ↔
          (rB ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2))))) (st (hostOf ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))))).1 ≠ 0 ∨ (cfl (hostOf ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))) ((Net.parOf R)^[kk] ((S.levelPad hN).ι (.inl (S.endV (At.1.2.κ1 At.2)))))).2 = true) := by
  obtain ⟨Cq, cq, hPq⟩ := levelPrep_local hE K
  obtain ⟨Cn, cn, hNd⟩ := levelNode_run hE K
  refine ⟨Cq + Cn, cq + cn, fun n D => ?_⟩
  obtain ⟨σ₁, A₁, off₁, flg₁, ixL₁, jxL₁, cfl₁, hA₁⟩ := hPq n D
  obtain ⟨σ₂, A₂, T₂, rr, r₂, r₃, rA, rB, o1, o2, hT₂, hA₂⟩ := hNd n D
  have hL : 1 ≤ logN (n * (n * 21)) := by unfold logN; omega
  have hp₁ : logN (n * (n * 21)) ^ cq ≤ logN (n * (n * 21)) ^ (cq + cn) := Nat.pow_le_pow_right hL (by omega)
  have hp₂ : logN (n * (n * 21)) ^ cn ≤ logN (n * (n * 21)) ^ (cq + cn) := Nat.pow_le_pow_right hL (by omega)
  have hm₁ := Nat.mul_le_mul (show Cq ≤ Cq + Cn by omega) hp₁
  have hm₂ := Nat.mul_le_mul (show Cn ≤ Cq + Cn by omega) hp₂
  have hw₁ : 4 * (Cq * logN (n * (n * 21)) ^ cq) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤
      4 * ((Cq + Cn) * logN (n * (n * 21)) ^ (cq + cn) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by
    omega
  have hw₂ : 4 * (Cn * logN (n * (n * 21)) ^ cn + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤
      4 * ((Cq + Cn) * logN (n * (n * 21)) ^ (cq + cn) + 3) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by
    omega
  set T₁ := 6 * (1 + (1 + Cq * logN (n * (n * 21)) ^ cq * (12 * D + 16))) + 1 with hT₁
  let J := LevelIn n × (ℕ → (Fin n → Bool → ℕ∞) × (Fin n → Bool → ℕ∞))
  let f : Fin n → J × σ₁ → LevelIn n × ((((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → Bool × Bool × Bool)) ×
      ((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → ℕ∞))) × (Fin (n * (n * 21)) → Bool × Bool)) :=
    fun w p => (p.1.1, (((off₁ w p.2, flg₁ w p.2), (ixL₁ w p.2, jxL₁ w p.2)), cfl₁ w p.2))
  let J₂ := LevelIn n × ((((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → Bool × Bool × Bool)) ×
      ((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → ℕ∞))) × (Fin (n * (n * 21)) → Bool × Bool))
  let A := ((A₁.widen hw₁).keep (fun _ (i : J) => i)).seq T₁ f ((A₂.widen hw₂).keep (fun _ (i : J₂) => i))
  let fin : ∀ {β : Type}, β → (J₂ × σ₂ → β) → ((ℕ × (J × σ₁)) ⊕ (J₂ × σ₂)) → β :=
    fun d F => Sum.elim (fun _ => d) F
  refine ⟨_, A, T₁ + T₂,
    fun a => fin (⊤, none) (fun q => rr a q.2), fun a => fin (⊤, none) (fun q => r₂ a q.2),
    fun a => fin (⊤, none) (fun q => r₃ a q.2), fun a => fin (⊤, none) (fun q => rA a q.2),
    fun a => fin (⊤, none) (fun q => rB a q.2), fun a => fin 0 (fun q => o1 a q.2),
    fun a => fin 0 (fun q => o2 a q.2), fun a => fin ⊤ (fun q => q.1.2.1.1.1 a),
    fun a => fin (false, false, false) (fun q => q.1.2.1.1.2 a), fun a => fin (false, false) (fun q => q.1.2.2 a),
    ?_, ?_⟩
  · have h : Cq * logN (n * (n * 21)) ^ cq * (12 * D + 16) ≤
        (Cq + Cn) * logN (n * (n * 21)) ^ (cq + cn) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₁
    have h' : Cn * logN (n * (n * 21)) ^ cn * (12 * D + 16) ≤
        (Cq + Cn) * logN (n * (n * 21)) ^ (cq + cn) * (12 * D + 16) := Nat.mul_le_mul_right _ hm₂
    omega
  intro N S hN Cp g hR hC hg Γ₀ L₀ j k r ℓ lam M cc u₀ Q vals gs hP hc hS hcut hD hlam hM hc1 hcr hlc hgc hΓ
    hQ hQu hM1 hmM hgs hvo hvi h0 h1 h2 h3 h4 h5 h6 h7 flg cfl
  set stP := A₁.run N.G (fun w => (S.levelIn hN lam M u₀ w, vals w)) T₁ with hstP
  obtain ⟨hx0, hxW, hix, hjx, hoff, hflg, hcfl⟩ := hA₁ N S hN lam M u₀ vals gs Q hP hc hS hcut hD hlam hM1 hM
    hmM hgs hvo hvi h0 h1 h2 h3 h4 h5 h6 h7
  have hnode := hA₂ N S hN r ℓ lam M cc u₀ Q (fun a => ixL₁ (hostOf a) (stP (hostOf a)) a)
    (fun a => jxL₁ (hostOf a) (stP (hostOf a)) a) (fun w => off₁ w (stP w)) (fun w => flg₁ w (stP w))
    (fun w => ixL₁ w (stP w)) (fun w => jxL₁ w (stP w)) (fun w => cfl₁ w (stP w)) hP hc hS hcut hD hlam hM hc1
    hcr hlc hgc hΓ hQ hQu hx0 hxW hix hjx hoff hflg (fun _ => rfl) (fun _ => rfl) hcfl
  have hflg' : ∀ a, flg₁ (hostOf a) (stP (hostOf a)) a =
      (S.tgtFlag hN Q a, decide (S.nodeFlag hN Cp 0 a), decide (S.nodeFlag hN Cp 1 a)) := hflg
  have hcfl' : ∀ a, cfl₁ (hostOf a) (stP (hostOf a)) a =
      (decide (S.cornerFlag hN Q (fun A c => A.2.CornerA c) a),
        decide (S.cornerFlag hN Q (fun A c => A.2.CornerB c) a)) := hcfl
  simp only [hflg', hcfl'] at hnode
  have hrun : A.run N.G (fun w => (S.levelIn hN lam M u₀ w, vals w)) (T₁ + T₂) =
      fun w => .inr ((S.levelIn hN lam M u₀ w, (((off₁ w (stP w), flg₁ w (stP w)),
        (ixL₁ w (stP w), jxL₁ w (stP w))), cfl₁ w (stP w))), A₂.run N.G (fun w => (S.levelIn hN lam M u₀ w,
          (((off₁ w (stP w), flg₁ w (stP w)), (ixL₁ w (stP w), jxL₁ w (stP w))), cfl₁ w (stP w)))) T₂ w) := by
    funext w
    simp only [A, run_seq, run_keep, run_widen]
    rfl
  have hoff' : ∀ a, off₁ (hostOf a) (stP (hostOf a)) a = S.srcOff hN Q a := hoff
  rw [hrun]
  exact ⟨fun a => ⟨hoff' a, hflg' a, hcfl' a⟩, hnode⟩

end RData

end RotSystem

end SsspFlow
