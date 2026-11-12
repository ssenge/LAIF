import SsspFlow.GHatLevelMinIdx
import SsspFlow.GHatLevelStep

/-!
# The least and the greatest index of a level as one algorithm

The nodes run the marking algorithm of a level (`RData.levelMark_local`), then two runs of least
offsets with token lengths `0` (`RData.levelMin_local`). For these runs a node gives each identifier
it hosts the offset `ix` or `jx` of its input if the marking run marked it, and `⊤` otherwise. The
values `ix` and `jx` are inputs at the identifiers of the copies, as are the offsets and the targets
of the marking run.

* `RData.levelI12_local`: assuming the Exact SSSP bound, one algorithm of the message model, fixed
  before the network, starts from the local inputs of a level, the offsets, the targets and the
  values `ix` and `jx` at the identifiers of each node. After at most
  `2 C log^c n' · (12 D + 16) + 4` rounds its outputs of the first run meet the specification of
  the oracle, and every copy holds, capped at `M`, the least `ix` and the least `jx` over the copies
  of its component of `Ĝ_ℓ[E_R ∪ E_C]` that the marking run marked.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

open Classical in
/-- **The least values at the marked copies of a component, as one algorithm.** Assuming the Exact
SSSP bound, one algorithm of the message model on `N`, fixed before the network, starts from the
inputs `levelIn` of a level and, at each node, offsets, targets and values `ix`, `jx` that agree with
`ψ`, `isT`, `ixI`, `jxI` at the identifiers it hosts. After `T` rounds its outputs `rr` meet the
specification of the oracle for the lengths of the level with offsets `ψ`, and at every copy the
outputs `o1` and `o2`, capped at `M`, are the least `ixI` and the least `jxI` over the copies of its
component of `Ĝ_ℓ[E_R ∪ E_C]` whose identifiers lie on the parent chain of a target. -/
theorem levelI12_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n)
        (LevelIn n × (((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → Bool)) ×
          ((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → ℕ∞)))) σ
        (4 * (C * logN (n * (n * 21)) ^ c + 1) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (rr : Fin (n * (n * 21)) → σ → ℕ∞ × Option (Fin (n * (n * 21))))
      (o1 o2 : Fin (n * (n * 21)) → σ → ℕ∞),
    T ≤ 4 + 2 * (C * logN (n * (n * 21)) ^ c * (12 * D + 16)) ∧
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex) (ψ : Fin (n * (n * 21)) → ℕ∞) (isT : Fin (n * (n * 21)) → Bool)
      (ixI jxI : Fin (n * (n * 21)) → ℕ∞)
      (off : Fin n → Fin (n * (n * 21)) → ℕ∞) (flg : Fin n → Fin (n * (n * 21)) → Bool)
      (ixL jxL : Fin n → Fin (n * (n * 21)) → ℕ∞),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ z, ψ z = ⊤ ∨ ψ z ≤ (n * (n * 21) + 2) ^ K) →
      (∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → ixI z = ⊤ ∧ jxI z = ⊤) →
      (∀ z, (ixI z = ⊤ ∨ ixI z ≤ (n * (n * 21) + 2) ^ K) ∧ (jxI z = ⊤ ∨ jxI z ≤ (n * (n * 21) + 2) ^ K)) →
      (∀ a, off (hostOf a) a = ψ a) → (∀ a, flg (hostOf a) a = isT a) →
      (∀ a, ixL (hostOf a) a = ixI a) → (∀ a, jxL (hostOf a) a = jxI a) →
      let st := A.run N.G (fun w => (S.levelIn hN lam M u₀ w, ((off w, flg w), (ixL w, jxL w)))) T
      let R := fun a => rr a (st (hostOf a))
      (S.levelNet hN).ExactSpec (S.levelLen hN lam M) ψ R ∧
      ∀ v : S.hRot.Vertex,
        min (o1 ((S.levelPad hN).ι (.inl v)) (st (hostOf ((S.levelPad hN).ι (.inl v)))) : ℝ≥0∞) M =
          min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v)),
            ⨅ (_ : ∃ t i, isT t = true ∧ (Net.parOf R)^[i] t = (S.levelPad hN).ι (.inl u)),
              (ixI ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞)) M ∧
        min (o2 ((S.levelPad hN).ι (.inl v)) (st (hostOf ((S.levelPad hN).ι (.inl v)))) : ℝ≥0∞) M =
          min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v)),
            ⨅ (_ : ∃ t i, isT t = true ∧ (Net.parOf R)^[i] t = (S.levelPad hN).ι (.inl u)),
              (jxI ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞)) M := by
  obtain ⟨C₁, c₁, hMk⟩ := levelMark_local hE K
  obtain ⟨C₂, c₂, hMn⟩ := levelMin_local hE K
  refine ⟨C₁ + C₂, c₁ + c₂, fun n D => ?_⟩
  obtain ⟨σ₁, A₁, T₁, out₁, out₂, hT₁, hA₁⟩ := hMk n D
  obtain ⟨σ₂, A₂, outm, hA₂⟩ := hMn n D
  have hL : 1 ≤ logN (n * (n * 21)) := by unfold logN; omega
  have hp₁ : logN (n * (n * 21)) ^ c₁ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hp₂ : logN (n * (n * 21)) ^ c₂ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hq₁ := Nat.mul_le_mul (show C₁ ≤ C₁ + C₂ by omega) hp₁
  have hq₂ := Nat.mul_le_mul (show C₂ ≤ C₁ + C₂ by omega) hp₂
  have hw₁ : 4 * (C₁ * logN (n * (n * 21)) ^ c₁ + 1) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤ 4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 1) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by
    omega
  have hw₂ : 4 * (C₂ * logN (n * (n * 21)) ^ c₂) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤ 4 * ((C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) + 1) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by
    omega
  set T₂ := 1 + C₂ * logN (n * (n * 21)) ^ c₂ * (12 * D + 16)
  let Im := LevelIn n × (((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → Bool)) ×
    ((Fin (n * (n * 21)) → ℕ∞) × (Fin (n * (n * 21)) → ℕ∞)))
  let offM : (Fin (n * (n * 21)) → ℕ∞) → σ₁ → Fin (n * (n * 21)) → ℕ∞ :=
    fun ixl s a => if (out₂ a s).1 = 0 then ixl a else ⊤
  let B₁ := (A₁.widen hw₁).keep (fun _ (j : Im) => (j.1, j.2.1))
  let B₂ := (A₂.widen hw₂).keep (fun _ (p : Im × σ₁) => (p.1.1.withConst 0, offM p.1.2.2.1 p.2))
  let B₃ := (A₂.widen hw₂).keep
    (fun _ (q : (Im × σ₁) × σ₂) => (q.1.1.1.withConst 0, offM q.1.1.2.2.2 q.1.2))
  let A := B₁.seq T₁ (fun _ s => s) (B₂.seq T₂ (fun _ s => s) B₃)
  refine ⟨_, A, T₁ + (T₂ + T₂),
    fun a st => match st with
      | .inr (.inr (((_, s₁), _), _)) => out₁ a s₁
      | _ => (⊤, none),
    fun a st => match st with
      | .inr (.inr ((_, s₂), _)) => outm a s₂
      | _ => ⊤,
    fun a st => match st with
      | .inr (.inr (_, s₃)) => outm a s₃
      | _ => ⊤, ?_, ?_⟩
  · have hr₁ := Nat.mul_le_mul_right (12 * D + 16) (Nat.mul_le_mul_left C₁ hp₁)
    have hr₂ := Nat.mul_le_mul_right (12 * D + 16) (Nat.mul_le_mul_left C₂ hp₂)
    have e : (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) =
        C₁ * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) + C₂ * logN (n * (n * 21)) ^ (c₁ + c₂) * (12 * D + 16) := by ring
    simp only [T₂]
    omega
  intro N S hN lam M u₀ ψ isT ixI jxI off flg ixL jxL hP hc hS hcut hD hlam hM hψW hixT hixW hoff hflg
    hixL hjxL
  have e0 : ∀ w, (S.levelIn hN lam M u₀ w).withConst 0 = S.levelIn hN (fun _ => 0) M u₀ w :=
    fun w => (S.levelIn_const hN lam M 0 u₀ w).symm
  set s₁ := A₁.run N.G (fun w => (S.levelIn hN lam M u₀ w, (off w, flg w))) T₁ with hs₁
  have hrun : A.run N.G (fun w => (S.levelIn hN lam M u₀ w, ((off w, flg w), (ixL w, jxL w))))
      (T₁ + (T₂ + T₂)) = fun w =>
        .inr (.inr ((((S.levelIn hN lam M u₀ w, ((off w, flg w), (ixL w, jxL w))), s₁ w),
          A₂.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, offM (ixL w) (s₁ w))) T₂ w),
          A₂.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, offM (jxL w) (s₁ w))) T₂ w)) := by
    funext w
    simp only [A, B₁, B₂, B₃, Cslib.Congest.Algorithm.run_seq, Cslib.Congest.Algorithm.run_keep,
      Cslib.Congest.Algorithm.run_widen, e0, s₁]
  intro st R
  have hR : R = fun a => out₁ a (s₁ (hostOf a)) := by
    funext a
    simp only [R, st, hrun]
  have hst : ∀ v : S.hRot.Vertex, st (hostOf ((S.levelPad hN).ι (.inl v))) =
      .inr (.inr ((((S.levelIn hN lam M u₀ (hostOf ((S.levelPad hN).ι (.inl v))),
          ((off (hostOf ((S.levelPad hN).ι (.inl v))), flg (hostOf ((S.levelPad hN).ι (.inl v)))),
          (ixL (hostOf ((S.levelPad hN).ι (.inl v))), jxL (hostOf ((S.levelPad hN).ι (.inl v)))))),
          s₁ (hostOf ((S.levelPad hN).ι (.inl v)))),
        A₂.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, offM (ixL w) (s₁ w))) T₂
          (hostOf ((S.levelPad hN).ι (.inl v)))),
        A₂.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, offM (jxL w) (s₁ w))) T₂
          (hostOf ((S.levelPad hN).ι (.inl v))))) := fun v => by
    simp only [st, hrun]
  obtain ⟨hX1, hX2⟩ := hA₁ N S hN lam M u₀ ψ isT off flg hP hc hS hcut hD hlam hM hψW hoff hflg
  have hm : ∀ a, (out₂ a (s₁ (hostOf a))).1 = 0 ↔
      ∃ t i, isT t = true ∧ (Net.parOf fun a => out₁ a (s₁ (hostOf a)))^[i] t = a := by
    intro a
    have hd := hX2.dist_eq a
    rw [hX1.dsrcTop_markB isT a] at hd
    split_ifs at hd with hx
    · exact ⟨fun _ => hx, fun _ => ENat.toENNReal_eq_zero.1 hd⟩
    · refine ⟨fun h0 => ?_, fun h => absurd h hx⟩
      rw [h0] at hd
      simp at hd
  have key : ∀ (xI : Fin (n * (n * 21)) → ℕ∞) (xL : Fin n → Fin (n * (n * 21)) → ℕ∞),
      (∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → xI z = ⊤) →
      (∀ z, xI z = ⊤ ∨ xI z ≤ (n * (n * 21) + 2) ^ K) → (∀ a, xL (hostOf a) a = xI a) →
      ∀ v : S.hRot.Vertex,
        min (outm ((S.levelPad hN).ι (.inl v))
          (A₂.run N.G (fun w => (S.levelIn hN (fun _ => 0) M u₀ w, offM (xL w) (s₁ w))) T₂
            (hostOf ((S.levelPad hN).ι (.inl v)))) : ℝ≥0∞) M =
          min (⨅ u, ⨅ (_ : Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v)),
            ⨅ (_ : ∃ t i, isT t = true ∧
              (Net.parOf fun a => out₁ a (s₁ (hostOf a)))^[i] t = (S.levelPad hN).ι (.inl u)),
              (xI ((S.levelPad hN).ι (.inl u)) : ℝ≥0∞)) M := by
    intro xI xL hxT hxW hxL v
    let ψ' : Fin (n * (n * 21)) → ℕ∞ := fun a => if (out₂ a (s₁ (hostOf a))).1 = 0 then xI a else ⊤
    have h1 : ∀ z, (∀ u, z ≠ (S.levelPad hN).ι (.inl u)) → ψ' z = ⊤ := fun z hz => by
      simp only [ψ']
      split_ifs
      · exact hxT z hz
      · rfl
    have h2 : ∀ z, ψ' z = ⊤ ∨ ψ' z ≤ (n * (n * 21) + 2) ^ K := fun z => by
      simp only [ψ']
      split_ifs
      · exact hxW z
      · exact .inl rfl
    have h3 : ∀ a, (fun w => offM (xL w) (s₁ w)) (hostOf a) a = ψ' a := fun a => by
      simp only [offM, ψ', hxL]
    rw [hA₂ N S hN M u₀ ψ' (fun w => offM (xL w) (s₁ w)) hP hc hS hcut hD hM h1 h2 h3 v]
    congr 1
    refine iInf_congr fun u => iInf_congr fun _ => ?_
    rw [iInf_eq_if]
    simp only [ψ']
    by_cases h : ∃ t i, isT t = true ∧
        (Net.parOf fun a => out₁ a (s₁ (hostOf a)))^[i] t = (S.levelPad hN).ι (.inl u)
    · rw [if_pos h, if_pos ((hm _).2 h)]
    · rw [if_neg h, if_neg (fun h' => h ((hm _).1 h')), ENat.toENNReal_top]
  rw [hR]
  refine ⟨hX1, fun v => ⟨?_, ?_⟩⟩
  · rw [hst v]
    exact key ixI ixL (fun z hz => (hixT z hz).1) (fun z => (hixW z).1) hixL v
  · rw [hst v]
    exact key jxI jxL (fun z hz => (hixT z hz).2) (fun z => (hixW z).2) hjxL v

end RData

end RotSystem

end SsspFlow
