import SsspFlow.GHatRuleM
import SsspFlow.GHatLevelConnLocal

/-!
# One level as one algorithm

The global phase of a level needs the distances of the level and the labels of the components of
`Ĝ_ℓ[E_R ∪ E_C]` and of `Ĝ_ℓ[E_R]`. The two label runs use the token lengths `0` and `M`, and a
node computes the inputs of these runs from its own inputs of the level (`LevelIn.withConst`,
`RData.levelIn_const`).

* `RData.levelStep_local`: assuming the Exact SSSP bound, one algorithm of the message model, fixed
  before the network, starts from the local inputs `levelIn` of a level and after at most
  `C log^c n' · (12 D + 16) + 3` rounds holds at every copy its distance from the source copy, a label
  of its component of `Ĝ_ℓ[E_R ∪ E_C]` and a label of its component of `Ĝ_ℓ[E_R]`.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace LevelIn

variable {n : ℕ}

/-- The inputs of the same level with the length `c` on every token. -/
def withConst (c : ℕ) (j : LevelIn n) : LevelIn n :=
  ⟨j.me, j.rot, j.own,
    fun u l => if u ∈ j.rot ∧ (l = .zero ↔ (j.own u).inc = false) then c else 0, j.bnd, j.src⟩

end LevelIn

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)

/-- The inputs for constant token lengths are computed from the inputs of the level. -/
theorem levelIn_const (lam : S.Tok → ℕ) (M c : ℕ) (u₀ : S.hRot.Vertex) (w : Fin n) :
    S.levelIn hN (fun _ => c) M u₀ w = (S.levelIn hN lam M u₀ w).withConst c := by
  unfold levelIn LevelIn.withConst
  congr 1
  funext u l
  unfold lamAt
  by_cases h : N.G.Adj w u
  · have hm : u ∈ N.rotList w := (N.mem_rotList w u).2 h
    have hi : (S.dinfoAt w u).inc = decide ((⟨(w, u), h⟩ : N.G.Dart) ∈ S.inc) := by
      unfold dinfoAt
      rw [dite_eq_left_of_eq_true (eq_true h)]
      rfl
    simp only [h, dite_true, hm, true_and, hi, IsTok, decide_eq_false_iff_not]
    split_ifs <;> rfl
  · have hm : u ∉ N.rotList w := fun hm => h ((N.mem_rotList w u).1 hm)
    simp [h, hm]

/-- **One level as one algorithm.** Assuming the Exact SSSP bound, one algorithm of the message model,
fixed before the network, starts from the local inputs of a level and after `T` rounds holds at every
copy its distance in `Ĝ_ℓ` from the source copy, a label of its component of `Ĝ_ℓ[E_R ∪ E_C]`, and a
label of its component of `Ĝ_ℓ[E_R]`. -/
theorem levelStep_local (hE : ExactSsspBound) (K : ℕ) : ∃ C c : ℕ, ∀ n D : ℕ,
    ∃ (σ : Type) (A : Cslib.Congest.Algorithm (Fin n) (LevelIn n) σ
      (4 * (C * logN (n * (n * 21)) ^ c) + (3 * (K * logN (n * (n * 21)) + 1) + 5)))
      (T : ℕ) (dist labC labR : Fin (n * (n * 21)) → σ → ℕ∞),
    T ≤ 3 + C * logN (n * (n * 21)) ^ c * (12 * D + 16) ∧
    ∀ (N : Net (Fin n)) (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w) (lam : S.Tok → ℕ) (M : ℕ)
      (u₀ : S.hRot.Vertex),
      N.toRot.Planar → N.toRot.Connected → S.NoConflict → S.cut.card ≤ 3 → N.DiamLE D →
      1 ≤ M → n * (n * 21) ≤ M → (∀ x, lam x ≤ (n * (n * 21) + 2) ^ K) → M ≤ (n * (n * 21) + 2) ^ K →
      (∀ v : S.hRot.Vertex,
        (dist ((S.levelPad hN).ι (.inl v))
          (A.run N.G (S.levelIn hN lam M u₀) T (hostOf ((S.levelPad hN).ι (.inl v)))) : ℝ≥0∞) =
          S.arcDist lam M (S.vcopy u₀) (S.vcopy v)) ∧
      (∀ u v : S.hRot.Vertex,
        labC ((S.levelPad hN).ι (.inl u))
            (A.run N.G (S.levelIn hN lam M u₀) T (hostOf ((S.levelPad hN).ι (.inl u)))) =
          labC ((S.levelPad hN).ι (.inl v))
            (A.run N.G (S.levelIn hN lam M u₀) T (hostOf ((S.levelPad hN).ι (.inl v)))) ↔
          Relation.ReflTransGen S.ERC (S.vcopy u) (S.vcopy v)) ∧
      (∀ u v : S.hRot.Vertex,
        labR ((S.levelPad hN).ι (.inl u))
            (A.run N.G (S.levelIn hN lam M u₀) T (hostOf ((S.levelPad hN).ι (.inl u)))) =
          labR ((S.levelPad hN).ι (.inl v))
            (A.run N.G (S.levelIn hN lam M u₀) T (hostOf ((S.levelPad hN).ι (.inl v)))) ↔
          Relation.ReflTransGen S.ER (S.vcopy u) (S.vcopy v)) := by
  obtain ⟨C₁, c₁, hS⟩ := levelSssp_local hE K
  obtain ⟨C₂, c₂, hC⟩ := levelConn_local hE K
  refine ⟨2 * (C₁ + C₂), c₁ + c₂, fun n D => ?_⟩
  obtain ⟨σ₁, A₁, out₁, hA₁⟩ := hS n D
  obtain ⟨σ₂, A₂, out₂, hA₂⟩ := hC n D
  have hL : 1 ≤ logN (n * (n * 21)) := by unfold logN; omega
  have hp₁ : logN (n * (n * 21)) ^ c₁ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hp₂ : logN (n * (n * 21)) ^ c₂ ≤ logN (n * (n * 21)) ^ (c₁ + c₂) := Nat.pow_le_pow_right hL (by omega)
  have hw₁ : 4 * (C₁ * logN (n * (n * 21)) ^ c₁) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤ 4 * (2 * (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂)) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by
    have := Nat.mul_le_mul (show C₁ ≤ 2 * (C₁ + C₂) by omega) hp₁
    omega
  have hw₂ : 4 * (C₂ * logN (n * (n * 21)) ^ c₂) + (3 * (K * logN (n * (n * 21)) + 1) + 5) ≤ 4 * (2 * (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂)) + (3 * (K * logN (n * (n * 21)) + 1) + 5) := by
    have := Nat.mul_le_mul (show C₂ ≤ 2 * (C₁ + C₂) by omega) hp₂
    omega
  set T₁ := 1 + C₁ * logN (n * (n * 21)) ^ c₁ * (12 * D + 16)
  set T₂ := 1 + C₂ * logN (n * (n * 21)) ^ c₂ * (12 * D + 16)
  let B₁ := (A₁.widen hw₁).keep (fun _ (j : LevelIn n) => j)
  let B₂ := (A₂.widen hw₂).keep (fun _ (p : LevelIn n × σ₁) => p.1.withConst 0)
  let B₃ := (A₂.widen hw₂).keep (fun _ (q : (LevelIn n × σ₁) × σ₂) => q.1.1.withConst q.1.1.bnd)
  let A := B₁.seq T₁ (fun _ s => s) (B₂.seq T₂ (fun _ s => s) B₃)
  let rd : (Fin (n * (n * 21)) → σ₁ → ℕ∞) → (Fin (n * (n * 21)) → σ₂ → ℕ∞) →
      (Fin (n * (n * 21)) → σ₂ → ℕ∞) → Fin (n * (n * 21)) →
      ((ℕ × (LevelIn n × σ₁)) ⊕ ((ℕ × ((LevelIn n × σ₁) × σ₂)) ⊕ (((LevelIn n × σ₁) × σ₂) × σ₂))) → ℕ∞ :=
    fun f g h i st =>
      match st with
      | .inr (.inr (((_, s₁), s₂), s₃)) => f i s₁ + g i s₂ + h i s₃
      | _ => 0
  refine ⟨_, A, T₁ + (T₂ + T₂), rd out₁ (fun _ _ => 0) (fun _ _ => 0), rd (fun _ _ => 0) out₂ (fun _ _ => 0),
    rd (fun _ _ => 0) (fun _ _ => 0) out₂, ?_, ?_⟩
  · have := Nat.mul_le_mul (show C₁ ≤ C₁ + C₂ by omega) hp₁
    have := Nat.mul_le_mul (show C₂ ≤ C₁ + C₂ by omega) hp₂
    have h1 := Nat.mul_le_mul_right (12 * D + 16) (show C₁ * logN (n * (n * 21)) ^ c₁ + 2 * (C₂ * logN (n * (n * 21)) ^ c₂) ≤
      2 * (C₁ + C₂) * logN (n * (n * 21)) ^ (c₁ + c₂) by nlinarith)
    simp only [T₁, T₂]
    nlinarith
  intro N S hN lam M u₀ hP hCn hNC hcut hD hM1 hM hlam hMK
  -- the state after all three runs
  have hrun : A.run N.G (S.levelIn hN lam M u₀) (T₁ + (T₂ + T₂)) = fun w =>
      .inr (.inr (((S.levelIn hN lam M u₀ w, A₁.run N.G (S.levelIn hN lam M u₀) T₁ w),
        A₂.run N.G (S.levelIn hN (fun _ => 0) M u₀) T₂ w),
        A₂.run N.G (S.levelIn hN (fun _ => M) M u₀) T₂ w)) := by
    have e0 : (fun w => S.levelIn hN lam M u₀ w |>.withConst 0) = S.levelIn hN (fun _ => 0) M u₀ :=
      funext fun w => (S.levelIn_const hN lam M 0 u₀ w).symm
    have eM : (fun w => S.levelIn hN lam M u₀ w |>.withConst (S.levelIn hN lam M u₀ w).bnd) =
        S.levelIn hN (fun _ => M) M u₀ :=
      funext fun w => (S.levelIn_const hN lam M M u₀ w).symm
    funext w
    simp only [A, B₁, B₂, B₃, Cslib.Congest.Algorithm.run_seq, Cslib.Congest.Algorithm.run_keep,
      Cslib.Congest.Algorithm.run_widen, e0, eM]
  rw [hrun]
  refine ⟨fun v => ?_, fun u v => ?_, fun u v => ?_⟩
  · simp only [rd, add_zero]
    exact hA₁ N S hN lam M u₀ hP hCn hNC hcut hD hlam hMK v
  · simp only [rd, zero_add, add_zero]
    rw [hA₂ N S hN (fun _ => 0) M u₀ hP hCn hNC hcut hD (fun _ => Or.inl rfl) (fun _ => rfl) hM
      (fun _ => Nat.zero_le _) hMK u v, zr_zero]
  · simp only [rd, zero_add]
    rw [hA₂ N S hN (fun _ => M) M u₀ hP hCn hNC hcut hD (fun _ => Or.inr le_rfl) (fun _ => rfl) hM
      (fun _ => hMK) hMK u v, zr_const S hM1]

end RData

end RotSystem

end SsspFlow
