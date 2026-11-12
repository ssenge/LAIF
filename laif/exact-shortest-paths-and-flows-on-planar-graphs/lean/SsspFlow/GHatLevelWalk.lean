import SsspFlow.GHatLevelMin

/-!
# Walks of the network of a level are walks of `Ĝ_ℓ`

An edge of finite length of the network of a level joins a copy and a dart at it, with length `0`,
or it is the middle edge of a kept dart, which is an arc of `Ĝ_ℓ` of the same length.

* `RData.levelStep_cases`: an edge of finite length stays at one copy with length `0`, or is an arc
  of `Ĝ_ℓ` between the copies of its ends with the same length.
* `RData.walk_project`: a walk of finite length of the network of a level gives a walk of `Ĝ_ℓ`
  between the copies of its ends, of the same length, through copies of its nodes only.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor SsspFlow.Congest
open scoped ENNReal

namespace RotSystem

namespace RData

variable {n : ℕ} {N : Net (Fin n)} (S : N.toRot.RData) (hN : ∀ u, ∃ w, N.G.Adj u w)
  (lam : S.Tok → ℕ) (M : ℕ)

/-- **One edge of the network of a level.** An edge of finite length stays at one copy with length
`0`, or it is an arc of `Ĝ_ℓ` of the same length. -/
theorem levelStep_cases {z z' : Fin (n * (n * 21))} (h : (S.levelNet hN).G.Adj z z')
    (hf : S.levelLen hN lam M z z' ≠ ⊤) :
    (S.copyAt hN z = S.copyAt hN z' ∧ S.levelLen hN lam M z z' = 0) ∨
      ∃ e : S.Arc (S.copyAt hN z) (S.copyAt hN z'),
        (S.arcW lam M _ _ e : ℕ∞) = S.levelLen hN lam M z z' := by
  classical
  have hnr : ∀ {x y}, (¬ (S.levelPad hN).IsReal x ∨ ¬ (S.levelPad hN).IsReal y) →
      S.levelLen hN lam M x y = ⊤ := fun hxy => by
    unfold levelLen
    rw [if_neg (fun h' => hxy.elim (· h'.1) (· h'.2))]
  rcases padNet_adj_cases h with ⟨x, y, rfl, rfl, hxy⟩ | ⟨hb, rfl⟩ | ⟨ha, rfl⟩
  · rw [S.copyAt_ι, S.copyAt_ι]
    rw [S.levelLen_ι] at hf ⊢
    rcases x with v | d <;> rcases y with w | d'
    · exact absurd hf (by simp)
    · obtain rfl : S.hRot.tail d' = v := hxy
      exact .inl ⟨rfl, rfl⟩
    · obtain rfl : S.hRot.tail d = w := hxy
      exact .inl ⟨rfl, rfl⟩
    · obtain rfl : d' = S.hRot.rev d := hxy
      by_cases hk : d ∈ S.keep
      · obtain ⟨e, he⟩ := S.arc_of_keep_w lam M d hk
        refine .inr ⟨e, ?_⟩
        simp only [show S.hRot.rev d = S.hrev d from rfl, true_and, hk, ite_true]
        exact congrArg (fun x : ℕ => (x : ℕ∞)) he
      · exact absurd hf (by simp [show S.hRot.rev d = S.hrev d from rfl, hk])
  · exact absurd (hnr (.inl hb)) hf
  · exact absurd (hnr (.inr ha)) hf

/-- **Walks project.** A walk of finite length of the network of a level gives a walk of `Ĝ_ℓ` between
the copies of its ends, of the same length, through copies of its nodes only. -/
theorem walk_project : ∀ {z z' : Fin (n * (n * 21))} (p : SsspFlow.Walk (S.levelNet hN).G.Adj z z'),
    p.wt (lenTop (S.levelLen hN lam M)) ≠ ⊤ →
    ∃ q : FaceDisjoint.Walk S.Arc (S.copyAt hN z) (S.copyAt hN z'),
      ((S.awt lam M q : ℕ) : ℝ≥0∞) = p.wt (lenTop (S.levelLen hN lam M)) ∧
        ∀ c ∈ q.support, ∃ y ∈ p.support, S.copyAt hN y = c
  | _, _, .nil z, _ => ⟨.nil _, by simp [awt, SsspFlow.Walk.wt], fun c hc => ⟨z, by simp,
      (List.mem_singleton.1 hc).symm⟩⟩
  | z, _, .cons (b := y) e p, hfin => by
    rw [SsspFlow.Walk.wt_cons] at hfin
    have hf1 : S.levelLen hN lam M z y ≠ ⊤ := fun h0 => hfin (by simp [lenTop, h0])
    have hf2 : p.wt (lenTop (S.levelLen hN lam M)) ≠ ⊤ := fun h0 => hfin (by rw [h0, add_top])
    obtain ⟨q, hq, hs⟩ := walk_project p hf2
    rcases S.levelStep_cases hN lam M e hf1 with ⟨hc, h0⟩ | ⟨e', he'⟩
    · rw [hc]
      refine ⟨q, ?_, fun c hc' => ?_⟩
      · rw [SsspFlow.Walk.wt_cons, hq]
        simp [lenTop, h0]
      · obtain ⟨y', hy', hc''⟩ := hs c hc'
        exact ⟨y', by simp [hy'], hc''⟩
    · refine ⟨.cons e' q, ?_, fun c hc' => ?_⟩
      · rw [SsspFlow.Walk.wt_cons, ← hq]
        simp only [awt, Nat.cast_add, lenTop]
        rw [← he']
        rfl
      · simp only [FaceDisjoint.Walk.support_cons, List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · exact ⟨z, by simp, rfl⟩
        · obtain ⟨y', hy', hc''⟩ := hs c hc'
          exact ⟨y', by simp [hy'], hc''⟩

end RData

end RotSystem

end SsspFlow
