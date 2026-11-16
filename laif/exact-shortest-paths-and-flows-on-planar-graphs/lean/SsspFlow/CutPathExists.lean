import SsspFlow.TheoremD
import SsspFlow.Crossing

/-!
# A shortest cut path exists

In a connected rotation system, for two corners on different faces there is a cut path between them
that is shortest for any natural lengths: take a walk of least length between the two vertices and
drop its loops. For the dual of a connected network, two corners at different vertices `s ≠ t` lie on
different faces of the dual.

* `RotSystem.walkV`: the vertices of a walk.
* `RotSystem.exists_shortest_cutPath`: a shortest cut path between two corners on different faces.
* `RotSystem.exists_shortest_cutPath_dual`: a shortest cut path of the dual from a corner at `s` to a
  corner at `t`, for `s ≠ t`.
-/

set_option autoImplicit false

universe u

namespace SsspFlow

open FourColor

namespace RotSystem

variable {D : Type u} [Fintype D] [DecidableEq D] (R : RotSystem D)

/-- The vertices of a walk from `u`: the vertex after `t` steps. -/
def walkV : R.Vertex → List D → ℕ → R.Vertex
  | u, [], _ => u
  | u, _ :: _, 0 => u
  | _, x :: q, t + 1 => walkV (R.head x) q t

variable {R}

theorem walkV_tail (x₀ : D) : ∀ {u v : R.Vertex} {q : List D}, R.IsWalk u q v →
    ∀ t, t < q.length → R.tail (q.getD t x₀) = R.walkV u q t
  | _, _, [], _, t, h => absurd h (Nat.not_lt_zero _)
  | _, _, x :: q, hq, 0, _ => hq.1
  | _, _, x :: q, hq, t + 1, h => walkV_tail x₀ hq.2 t (by simp at h; omega)

theorem walkV_head (x₀ : D) : ∀ {u v : R.Vertex} {q : List D}, R.IsWalk u q v →
    ∀ t, t < q.length → R.head (q.getD t x₀) = R.walkV u q (t + 1)
  | _, _, [], _, t, h => absurd h (Nat.not_lt_zero _)
  | _, _, [x], _, 0, _ => rfl
  | _, _, x :: y :: q, _, 0, _ => rfl
  | _, _, x :: q, hq, t + 1, h => walkV_head x₀ hq.2 t (by simp at h; omega)

theorem walkV_length : ∀ {u v : R.Vertex} {q : List D}, R.IsWalk u q v → R.walkV u q q.length = v
  | _, _, [], hq => hq
  | _, _, [x], hq => by simp only [walkV, List.length_singleton]; exact hq.2
  | _, _, x :: y :: q, hq => by
    have := walkV_length hq.2
    simpa [walkV] using this

theorem walkV_zero {u : R.Vertex} : ∀ q : List D, R.walkV u q 0 = u
  | [] => rfl
  | _ :: _ => rfl

variable (R)

/-- **A shortest cut path exists** between two corners on different faces of a connected rotation
system, for any natural lengths. -/
theorem exists_shortest_cutPath (hc : R.Connected) (w : D → ℕ) (cs ct : D)
    (hf : ¬ fconnect R.facePerm cs ct) :
    ∃ C : R.CutPath, C.cs = cs ∧ C.ct = ct ∧
      ∀ q, R.IsWalk (C.v 0) q (C.v C.m) → C.pos w C.m ≤ (q.map w).sum := by
  classical
  obtain ⟨-, hw⟩ := R.connected_iff.1 hc
  have hex : ∃ k, ∃ q, R.IsWalk (R.tail cs) q (R.tail ct) ∧ (q.map w).sum = k := by
    obtain ⟨p, hp⟩ := hw (R.tail cs) (R.tail ct)
    exact ⟨_, p, hp, rfl⟩
  obtain ⟨q₀, hq₀, hk⟩ := Nat.find_spec hex
  have hmin : ∀ q, R.IsWalk (R.tail cs) q (R.tail ct) → Nat.find hex ≤ (q.map w).sum :=
    fun q hq => Nat.find_min' hex ⟨q, hq, rfl⟩
  obtain ⟨q, hq, hnd, hne, hsub⟩ := hq₀.exists_simple
  have hle : (q.map w).sum ≤ (q₀.map w).sum := (hsub.map w).sum_le_sum (fun _ _ => Nat.zero_le _)
  let V : ℕ → R.Vertex := R.walkV (R.tail cs) q
  have htail := walkV_tail cs hq
  have hhead := walkV_head cs hq
  have hlen := walkV_length hq
  have hinj : ∀ s t, s ≤ q.length → t ≤ q.length → V s = V t → s = t := by
    intro s t hs ht he
    have key : ∀ a b, a < q.length → b ≤ q.length → V a = V b → a = b := by
      intro a b ha hb hab
      rcases Nat.lt_or_ge b q.length with hb' | hb'
      · have e1 := htail a ha
        have e2 := htail b hb'
        rw [List.getD_eq_getElem _ _ ha] at e1
        rw [List.getD_eq_getElem _ _ hb'] at e2
        have : (q.map R.tail)[a]'(by simpa using ha) = (q.map R.tail)[b]'(by simpa using hb') := by
          simp only [List.getElem_map]; rw [e1, e2]; exact hab
        exact (List.Nodup.getElem_inj_iff hnd).1 this
      · have hbq : b = q.length := le_antisymm hb hb'
        subst hbq
        have e1 := htail a ha
        rw [List.getD_eq_getElem _ _ ha] at e1
        exact absurd (e1.trans (hab.trans hlen)) (hne _ (List.getElem_mem ha))
    rcases Nat.lt_or_ge s q.length with hs' | hs'
    · exact key s t hs' ht he
    rcases Nat.lt_or_ge t q.length with ht' | ht'
    · exact (key t s ht' hs he.symm).symm
    · omega
  let C₀ : R.CutPath := ⟨q.length, V, fun t => q.getD t cs, cs, ct, fun t ht => htail t ht,
    fun t ht => hhead t ht, (walkV_zero q).symm, hlen.symm, hinj, hf⟩
  refine ⟨C₀, rfl, rfl, ?_⟩
  · intro q' hq'
    have hpos : ∀ t, t ≤ q.length → C₀.pos w t = ((q.map w).take t).sum := by
      intro t
      induction t with
      | zero => intro _; simp [CutPath.pos]
      | succ t ih =>
        intro ht
        simp only [CutPath.pos]
        rw [if_pos (show t < C₀.m from Nat.lt_of_succ_le ht), ih (by omega),
          List.sum_take_succ _ _ (by simpa using ht)]
        simp only [List.getElem_map]
        exact congrArg (fun y => _ + w y) (List.getD_eq_getElem _ _ _)
    show C₀.pos w q.length ≤ _
    rw [hpos _ le_rfl, List.take_of_length_le (by simp)]
    have h1 : R.IsWalk (R.tail cs) q' (R.tail ct) := by
      have e0 : V 0 = R.tail cs := walkV_zero q
      have em : V q.length = R.tail ct := hlen
      exact e0 ▸ em ▸ hq'
    exact hle.trans (hk ▸ hmin q' h1)

/-- **A shortest cut path of the dual from `s` to `t`.** For two different vertices `s ≠ t` of a
connected rotation system and any natural lengths, the dual has a shortest cut path whose end corners
lie at `s` and `t`. -/
theorem exists_shortest_cutPath_dual (hc : R.Connected) (w : D → ℕ) {s t : R.Vertex} (hst : s ≠ t) :
    ∃ C : R.dual.CutPath, R.tail C.cs = s ∧ R.tail C.ct = t ∧
      ∀ q, R.dual.IsWalk (C.v 0) q (C.v C.m) → C.pos w C.m ≤ (q.map w).sum := by
  obtain ⟨cs, rfl⟩ := R.exists_tail_eq s
  obtain ⟨ct, rfl⟩ := R.exists_tail_eq t
  have hf : ¬ fconnect R.dual.facePerm cs ct := by
    intro hfc
    apply hst
    have h' := (fconnect_congr R.dual.facePerm_apply).1 hfc
    rw [← R.dual_faceOf_eq_iff, faceOf_eq_iff]
    exact h'
  obtain ⟨C, h1, h2, h3⟩ := R.dual.exists_shortest_cutPath (R.connected_dual.2 hc) w cs ct hf
  exact ⟨C, h1 ▸ rfl, h2 ▸ rfl, h3⟩

end RotSystem

end SsspFlow
