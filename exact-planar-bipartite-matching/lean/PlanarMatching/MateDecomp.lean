import PlanarMatching.MateSearch
import PlanarMatching.ElimDecomp

/-!
# The search for mates on the tree of bags

`notes/GENERAL.md`, Section 4, Lemma 6, on a rooted `Decomp` whose bags are numbered children first. The bags run
parents first, bag `t` being `bag (T - 1 - t)`. The part of a bag `X` is `X°`, the vertices with `X` on their chain,
and its hubs include the vertices of `X°` on the separator of `X` (all of `X°` at a leaf, where the separator is
everything). The entries of `A` lie on arcs of the root.

* `Decomp.escape`: if an edge joins `i ∈ X°` to `j ∉ X°`, the chain of `j` stops strictly above `X`.
* `mates_decomp` (Lemma 6): if `A_{B,B}` is nonsingular, the search matches `B` perfectly by edges of `A`, for any
  rule that picks a candidate.
-/

namespace PlanarMatching

open Matrix Relation

set_option linter.unusedSectionVars false

variable {V B : Type*} (D : Decomp V B)

/-- If an arc of `b` joins `i`, on the chain of `X`, to `j`, off it, then the chain of `j` stops at a bag strictly
above `X`. -/
theorem Decomp.escape {X b : B} {i j : V} (hi : D.OnChain X i b) (a : D.arc b i j ∨ D.arc b j i)
    (hj : ¬ D.OnChain X j b) : ∃ Z, D.OnChain Z j b ∧ D.sep Z j ∧ TransGen D.child X Z := by
  induction b using D.wf.induction with
  | _ b ih =>
  have hjb : D.verts b j := a.elim (fun a => (D.arc_mem a).2) (fun a => (D.arc_mem a).1)
  cases hi with
  | here _ => exact absurd (.here hjb) hj
  | down hc hb hs hrest =>
    by_cases hsj : D.sep b j
    · exact ⟨b, .here hjb, hsj, TransGen.tail' (Decomp.OnChain.toTop D hrest) hc⟩
    · obtain ⟨c', hc', ha⟩ : ∃ c', D.child c' b ∧ (D.arc c' i j ∨ D.arc c' j i) := by
        rcases a with a | a
        · obtain ⟨c', hc', ha⟩ := D.arc_child a ⟨_, hc⟩; exact ⟨c', hc', Or.inl ha⟩
        · obtain ⟨c', hc', ha⟩ := D.arc_child a ⟨_, hc⟩; exact ⟨c', hc', Or.inr ha⟩
      have hic' : D.verts c' i := ha.elim (fun a => (D.arc_mem a).1) (fun a => (D.arc_mem a).2)
      have e := D.uniq hc hc' (Decomp.OnChain.mem_top D hrest) hic' hs
      subst e
      obtain ⟨Z, h1, h2, h3⟩ := ih _ hc hrest ha (fun h' => hj (.down hc hjb hsj h'))
      exact ⟨Z, .down hc hjb hsj h1, h2, h3⟩

variable {K : Type*} [Field K] [Fintype V] [DecidableEq V]

open Classical in
/-- The part `X°` of the bag run at step `t`. -/
noncomputable def partOf (r : B) (bag : ℕ → B) (T t : ℕ) : Finset V :=
  Finset.univ.filter fun x => D.OnChain (bag (T - 1 - t)) x r

/-- The unmatched vertices before step `t`. -/
noncomputable def unmatched (B₀ : Finset V) (O : ℕ → Finset V) (H : ℕ → List V) (pick : Finset V → V → V) :
    ℕ → Finset V
  | 0 => B₀
  | t + 1 => (unmatched B₀ O H pick t \ (unmatched B₀ O H pick t ∩ O t)) ∪
      (search pick (H t) (unmatched B₀ O H pick t ∩ O t)).2

section

variable {B₀ : Finset V} {O : ℕ → Finset V} {H : ℕ → List V} {pick : Finset V → V → V}

theorem unmatched_mono (t : ℕ) : unmatched B₀ O H pick (t + 1) ⊆ unmatched B₀ O H pick t :=
  Finset.union_subset Finset.sdiff_subset ((search_sub pick _ _).trans Finset.inter_subset_left)

theorem unmatched_mono_le {s t : ℕ} (hst : s ≤ t) : unmatched B₀ O H pick t ⊆ unmatched B₀ O H pick s := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih => exact (unmatched_mono t).trans ih

/-- A vertex that is a hub of a step whose part holds it is matched after that step. -/
theorem unmatched_hub {t : ℕ} {x : V} (hO : x ∈ O t) (hH : x ∈ H t) : x ∉ unmatched B₀ O H pick (t + 1) := by
  intro hx
  simp only [unmatched, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at hx
  rcases hx with ⟨h1, h2⟩ | h2
  · exact h2 ⟨h1, hO⟩
  · exact search_hub pick _ _ x hH h2

end

theorem Decomp.Rooted.lt_of_trans {r : B} {T : ℕ} {bag : ℕ → B} {idx : B → ℕ} (hR : D.Rooted r T bag idx)
    {a c : B} (h : TransGen D.child a c) : idx a < idx c := by
  induction h with
  | single h => exact hR.order h
  | tail _ h ih => exact ih.trans (hR.order h)

/-- **Lemma 6** on a rooted tree of bags. If `A_{B,B}` is nonsingular, and the hubs of each bag include the vertices
of its part on its separator, then the search matches `B` perfectly by edges of `A`, for any rule that picks a
candidate. -/
theorem mates_decomp {r : B} {T : ℕ} {bag : ℕ → B} {idx : B → ℕ} (hR : D.Rooted r T bag idx)
    {A : Matrix V V K} (hA : IsAlternating A) (harc : ∀ i j, A i j ≠ 0 → D.arc r i j)
    {B₀ : Finset V} (hB : Nsg A B₀) {H : ℕ → List V}
    (hH : ∀ t < T, ∀ x, x ∈ partOf D r bag T t → D.sep (bag (T - 1 - t)) x → x ∈ H t)
    {pick : Finset V → V → V} (hpick : ∀ U s, (cand A U s).Nonempty → pick U s ∈ cand A U s) :
    let O := partOf D r bag T
    let U := unmatched B₀ O H pick
    (∀ t < T, ∀ p ∈ Sched.pairs O H pick U t, A p.1 p.2 ≠ 0) ∧
      ((List.range T).flatMap fun t => ends (Sched.pairs O H pick U t)).Nodup ∧
      ∀ x, x ∈ (List.range T).flatMap (fun t => ends (Sched.pairs O H pick U t)) ↔ x ∈ B₀ := by
  intro O U
  -- the step at which the home of a vertex runs
  have hstep : ∀ x, T - 1 - (T - 1 - idx (D.homeBag r x)) = idx (D.homeBag r x) := fun x => by
    have := hR.idx_lt (D.homeBag r x); omega
  have hbag : ∀ x, bag (T - 1 - (T - 1 - idx (D.homeBag r x))) = D.homeBag r x := fun x => by
    rw [hstep, hR.bag_idx]
  have hspec := fun x => D.homeBag_spec (r := r) (hR.root_verts x)
  -- a vertex is matched once the step of its home has run
  have hgone : ∀ x t, T - 1 - idx (D.homeBag r x) < t → x ∉ U t := by
    intro x t ht hx
    have hO : x ∈ O (T - 1 - idx (D.homeBag r x)) := by
      simp only [O, partOf, Finset.mem_filter, Finset.mem_univ, true_and]; rw [hbag]; exact (hspec x).1
    have hHx := hH _ (by have := hR.idx_lt (D.homeBag r x); omega) x hO (by rw [hbag]; exact (hspec x).2)
    exact unmatched_hub hO hHx (unmatched_mono_le ht hx)
  have hS : Sched A B₀ O H pick U T := by
    refine ⟨rfl, fun t _ => rfl, fun t ht i hi j hj => ?_, fun b _ => ?_⟩
    · have hiO := (Finset.mem_inter.1 hi).2
      have hjU := (Finset.mem_sdiff.1 hj).1
      have hjO : j ∉ O t := fun h' => (Finset.mem_sdiff.1 hj).2 (Finset.mem_inter.2 ⟨hjU, h'⟩)
      simp only [O, partOf, Finset.mem_filter, Finset.mem_univ, true_and] at hiO hjO
      have key : (D.arc r i j ∨ D.arc r j i) → False := fun a => by
        obtain ⟨Z, h1, h2, h3⟩ := D.escape hiO a hjO
        have hZ := D.bottom_unique h1 h2 (hspec j).1 (hspec j).2
        subst hZ
        have hlt := Decomp.Rooted.lt_of_trans D hR h3
        have hX : idx (bag (T - 1 - t)) = T - 1 - t := hR.idx_bag _ (by omega)
        rw [hX] at hlt
        have hjT := hR.idx_lt (D.homeBag r j)
        have hgoal : T - 1 - idx (D.homeBag r j) < t := by omega
        exact hgone j t hgoal hjU
      refine ⟨?_, ?_⟩
      · by_contra h0; exact key (Or.inl (harc i j h0))
      · by_contra h0; exact key (Or.inr (harc j i h0))
    · refine ⟨T - 1 - idx (D.homeBag r b), by have := hR.idx_lt (D.homeBag r b); omega, ?_, ?_⟩
      · simp only [O, partOf, Finset.mem_filter, Finset.mem_univ, true_and]; rw [hbag]; exact (hspec b).1
      · exact hH _ (by have := hR.idx_lt (D.homeBag r b); omega) b
          (by simp only [O, partOf, Finset.mem_filter, Finset.mem_univ, true_and]; rw [hbag]; exact (hspec b).1)
          (by rw [hbag]; exact (hspec b).2)
  exact hS.matched hA hpick hB

end PlanarMatching
