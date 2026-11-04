import Dominators.Basic

/-!
# Dominance, immediate dominators, and Lemma 2

Lemma 2 is `lemma2`, in the form of `README.md`: `v ≠ r` reachable, and the quantifier runs over reachable
predecessors `w ≠ u`. The right-hand side does not assert that `(u, v)` is an edge. It follows.
-/

namespace Dominators

universe u

variable {V : Type u} {E : V → V → Prop} {r : V}

/-- Dominance does not change if only simple paths are considered. -/
theorem dominates_iff_paths {d w : V} :
    Dominates E r d w ↔ ∀ p : Walk E r w, p.IsPath → d ∈ p.support := by
  constructor
  · exact fun h p _ => h p
  · intro h p
    obtain ⟨q, hq, hs, _⟩ := p.exists_isPath
    exact hs (h q hq)

/-- Lying on every path does not change if only simple paths are considered. -/
theorem onAllPaths_iff_paths {u v : V} :
    OnAllPaths E r u v ↔ ∀ p : Walk E r v, p.IsPath → (u, v) ∈ p.edges := by
  constructor
  · exact fun h p _ => h p
  · intro h p
    obtain ⟨q, hq, _, he⟩ := p.exists_isPath
    exact he (h q hq)

theorem Dominates.refl (r w : V) : Dominates E r w w := fun p => p.end_mem

theorem Dominates.root (r w : V) : Dominates E r r w := fun p => p.start_mem

/-- `d` does not dominate `w` iff some walk avoids it. -/
theorem not_dominates_iff {d w : V} : ¬ Dominates E r d w ↔ ∃ p : Walk E r w, d ∉ p.support := by
  simp [Dominates]

/-- Dominance is reachability from `r` failing in `G - d`. -/
theorem dominates_iff_not_reach_delVertex {d w : V} (hr : r ≠ d) (hw : w ≠ d) :
    Dominates E r d w ↔ ¬ Reach (delVertex E d) ⟨r, hr⟩ ⟨w, hw⟩ := by
  rw [reach_delVertex_iff]
  simp [Dominates]

/-- On a simple path, the prefix up to `a ≠ b` does not contain the end `b`. -/
theorem Walk.prefix_of_isPath {x b a : V} (p : Walk E x b) (hp : p.IsPath) (h : a ∈ p.support) (hab : a ≠ b) :
    ∃ q : Walk E x a, q.support ⊆ p.support ∧ b ∉ q.support := by
  induction p with
  | nil v =>
    simp only [Walk.support_nil, List.mem_singleton] at h
    exact absurd h hab
  | @cons x y b hxy p ih =>
    have hnd : (x :: p.support).Nodup := hp
    have hxp := (List.nodup_cons.mp hnd).1
    have hxb : b ≠ x := fun e => hxp (e ▸ p.end_mem)
    by_cases hax : a = x
    · subst hax
      exact ⟨.nil a, by simp, by simpa using hxb⟩
    · have ha : a ∈ p.support := by simpa [hax] using h
      obtain ⟨q, h1, h2⟩ := ih (List.nodup_cons.mp hnd).2 ha hab
      refine ⟨.cons hxy q, ?_, ?_⟩
      · intro t ht
        simp only [Walk.support_cons, List.mem_cons] at ht ⊢
        rcases ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (h1 ht)
      · simp only [Walk.support_cons, List.mem_cons, not_or]
        exact ⟨hxb, h2⟩

/-- A walk has a prefix up to any of its vertices. -/
theorem Walk.prefix {x b a : V} (p : Walk E x b) (h : a ∈ p.support) :
    ∃ q : Walk E x a, q.support ⊆ p.support := by
  induction p with
  | nil v =>
    simp only [Walk.support_nil, List.mem_singleton] at h
    subst h
    exact ⟨.nil _, by simp⟩
  | @cons x y b hxy p ih =>
    by_cases hax : a = x
    · subst hax
      exact ⟨.nil a, by simp⟩
    · have ha : a ∈ p.support := by simpa [hax] using h
      obtain ⟨q, h1⟩ := ih ha
      refine ⟨.cons hxy q, ?_⟩
      intro t ht
      simp only [Walk.support_cons, List.mem_cons] at ht ⊢
      rcases ht with rfl | ht
      · exact Or.inl rfl
      · exact Or.inr (h1 ht)

/-- Dominance is transitive. -/
theorem Dominates.trans {a b c : V} (h1 : Dominates E r a b) (h2 : Dominates E r b c) : Dominates E r a c := by
  intro p
  obtain ⟨q, hq⟩ := p.prefix (h2 p)
  exact hq (h1 q)

/-- Dominance is antisymmetric on reachable vertices. -/
theorem Dominates.not_symm {d w : V} (hw : Reach E r w) (hd : d ≠ w) (h : Dominates E r d w) :
    ¬ Dominates E r w d := by
  obtain ⟨p⟩ := hw
  obtain ⟨q, hq, hs, _⟩ := p.exists_isPath
  obtain ⟨q', _, h2⟩ := q.prefix_of_isPath hq (h q) hd
  exact fun h' => h2 (h' q')

/-- A dominator of a reachable vertex is reachable. -/
theorem Dominates.reach {d w : V} (hw : Reach E r w) (h : Dominates E r d w) : Reach E r d := by
  obtain ⟨p⟩ := hw
  obtain ⟨q, _⟩ := p.prefix (h p)
  exact ⟨q⟩

/-! ## Immediate dominators exist and are unique -/

/-- The last vertex on a walk with a given property. -/
theorem Walk.exists_last {x w : V} (P : V → Prop) (p : Walk E x w) (h : ∃ t ∈ p.support, P t) :
    ∃ u, P u ∧ ∃ q : Walk E u w, ∀ t ∈ q.support, P t → t = u := by
  induction p with
  | nil v =>
    obtain ⟨t, ht, hP⟩ := h
    simp only [Walk.support_nil, List.mem_singleton] at ht
    subst ht
    refine ⟨t, hP, .nil t, ?_⟩
    simp
  | @cons x y w hxy p ih =>
    by_cases h' : ∃ t ∈ p.support, P t
    · exact ih h'
    · obtain ⟨t, ht, hP⟩ := h
      have htx : t = x := by
        simp only [Walk.support_cons, List.mem_cons] at ht
        rcases ht with ht | ht
        · exact ht
        · exact absurd ⟨t, ht, hP⟩ h'
      subst htx
      refine ⟨t, hP, .cons hxy p, ?_⟩
      intro s hs hPs
      simp only [Walk.support_cons, List.mem_cons] at hs
      rcases hs with hs | hs
      · exact hs
      · exact absurd ⟨s, hs, hPs⟩ h'

/-- Every reachable vertex other than the root has an immediate dominator. -/
theorem exists_idom {w : V} (hw : Reach E r w) (hwr : w ≠ r) : ∃ u, IsIdom E r u w := by
  obtain ⟨p⟩ := id hw
  obtain ⟨u, ⟨huw, hud⟩, q, hq⟩ := p.exists_last (fun t => t ≠ w ∧ Dominates E r t w)
    ⟨r, p.start_mem, Ne.symm hwr, Dominates.root r w⟩
  refine ⟨u, hw, huw, hud, ?_⟩
  intro d hdw hd
  by_contra hne
  obtain ⟨Q, hQ⟩ := not_dominates_iff.mp hne
  have := hd (Q.append q)
  rw [Walk.mem_support_append] at this
  rcases this with h | h
  · exact hQ h
  · have hdu := hq d h ⟨hdw, hd⟩
    exact hQ (hdu ▸ Q.end_mem)

/-- The immediate dominator is unique. -/
theorem IsIdom.unique {u u' w : V} (h : IsIdom E r u w) (h' : IsIdom E r u' w) : u = u' := by
  by_contra hne
  have h1 : Dominates E r u' u := h.2.2.2 u' h'.2.1 h'.2.2.1
  have h2 : Dominates E r u u' := h'.2.2.2 u h.2.1 h.2.2.1
  exact Dominates.not_symm (h.2.2.1.reach h.1) (Ne.symm hne) h1 h2

/-- The root has no immediate dominator. -/
theorem not_isIdom_root (u : V) : ¬ IsIdom E r u r := by
  rintro ⟨_, h1, h2, _⟩
  have := h2 (.nil r)
  simp at this
  exact h1 this

/-! ## Lemma 2 -/

/-- **Lemma 2.** Let `v ≠ r` be reachable. The edge `(u, v)` is on every path from `r` to `v` iff
`u = idom(v)` and `v` dominates every reachable predecessor `w ≠ u` of `v`. -/
theorem lemma2 {u v : V} (hv : Reach E r v) (hvr : v ≠ r) :
    OnAllPaths E r u v ↔
      IsIdom E r u v ∧ ∀ w, Reach E r w → E w v → w ≠ u → Dominates E r v w := by
  constructor
  · intro h
    obtain ⟨P⟩ := id hv
    have hfa := P.firstArrival
    rcases hfa with hrv | ⟨w', q, hw', hvq, _, _, _⟩
    · exact absurd hrv.symm hvr
    have huw : u = w' := by
      have := h (q.snoc hw')
      rw [Walk.mem_edges_snoc] at this
      rcases this with h1 | h1
      · exact absurd (q.mem_support_of_mem_edges h1).2 hvq
      · exact (Prod.mk.inj h1).1
    subst huw
    have huv : u ≠ v := fun e => hvq (e ▸ q.end_mem)
    refine ⟨⟨hv, huv, fun p => (p.mem_support_of_mem_edges (h p)).1, ?_⟩, ?_⟩
    · intro d hdv hd Q
      have := hd (Q.snoc hw')
      rw [Walk.mem_support_snoc] at this
      exact this.resolve_right hdv
    · rintro w ⟨Q⟩ hwv hwu Q'
      have := h (Q'.snoc hwv)
      rw [Walk.mem_edges_snoc] at this
      rcases this with h1 | h1
      · exact (Q'.mem_support_of_mem_edges h1).2
      · exact absurd (Prod.mk.inj h1).1.symm hwu
  · rintro ⟨_, hdom⟩ P
    rcases P.firstArrival with hrv | ⟨w', q, hw', hvq, _, _, hl⟩
    · exact absurd hrv.symm hvr
    by_cases hwu : w' = u
    · exact hwu ▸ hl
    · exact absurd (hdom w' ⟨q⟩ hw' hwu q) hvq

/-- An edge on every path to its reachable head is an edge. -/
theorem OnAllPaths.edge {u v : V} (hv : Reach E r v) (h : OnAllPaths E r u v) : E u v := by
  obtain ⟨P⟩ := hv
  exact P.edge_of_mem_edges (h P)

/-- The bridge test of `README.md`, read off from Lemma 2: for reachable `v ≠ r`, the edge `(u, v)` is a bridge
iff `u = idom(v)` and no reachable predecessor `w ≠ u` of `v` is left undominated by `v`. -/
theorem isBridge_iff_test {u v : V} (hv : Reach E r v) (hvr : v ≠ r) :
    IsBridge E r u v ↔
      IsIdom E r u v ∧ ¬ ∃ w, Reach E r w ∧ E w v ∧ w ≠ u ∧ ¬ Dominates E r v w := by
  rw [IsBridge]
  constructor
  · rintro ⟨_, _, h⟩
    obtain ⟨h1, h2⟩ := (lemma2 hv hvr).mp h
    exact ⟨h1, fun ⟨w, a, b, c, d⟩ => d (h2 w a b c)⟩
  · rintro ⟨h1, h2⟩
    have h3 : OnAllPaths E r u v := (lemma2 hv hvr).mpr ⟨h1, fun w a b c => by
      by_contra d
      exact h2 ⟨w, a, b, c, d⟩⟩
    exact ⟨h3.edge hv, hv, h3⟩

/-- A bridge is exactly an edge whose removal cuts its head off from `r`. -/
theorem onAllPaths_iff_not_reach_delEdge {u v : V} :
    OnAllPaths E r u v ↔ ¬ Reach (delEdge E u v) r v := by
  rw [reach_delEdge_iff]
  simp [OnAllPaths]

/-- An edge whose removal cuts off some vertex cuts off its own head. So a bridge in the sense of "on every
path to its head" is the same as an edge whose removal makes some vertex unreachable. -/
theorem isBridge_iff_cuts {u v : V} (h : E u v) (hu : Reach E r u) :
    IsBridge E r u v ↔ ∃ x, Reach E r x ∧ ¬ Reach (delEdge E u v) r x := by
  constructor
  · rintro ⟨_, hv, ho⟩
    exact ⟨v, hv, onAllPaths_iff_not_reach_delEdge.mp ho⟩
  · rintro ⟨x, hx, hn⟩
    refine ⟨h, hu.tail h, onAllPaths_iff_not_reach_delEdge.mpr fun hrv => hn ?_⟩
    rcases reach_delEdge_or (u := u) (v := v) hx with h1 | h1
    · exact h1
    · exact hrv.trans h1

end Dominators
