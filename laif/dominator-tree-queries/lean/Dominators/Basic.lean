import Dominators.Model

/-!
# Walks: cutting, removal, reversal, counting components
-/

namespace Dominators

universe u

variable {V : Type u} {E : V → V → Prop}

namespace Walk

@[simp] theorem support_nil (v : V) : (Walk.nil v : Walk E v v).support = [v] := rfl
@[simp] theorem support_cons {x y z : V} (h : E x y) (p : Walk E y z) :
    (Walk.cons h p).support = x :: p.support := rfl
@[simp] theorem edges_nil (v : V) : (Walk.nil v : Walk E v v).edges = [] := rfl
@[simp] theorem edges_cons {x y z : V} (h : E x y) (p : Walk E y z) :
    (Walk.cons h p).edges = (x, y) :: p.edges := rfl
@[simp] theorem nil_append {x y : V} (q : Walk E x y) : (Walk.nil x).append q = q := rfl
@[simp] theorem cons_append {x y z w : V} (h : E x y) (p : Walk E y z) (q : Walk E z w) :
    (Walk.cons h p).append q = Walk.cons h (p.append q) := rfl

theorem start_mem {x y : V} (p : Walk E x y) : x ∈ p.support := by
  cases p <;> simp

theorem end_mem {x y : V} (p : Walk E x y) : y ∈ p.support := by
  induction p with
  | nil v => simp
  | cons h p ih => simp [ih]

theorem mem_support_append {x y z d : V} (p : Walk E x y) (q : Walk E y z) :
    d ∈ (p.append q).support ↔ d ∈ p.support ∨ d ∈ q.support := by
  induction p with
  | nil v =>
    simp only [nil_append, support_nil, List.mem_singleton]
    constructor
    · exact Or.inr
    · rintro (rfl | h)
      · exact q.start_mem
      · exact h
  | cons h p ih => simp [ih, or_assoc]

theorem mem_edges_append {x y z : V} {e : V × V} (p : Walk E x y) (q : Walk E y z) :
    e ∈ (p.append q).edges ↔ e ∈ p.edges ∨ e ∈ q.edges := by
  induction p with
  | nil v => simp
  | cons h p ih => simp [ih, or_assoc]

/-- A one-edge extension at the end. -/
def snoc {x y z : V} (p : Walk E x y) (h : E y z) : Walk E x z :=
  p.append (.cons h (.nil z))

theorem mem_support_snoc {x y z d : V} (p : Walk E x y) (h : E y z) :
    d ∈ (p.snoc h).support ↔ d ∈ p.support ∨ d = z := by
  rw [snoc, mem_support_append]
  simp only [support_cons, support_nil, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (h | rfl | h)
    · exact Or.inl h
    · exact Or.inl p.end_mem
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

theorem mem_edges_snoc {x y z : V} {e : V × V} (p : Walk E x y) (h : E y z) :
    e ∈ (p.snoc h).edges ↔ e ∈ p.edges ∨ e = (y, z) := by
  rw [snoc, mem_edges_append]
  simp

/-- Both ends of an edge of a walk are on it. -/
theorem mem_support_of_mem_edges {x y a b : V} (p : Walk E x y) (h : (a, b) ∈ p.edges) :
    a ∈ p.support ∧ b ∈ p.support := by
  induction p with
  | nil v => simp at h
  | @cons x y z hxy p ih =>
    simp only [edges_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact ⟨by simp, by simp [p.start_mem]⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨by simp [h1], by simp [h2]⟩

/-- An edge of a walk is an edge of the graph. -/
theorem edge_of_mem_edges {x y a b : V} (p : Walk E x y) (h : (a, b) ∈ p.edges) : E a b := by
  induction p with
  | nil v => simp at h
  | @cons x y z hxy p ih =>
    simp only [edges_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact hxy
    · exact ih h

/-- Cut a walk at its first arrival at its end: either the walk is trivial or it has a prefix that contains
the end only as its last vertex. -/
theorem firstArrival {x v : V} (p : Walk E x v) :
    x = v ∨ ∃ (w : V) (q : Walk E x w) (_ : E w v), v ∉ q.support ∧ q.support ⊆ p.support ∧
      q.edges ⊆ p.edges ∧ (w, v) ∈ p.edges := by
  induction p with
  | nil v => exact Or.inl rfl
  | @cons x y v hxy p ih =>
    by_cases hxv : x = v
    · exact Or.inl hxv
    right
    rcases ih with rfl | ⟨w, q, h, hv, hs, he, hl⟩
    · refine ⟨x, .nil x, hxy, by simpa using Ne.symm hxv, by simp, by simp, by simp⟩
    · refine ⟨w, .cons hxy q, h, ?_, ?_, ?_, ?_⟩
      · simp only [support_cons, List.mem_cons, not_or]
        exact ⟨Ne.symm hxv, hv⟩
      · intro a ha
        simp only [support_cons, List.mem_cons] at ha ⊢
        rcases ha with rfl | ha
        · exact Or.inl rfl
        · exact Or.inr (hs ha)
      · intro a ha
        simp only [edges_cons, List.mem_cons] at ha ⊢
        rcases ha with rfl | ha
        · exact Or.inl rfl
        · exact Or.inr (he ha)
      · simp [hl]

/-- A walk with no repeated vertex. -/
def IsPath {x y : V} (p : Walk E x y) : Prop := p.support.Nodup

open Classical in
/-- Every walk contains a simple path with the same ends. So "every path contains `d`" means the same for
walks and for simple paths. -/
theorem exists_isPath {x y : V} (p : Walk E x y) :
    ∃ q : Walk E x y, q.IsPath ∧ q.support ⊆ p.support ∧ q.edges ⊆ p.edges := by
  induction p with
  | nil v => exact ⟨.nil v, by simp [IsPath], by simp, by simp⟩
  | @cons x y z hxy p ih =>
    obtain ⟨q, hq, hs, he⟩ := ih
    by_cases hx : x ∈ q.support
    · -- drop the prefix of `q` up to `x`
      have key : ∀ {a b : V} (q : Walk E a b), q.IsPath → x ∈ q.support →
          ∃ q' : Walk E x b, q'.IsPath ∧ q'.support ⊆ q.support ∧ q'.edges ⊆ q.edges := by
        intro a b q hq hx
        induction q with
        | nil v =>
          simp only [support_nil, List.mem_singleton] at hx
          subst hx
          exact ⟨.nil _, by simp [IsPath], by simp, by simp⟩
        | @cons a c b hac q ih =>
          by_cases hxa : x = a
          · subst hxa
            exact ⟨.cons hac q, hq, by simp, by simp⟩
          · have hq' : q.IsPath := by
              have : (a :: q.support).Nodup := hq
              exact (List.nodup_cons.mp this).2
            have hx' : x ∈ q.support := by
              simpa [hxa] using hx
            obtain ⟨q', h1, h2, h3⟩ := ih hq' hx'
            refine ⟨q', h1, ?_, ?_⟩
            · intro t ht
              simpa using Or.inr (h2 ht)
            · intro t ht
              simpa using Or.inr (h3 ht)
      obtain ⟨q', h1, h2, h3⟩ := key q hq hx
      refine ⟨q', h1, ?_, ?_⟩
      · intro t ht
        simpa using Or.inr (hs (h2 ht))
      · intro t ht
        simpa using Or.inr (he (h3 ht))
    · refine ⟨.cons hxy q, ?_, ?_, ?_⟩
      · exact List.nodup_cons.mpr ⟨hx, hq⟩
      · intro t ht
        simp only [support_cons, List.mem_cons] at ht ⊢
        rcases ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (hs ht)
      · intro t ht
        simp only [edges_cons, List.mem_cons] at ht ⊢
        rcases ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (he ht)

/-- Reverse a walk. -/
def reverse : {x y : V} → Walk E x y → Walk (rev E) y x
  | _, _, .nil v => .nil v
  | _, _, .cons h p => p.reverse.append (.cons h (.nil _))

theorem mem_support_reverse {x y d : V} (p : Walk E x y) : d ∈ p.reverse.support ↔ d ∈ p.support := by
  induction p with
  | nil v => simp [reverse]
  | @cons x y z hxy p ih =>
    simp only [reverse, mem_support_append, ih, support_cons, support_nil, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro (h | h | h)
      · exact Or.inr h
      · have : d ∈ p.support := by rw [h]; exact p.start_mem
        exact Or.inr this
      · exact Or.inl h
    · rintro (h | h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h

theorem mem_edges_reverse {x y a b : V} (p : Walk E x y) :
    (a, b) ∈ p.reverse.edges ↔ (b, a) ∈ p.edges := by
  induction p with
  | nil v => simp [reverse]
  | @cons x y z hxy p ih =>
    simp only [reverse, mem_edges_append, ih, edges_cons, edges_nil, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false]
    constructor
    · rintro (h | ⟨rfl, rfl⟩)
      · exact Or.inr h
      · exact Or.inl ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | h)
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl h

end Walk

@[simp] theorem rev_rev (E : V → V → Prop) : rev (rev E) = E := rfl

theorem Reach.edge {x y : V} (h : E x y) : Reach E x y := ⟨.cons h (.nil y)⟩

theorem Reach.head {x y z : V} (h : E x y) (h' : Reach E y z) : Reach E x z := (Reach.edge h).trans h'

theorem Reach.tail {x y z : V} (h' : Reach E x y) (h : E y z) : Reach E x z := h'.trans (Reach.edge h)

theorem reach_rev {x y : V} : Reach (rev E) x y ↔ Reach E y x :=
  ⟨fun ⟨p⟩ => ⟨p.reverse⟩, fun ⟨p⟩ => ⟨p.reverse⟩⟩

/-- A closed set contains everything reachable from it. -/
theorem Reach.mem_of_closed {S : V → Prop} (hS : ∀ a b, S a → E a b → S b) {x y : V} (h : Reach E x y)
    (hx : S x) : S y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil v => exact hx
  | cons hxy p ih => exact ih (hS _ _ hx hxy)

/-- Reachability with a smaller edge set. -/
theorem Reach.mono {F : V → V → Prop} (hF : ∀ a b, E a b → F a b) {x y : V} (h : Reach E x y) :
    Reach F x y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil v => exact Reach.refl F v
  | cons hxy p ih => exact Reach.head (hF _ _ hxy) ih

/-- Reachability maps along a function that maps edges to edges. -/
theorem Reach.map {W : Type*} {F : W → W → Prop} (f : V → W) (hf : ∀ a b, E a b → F (f a) (f b)) {x y : V}
    (h : Reach E x y) : Reach F (f x) (f y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil a => exact Reach.refl F (f a)
  | cons hxy _ ih => exact Reach.head (hf _ _ hxy) ih

theorem Mutual.mono {F : V → V → Prop} (hF : ∀ a b, E a b → F a b) {x y : V} (h : Mutual E x y) :
    Mutual F x y := ⟨h.1.mono hF, h.2.mono hF⟩

/-! ## Removing an edge -/

theorem reach_delEdge_iff {u v x y : V} :
    Reach (delEdge E u v) x y ↔ ∃ p : Walk E x y, (u, v) ∉ p.edges := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil a => exact ⟨.nil a, by simp⟩
    | @cons a b c hab p ih =>
      obtain ⟨q, hq⟩ := ih
      refine ⟨.cons hab.1 q, ?_⟩
      simp only [Walk.edges_cons, List.mem_cons, Prod.mk.injEq, not_or]
      exact ⟨fun ⟨h1, h2⟩ => hab.2 ⟨h1.symm, h2.symm⟩, hq⟩
  · rintro ⟨p, hp⟩
    induction p with
    | nil a => exact Reach.refl _ a
    | @cons a b c hab p ih =>
      simp only [Walk.edges_cons, List.mem_cons, Prod.mk.injEq, not_or] at hp
      exact Reach.head ⟨hab, fun ⟨h1, h2⟩ => hp.1 ⟨h1.symm, h2.symm⟩⟩ (ih hp.2)

/-- A walk either avoids the edge `(u, v)`, or has a suffix from `v` that avoids it. -/
theorem reach_delEdge_or {u v x y : V} (h : Reach E x y) :
    Reach (delEdge E u v) x y ∨ Reach (delEdge E u v) v y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil a => exact Or.inl (Reach.refl _ a)
  | @cons a b c hab p ih =>
    rcases ih with h | h
    · by_cases he : a = u ∧ b = v
      · right
        obtain ⟨_, rfl⟩ := he
        exact h
      · exact Or.inl (Reach.head ⟨hab, he⟩ h)
    · exact Or.inr h

/-- A walk avoiding the edge, or passing through its tail and then its head. -/
theorem reach_delEdge_or' {u v x y : V} (h : Reach E x y) :
    Reach (delEdge E u v) x y ∨ (Reach E x u ∧ Reach (delEdge E u v) v y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil a => exact Or.inl (Reach.refl _ a)
  | @cons a b c hab p ih =>
    by_cases he : a = u ∧ b = v
    · obtain ⟨rfl, rfl⟩ := he
      rcases ih with h | ⟨_, h⟩
      · exact Or.inr ⟨Reach.refl _ _, h⟩
      · exact Or.inr ⟨Reach.refl _ _, h⟩
    · rcases ih with h | ⟨h1, h2⟩
      · exact Or.inl (Reach.head ⟨hab, he⟩ h)
      · exact Or.inr ⟨Reach.head hab h1, h2⟩

theorem delEdge_le (E : V → V → Prop) (u v : V) : ∀ a b, delEdge E u v a b → E a b := fun _ _ h => h.1

theorem rev_delEdge (E : V → V → Prop) (u v : V) : rev (delEdge E u v) = delEdge (rev E) v u := by
  funext x y
  simp only [rev, delEdge, eq_iff_iff]
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h, fun ⟨h1, h2⟩ => h' ⟨h2, h1⟩⟩
  · rintro ⟨h, h'⟩
    exact ⟨h, fun ⟨h1, h2⟩ => h' ⟨h2, h1⟩⟩

/-! ## Removing a vertex -/

/-- Reachability in `G - d` is reachability by walks avoiding `d`. -/
theorem reach_delVertex_iff {d : V} {x y : {a : V // a ≠ d}} :
    Reach (delVertex E d) x y ↔ ∃ p : Walk E x.1 y.1, d ∉ p.support := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil a => exact ⟨.nil a.1, by simpa using Ne.symm a.2⟩
    | @cons a b c hab p ih =>
      obtain ⟨q, hq⟩ := ih
      refine ⟨.cons hab q, ?_⟩
      simp only [Walk.support_cons, List.mem_cons, not_or]
      exact ⟨Ne.symm a.2, hq⟩
  · rintro ⟨p, hp⟩
    obtain ⟨x, hx⟩ := x
    obtain ⟨y, hy⟩ := y
    simp only at p hp
    induction p with
    | nil a => exact Reach.refl _ _
    | @cons a b c hab p ih =>
      simp only [Walk.support_cons, List.mem_cons, not_or] at hp
      have hb : b ≠ d := fun h => hp.2 (h ▸ p.start_mem)
      exact Reach.head (E := delVertex E d) (y := ⟨b, hb⟩) hab (ih hb hy hp.2)

/-- A walk either avoids `d`, or passes through it. -/
theorem reach_avoid_or (d : V) {x y : V} (p : Walk E x y) :
    d ∉ p.support ∨ (Reach E x d ∧ Reach E d y) := by
  by_cases hd : d ∈ p.support
  · right
    induction p with
    | nil a =>
      simp only [Walk.support_nil, List.mem_singleton] at hd
      subst hd
      exact ⟨Reach.refl _ _, Reach.refl _ _⟩
    | @cons a b c hab p ih =>
      simp only [Walk.support_cons, List.mem_cons] at hd
      by_cases hda : d = a
      · subst hda
        exact ⟨Reach.refl _ _, Reach.head hab ⟨p⟩⟩
      · have := hd.resolve_left hda
        obtain ⟨h1, h2⟩ := ih this
        exact ⟨Reach.head hab h1, h2⟩
  · exact Or.inl hd

theorem Reach.of_delVertex {d : V} {x y : {a : V // a ≠ d}} (h : Reach (delVertex E d) x y) :
    Reach E x.1 y.1 := by
  obtain ⟨p, _⟩ := reach_delVertex_iff.mp h
  exact ⟨p⟩

/-! ## Counting components

A map on vertices that respects the components and hits all of them compares the two counts. -/

section Count

variable {A B : Type*}

theorem quotient_card_lt_iff [Finite A] (r : Setoid A) (s : Setoid B) (f : A → B)
    (hr : ∀ a a', r a a' → s (f a) (f a')) (hs : ∀ b, ∃ a, s (f a) b) :
    Nat.card (Quotient s) < Nat.card (Quotient r) ↔ ∃ a a', s (f a) (f a') ∧ ¬ r a a' := by
  classical
  let F : Quotient r → Quotient s := Quotient.map' f hr
  have hF : Function.Surjective F := by
    intro q
    induction q using Quotient.inductionOn' with
    | h b =>
      obtain ⟨a, ha⟩ := hs b
      exact ⟨Quotient.mk'' a, Quotient.sound' ha⟩
  have hf : ∀ a, F (Quotient.mk'' a) = Quotient.mk'' (f a) := fun _ => rfl
  have : Finite (Quotient r) := Quotient.finite r
  constructor
  · intro hlt
    by_contra hno
    push Not at hno
    have hinj : Function.Injective F := by
      intro p q
      induction p using Quotient.inductionOn' with
      | h a =>
        induction q using Quotient.inductionOn' with
        | h a' =>
          intro h
          rw [hf, hf] at h
          exact Quotient.sound' (hno a a' (Quotient.exact' h))
    have := Nat.card_eq_of_bijective F ⟨hinj, hF⟩
    omega
  · rintro ⟨a, a', h1, h2⟩
    by_contra hle
    push Not at hle
    have hb := hF.bijective_of_nat_card_le hle
    have : (Quotient.mk'' a : Quotient r) = Quotient.mk'' a' :=
      hb.1 (by rw [hf, hf]; exact Quotient.sound' h1)
    exact h2 (Quotient.exact' this)

end Count

variable [Finite V]

/-- Removing an edge raises the count iff it separates two vertices of a component. -/
theorem sccCount_delEdge_lt_iff (u v : V) :
    sccCount E < sccCount (delEdge E u v) ↔ ∃ x y, Mutual E x y ∧ ¬ Mutual (delEdge E u v) x y := by
  have := quotient_card_lt_iff (sccSetoid (delEdge E u v)) (sccSetoid E) id
    (fun a a' h => Mutual.mono (delEdge_le E u v) h)
    (fun b => ⟨b, ⟨Reach.refl _ _, Reach.refl _ _⟩⟩)
  exact this

/-- Removing a vertex raises the count iff it separates two other vertices of a component. -/
theorem sccCount_delVertex_lt_iff (d : V) :
    sccCount E < sccCount (delVertex E d) ↔
      ∃ x y : {a : V // a ≠ d}, Mutual E x.1 y.1 ∧ ¬ Mutual (delVertex E d) x y := by
  constructor
  · intro hlt
    by_contra hno
    push Not at hno
    -- the map on classes is injective, so the count cannot grow
    let F : Quotient (sccSetoid (delVertex E d)) → Quotient (sccSetoid E) :=
      Quotient.map' (fun x => x.1) (fun _ _ h => ⟨h.1.of_delVertex, h.2.of_delVertex⟩)
    have hinj : Function.Injective F := by
      intro p q
      induction p using Quotient.inductionOn' with
      | h a =>
        induction q using Quotient.inductionOn' with
        | h a' =>
          intro h
          exact Quotient.sound' (hno a a' (Quotient.exact' h))
    have : Finite (Quotient (sccSetoid E)) := Quotient.finite _
    have := Nat.card_le_card_of_injective F hinj
    simp only [sccCount] at hlt
    omega
  · rintro ⟨x, y, hm, hn⟩
    -- some walk between `x` and `y` passes through `d`, so `x` is in the class of `d`
    have hxd : Mutual E x.1 d := by
      by_contra hxd
      apply hn
      have key : ∀ {a b : {t : V // t ≠ d}}, Mutual E x.1 a.1 → Reach E a.1 b.1 → Mutual E x.1 b.1 →
          Reach (delVertex E d) a b := by
        intro a b hxa hab hxb
        obtain ⟨p⟩ := hab
        rcases reach_avoid_or d p with h | ⟨h1, h2⟩
        · exact reach_delVertex_iff.mpr ⟨p, h⟩
        · exact absurd ⟨hxa.1.trans h1, h2.trans hxb.2⟩ hxd
      have hxx : Mutual E x.1 x.1 := ⟨Reach.refl _ _, Reach.refl _ _⟩
      exact ⟨key hxx hm.1 hm, key hm hm.2 hxx⟩
    have := quotient_card_lt_iff (sccSetoid (delVertex E d)) (sccSetoid E) (fun x => x.1)
      (fun a a' h => ⟨h.1.of_delVertex, h.2.of_delVertex⟩)
      (fun b => by
        by_cases hb : b = d
        · subst hb
          exact ⟨x, hxd⟩
        · exact ⟨⟨b, hb⟩, ⟨Reach.refl _ _, Reach.refl _ _⟩⟩)
    exact this.mpr ⟨x, y, hm, hn⟩

/-- Removing an edge between two components changes the count not at all. -/
theorem sccCount_delEdge_eq {u v : V} (huv : E u v) (hn : ¬ Mutual E u v) :
    sccCount (delEdge E u v) = sccCount E := by
  have hno : ¬ sccCount E < sccCount (delEdge E u v) := by
    rw [sccCount_delEdge_lt_iff]
    rintro ⟨x, y, hm, hne⟩
    apply hne
    have key : ∀ {a b : V}, Reach E a b → Reach E b a → Reach (delEdge E u v) a b := by
      intro a b hab hba
      rcases reach_delEdge_or' (u := u) (v := v) hab with h | ⟨h1, h2⟩
      · exact h
      · exact absurd ⟨Reach.edge huv, (h2.mono (delEdge_le E u v)).trans (hba.trans h1)⟩ hn
    exact ⟨key hm.1 hm.2, key hm.2 hm.1⟩
  let F : Quotient (sccSetoid (delEdge E u v)) → Quotient (sccSetoid E) :=
    Quotient.map' id (fun _ _ h => Mutual.mono (delEdge_le E u v) h)
  have hF : Function.Surjective F := by
    intro q
    induction q using Quotient.inductionOn' with
    | h b => exact ⟨Quotient.mk'' b, rfl⟩
  have : Finite (Quotient (sccSetoid (delEdge E u v))) := Quotient.finite _
  exact Nat.card_eq_of_bijective F (hF.bijective_of_nat_card_le (not_lt.mp hno))

/-- Removing a vertex alone in its component lowers the count by one. -/
theorem sccCount_delVertex_of_alone {d : V} (hd : ∀ x, Mutual E x d → x = d) :
    sccCount (delVertex E d) + 1 = sccCount E := by
  classical
  let F : Quotient (sccSetoid (delVertex E d)) → Quotient (sccSetoid E) :=
    Quotient.map' (fun x => x.1) (fun _ _ h => ⟨h.1.of_delVertex, h.2.of_delVertex⟩)
  let G : Option (Quotient (sccSetoid (delVertex E d))) → Quotient (sccSetoid E) := fun o =>
    match o with
    | none => Quotient.mk'' d
    | some q => F q
  have hne : ∀ x : {a : V // a ≠ d}, (Quotient.mk'' x.1 : Quotient (sccSetoid E)) ≠ Quotient.mk'' d := by
    intro x h
    exact x.2 (hd x.1 (Quotient.exact' h))
  have hG : Function.Bijective G := by
    constructor
    · rintro (_ | p) (_ | q) h
      · rfl
      · induction q using Quotient.inductionOn' with
        | h b => exact absurd h.symm (hne b)
      · induction p using Quotient.inductionOn' with
        | h b => exact absurd h (hne b)
      · induction p using Quotient.inductionOn' with
        | h a =>
          induction q using Quotient.inductionOn' with
          | h b =>
            have hm : Mutual E a.1 b.1 := Quotient.exact' h
            have key : ∀ {x y : {t : V // t ≠ d}}, Mutual E a.1 x.1 → Mutual E a.1 y.1 →
                Reach (delVertex E d) x y := by
              intro x y hx hy
              obtain ⟨p⟩ := hx.2.trans hy.1
              rcases reach_avoid_or d p with h1 | ⟨h1, h2⟩
              · exact reach_delVertex_iff.mpr ⟨p, h1⟩
              · exfalso
                exact x.2 (hd x.1 ⟨h1, h2.trans (hy.2.trans hx.1)⟩)
            have ha : Mutual E a.1 a.1 := ⟨Reach.refl _ _, Reach.refl _ _⟩
            exact congrArg some (Quotient.sound' ⟨key ha hm, key hm ha⟩)
    · intro q
      induction q using Quotient.inductionOn' with
      | h b =>
        by_cases hb : b = d
        · exact ⟨none, by rw [hb]⟩
        · exact ⟨some (Quotient.mk'' ⟨b, hb⟩), rfl⟩
  have : Finite (Quotient (sccSetoid (delVertex E d))) := Quotient.finite _
  have := Nat.card_eq_of_bijective G hG
  rw [Finite.card_option] at this
  exact this

omit [Finite V] in
/-- The count of a strongly connected graph. -/
theorem sccCount_eq_one [Nonempty V] (h : StrongConn E) : sccCount E = 1 := by
  rw [sccCount, Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun p q => ?_⟩, ⟨Quotient.mk'' (Classical.arbitrary V)⟩⟩
  induction p using Quotient.inductionOn' with
  | h a =>
    induction q using Quotient.inductionOn' with
    | h b => exact Quotient.sound' ⟨h a b, h b a⟩

end Dominators
