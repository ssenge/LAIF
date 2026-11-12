import PlanarMatching.ElimTree
import PlanarMatching.Decomp

/-!
# The facts on the tree of bags for the elimination

`notes/GENERAL.md`, Section 3, chains, homes and Fact 1, from the properties of `Decomp` alone. The arcs of the root
are the edges of `G`. The home of a vertex is the bag where its chain stops (`Decomp.homeBag`), and an edge is
assigned to the deeper home of its ends.

* `Decomp.fact1` (Fact 1): the homes of the ends of an edge are comparable, and the edge is an arc of the deeper one.
* `Decomp.comparable`: a bag holding `x` is comparable with every bag on the chain of `x`.
* `ElimData.FromDecomp.valid`: the tree hypotheses of `ElimData.Valid` hold for the chains, homes and edges of a
  rooted `Decomp` whose bags are numbered children first. With the steps of the bags this gives Lemma 2
  (`ElimData.FromDecomp.correct`).
-/

namespace PlanarMatching

open Relation

variable {V B : Type*} (D : Decomp V B)

theorem Decomp.verts_up {Y c : B} {x : V} (h : ReflTransGen D.child Y c) (hx : D.verts Y x) : D.verts c x := by
  induction h with
  | refl => exact hx
  | tail _ hc ih => exact D.child_verts hc ih

/-- An arc of `b` whose end `v` lies on the chain of `Y` is an arc of `Y`. -/
theorem Decomp.arc_down_right {Y b : B} {u v : V} (hv : D.OnChain Y v b) (a : D.arc b u v) : D.arc Y u v := by
  induction hv generalizing u with
  | here _ => exact a
  | down hc _ hs hrest ih =>
    obtain ⟨c', hc', ha⟩ := D.arc_child a ⟨_, hc⟩
    have e := D.uniq hc hc' (Decomp.OnChain.mem_top D hrest) (D.arc_mem ha).2 hs
    subst e
    exact ih ha

/-- An arc of `b` whose end `u` lies on the chain of `Y` is an arc of `Y`. -/
theorem Decomp.arc_down_left {Y b : B} {u v : V} (hu : D.OnChain Y u b) (a : D.arc b u v) : D.arc Y u v := by
  induction hu generalizing v with
  | here _ => exact a
  | down hc _ hs hrest ih =>
    obtain ⟨c', hc', ha⟩ := D.arc_child a ⟨_, hc⟩
    have e := D.uniq hc hc' (Decomp.OnChain.mem_top D hrest) (D.arc_mem ha).1 hs
    subst e
    exact ih ha

/-- The chain of a vertex stops at a bag where the vertex is on the separator. -/
theorem Decomp.exists_bottom {b : B} {x : V} (hx : D.verts b x) : ∃ Z, D.OnChain Z x b ∧ D.sep Z x := by
  induction b using D.wf.induction with
  | _ b ih =>
  by_cases hs : D.sep b x
  · exact ⟨b, .here hx, hs⟩
  · obtain ⟨c, hc, hxc⟩ := D.off_child hx hs
    obtain ⟨Z, hZ, hZs⟩ := ih c hc hxc
    exact ⟨Z, .down hc hx hs hZ, hZs⟩

theorem Decomp.OnChain.eq_of_sep {Z Z' : B} {x : V} (h : D.OnChain Z x Z') (hs : D.sep Z' x) : Z = Z' := by
  cases h with
  | here _ => rfl
  | down _ _ hs' _ => exact absurd hs hs'

/-- A bag on the chain of `x` lies above the bottom of the chain. -/
theorem Decomp.bottom_low {X Z b : B} {x : V} (hX : D.OnChain X x b) (hZ : D.OnChain Z x b) (hs : D.sep Z x) :
    ReflTransGen D.child Z X := by
  rcases D.chain_comparable hZ hX with h | h
  · exact Decomp.OnChain.toTop D h
  · rw [Decomp.OnChain.eq_of_sep D h hs]

theorem Decomp.bottom_unique {Z Z' b : B} {x : V} (hZ : D.OnChain Z x b) (hs : D.sep Z x)
    (hZ' : D.OnChain Z' x b) (hs' : D.sep Z' x) : Z = Z' := by
  rcases D.chain_comparable hZ hZ' with h | h
  · exact Decomp.OnChain.eq_of_sep D h hs'
  · exact (Decomp.OnChain.eq_of_sep D h hs).symm

theorem Decomp.antisymm {a b : B} (h : ReflTransGen D.child a b) (h' : ReflTransGen D.child b a) : a = b := by
  rcases reflTransGen_iff_eq_or_transGen.1 h with e | t
  · exact e.symm
  rcases reflTransGen_iff_eq_or_transGen.1 h' with e | t'
  · exact e
  exact absurd (t.trans t') (D.no_cycle a)

/-- A bag below `b` that holds `x` is comparable with every bag on the chain of `x` from `b`. -/
theorem Decomp.comparable {X b Y : B} {x : V} (h : D.OnChain X x b) (hY : ReflTransGen D.child Y b)
    (hx : D.verts Y x) : Y = X ∨ TransGen D.child Y X ∨ TransGen D.child X Y := by
  induction h generalizing Y with
  | here _ =>
    rcases reflTransGen_iff_eq_or_transGen.1 hY with e | t
    · exact Or.inl e.symm
    · exact Or.inr (Or.inl t)
  | down hc _ hs hrest ih =>
    rcases ReflTransGen.cases_tail hY with e | ⟨c', hY', hc'⟩
    · subst e
      exact Or.inr (Or.inr (TransGen.tail' (Decomp.OnChain.toTop D hrest) hc))
    · have e := D.uniq hc hc' (Decomp.OnChain.mem_top D hrest) (D.verts_up hY' hx) hs
      subst e
      exact ih hY' hx

/-- Fact 1, on any bag: the bottoms of the chains of the ends of an arc are comparable, and the arc lies in the
deeper one. -/
theorem Decomp.fact1_at (b : B) {u v : V} (a : D.arc b u v) :
    ∃ Zu Zv, D.OnChain Zu u b ∧ D.sep Zu u ∧ D.OnChain Zv v b ∧ D.sep Zv v ∧
      ((ReflTransGen D.child Zv Zu ∧ D.arc Zv u v) ∨ (ReflTransGen D.child Zu Zv ∧ D.arc Zu u v)) := by
  induction b using D.wf.induction with
  | _ b ih =>
  obtain ⟨hu, hv⟩ := D.arc_mem a
  by_cases hsu : D.sep b u
  · obtain ⟨Zv, hZv, hsv⟩ := D.exists_bottom hv
    exact ⟨b, Zv, .here hu, hsu, hZv, hsv, Or.inl ⟨Decomp.OnChain.toTop D hZv, D.arc_down_right hZv a⟩⟩
  by_cases hsv : D.sep b v
  · obtain ⟨Zu, hZu, hsu'⟩ := D.exists_bottom hu
    exact ⟨Zu, b, hZu, hsu', .here hv, hsv, Or.inr ⟨Decomp.OnChain.toTop D hZu, D.arc_down_left hZu a⟩⟩
  obtain ⟨c0, hc0, -⟩ := D.off_child hu hsu
  obtain ⟨c, hc, ha⟩ := D.arc_child a ⟨c0, hc0⟩
  obtain ⟨Zu, Zv, h1, h2, h3, h4, h5⟩ := ih c hc ha
  exact ⟨Zu, Zv, .down hc hu hsu h1, h2, .down hc hv hsv h3, h4, h5⟩

open Classical in
/-- The home of `x`: the bag where its chain from `r` stops. -/
noncomputable def Decomp.homeBag (r : B) (x : V) : B :=
  if h : ∃ Z, D.OnChain Z x r ∧ D.sep Z x then h.choose else r

theorem Decomp.homeBag_spec {r : B} {x : V} (hx : D.verts r x) :
    D.OnChain (D.homeBag r x) x r ∧ D.sep (D.homeBag r x) x := by
  have h := D.exists_bottom hx
  rw [Decomp.homeBag, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- Fact 1: the homes of the ends of an edge are comparable, and the edge is an arc of the deeper home. -/
theorem Decomp.fact1 {r : B} {u v : V} (a : D.arc r u v) :
    (ReflTransGen D.child (D.homeBag r v) (D.homeBag r u) ∧ D.arc (D.homeBag r v) u v) ∨
      (ReflTransGen D.child (D.homeBag r u) (D.homeBag r v) ∧ D.arc (D.homeBag r u) u v) := by
  obtain ⟨Zu, Zv, h1, h2, h3, h4, h5⟩ := D.fact1_at r a
  obtain ⟨hu, hv⟩ := D.arc_mem a
  have eu := D.bottom_unique h1 h2 (D.homeBag_spec hu).1 (D.homeBag_spec hu).2
  have ev := D.bottom_unique h3 h4 (D.homeBag_spec hv).1 (D.homeBag_spec hv).2
  rw [← eu, ← ev]
  exact h5

/-- A tree of bags with root `r`, all vertices in the root, one parent per bag, and the bags numbered children
first by `idx`, with inverse `bag`. -/
structure Decomp.Rooted (r : B) (T : ℕ) (bag : ℕ → B) (idx : B → ℕ) : Prop where
  below : ∀ b, ReflTransGen D.child b r
  root_verts : ∀ x, D.verts r x
  par_uniq : ∀ {c b b'}, D.child c b → D.child c b' → b = b'
  bag_idx : ∀ b, bag (idx b) = b
  idx_lt : ∀ b, idx b < T
  idx_bag : ∀ t < T, idx (bag t) = t
  order : ∀ {c b}, D.child c b → idx c < idx b

variable {K : Type*} [Field K] [Fintype V] [DecidableEq V]

open Classical in
/-- The chains, homes, boundaries and edges of `S` are those of `D`, and the edges of `S` are arcs of the root. -/
structure ElimData.FromDecomp (S : ElimData K V) (r : B) (bag : ℕ → B) (idx : B → ℕ) (fst snd : S.E → V) :
    Prop where
  ch : ∀ Y X, S.ch Y X ↔ Y < S.T ∧ X < S.T ∧ D.child (bag Y) (bag X)
  bd : ∀ X x, x ∈ S.bd X ↔ D.verts (bag X) x ∧ ¬ D.OnChain (bag X) x r
  chain : ∀ x X, S.chain x X ↔ X < S.T ∧ D.OnChain (bag X) x r
  home : ∀ x, S.home x = idx (D.homeBag r x)
  en : ∀ e, S.en e = {fst e, snd e}
  as : ∀ e, S.as e = if ReflTransGen D.child (D.homeBag r (snd e)) (D.homeBag r (fst e))
    then idx (D.homeBag r (snd e)) else idx (D.homeBag r (fst e))
  arc : ∀ e, D.arc r (fst e) (snd e)

namespace ElimData.FromDecomp

open Classical

variable {D} {S : ElimData K V} {r : B} {bag : ℕ → B} {idx : B → ℕ} {fst snd : S.E → V}
variable (hF : S.FromDecomp D r bag idx fst snd) (hR : D.Rooted r S.T bag idx)
include hF hR

theorem desc_of {a c : B} (h : TransGen D.child a c) : S.desc (idx a) (idx c) := by
  induction h with
  | single h =>
    exact TransGen.single ((hF.ch _ _).2 ⟨hR.idx_lt _, hR.idx_lt _, by rw [hR.bag_idx, hR.bag_idx]; exact h⟩)
  | tail _ h ih =>
    exact ih.tail ((hF.ch _ _).2 ⟨hR.idx_lt _, hR.idx_lt _, by rw [hR.bag_idx, hR.bag_idx]; exact h⟩)

/-- Below or equal in the tree gives below or equal in the numbering. -/
theorem le_of {a c : B} (h : ReflTransGen D.child a c) : idx a = idx c ∨ S.desc (idx a) (idx c) := by
  rcases reflTransGen_iff_eq_or_transGen.1 h with e | t
  · exact Or.inl (by rw [e])
  · exact Or.inr (hF.desc_of hR t)

theorem home_spec (x : V) : D.OnChain (D.homeBag r x) x r ∧ D.sep (D.homeBag r x) x :=
  D.homeBag_spec (hR.root_verts x)

theorem bag_home (x : V) : bag (S.home x) = D.homeBag r x := by rw [hF.home, hR.bag_idx]

/-- The bag of an edge, in the tree. -/
theorem bag_as (e : S.E) : bag (S.as e) =
    if ReflTransGen D.child (D.homeBag r (snd e)) (D.homeBag r (fst e))
    then D.homeBag r (snd e) else D.homeBag r (fst e) := by
  rw [hF.as]; split_ifs <;> exact hR.bag_idx _

theorem idx_bag_as (e : S.E) : idx (bag (S.as e)) = S.as e := by
  rw [hF.as]; split_ifs <;> rw [hR.bag_idx]

/-- The ends of an edge lie in the bag it is assigned to. -/
theorem en_verts (e : S.E) {x : V} (hx : x ∈ S.en e) : D.verts (bag (S.as e)) x := by
  have ha : D.arc (bag (S.as e)) (fst e) (snd e) := by
    rw [hF.bag_as hR]
    split_ifs with hc
    · rcases D.fact1 (hF.arc e) with ⟨-, h⟩ | ⟨h', h⟩
      · exact h
      · rw [D.antisymm hc h']; exact h
    · rcases D.fact1 (hF.arc e) with ⟨h', -⟩ | ⟨-, h⟩
      · exact absurd h' hc
      · exact h
  rw [hF.en, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact (D.arc_mem ha).1
  · exact (D.arc_mem ha).2

/-- Every index of `J_Y` lies in the bag `Y`. -/
theorem J_verts (hJ : ∀ X, S.J X = (S.kids X).biUnion S.ret ∪ (S.own X).biUnion S.en ∪
      S.W.filter (S.home · = X))
    (loc : ∀ X < S.T, LocalStep (S.M X) (S.I X) (S.J X) (S.P X) (S.Q X)) :
    ∀ Y, ∀ x ∈ S.J Y, Y < S.T ∧ D.verts (bag Y) x := by
  intro Y
  induction Y using Nat.strong_induction_on with
  | _ Y ih =>
  intro x hx
  rw [hJ] at hx
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, ElimData.kids, ElimData.own,
    Finset.mem_range, Finset.mem_univ, true_and] at hx
  rcases hx with (⟨Y', ⟨hY', hc⟩, hr⟩ | ⟨e, he, hen⟩) | ⟨-, hh⟩
  · obtain ⟨-, hYT, hc'⟩ := (hF.ch _ _).1 hc
    have hJ' : x ∈ S.J Y' := by
      rcases Finset.mem_union.1 hr with h | h
      · exact (loc Y' hY').sub (Finset.mem_sdiff.1 ((loc Y' hY').ret h)).1
      · exact (Finset.mem_inter.1 h).1
    have hlt : Y' < Y := by
      have := hR.order hc'; rwa [hR.idx_bag _ hY', hR.idx_bag _ hYT] at this
    exact ⟨hYT, D.child_verts hc' (ih Y' hlt x hJ').2⟩
  · subst he
    exact ⟨by rw [← hF.idx_bag_as hR]; exact hR.idx_lt _, hF.en_verts hR e hen⟩
  · subst hh
    refine ⟨by rw [hF.home]; exact hR.idx_lt _, ?_⟩
    rw [hF.bag_home hR]
    exact Decomp.OnChain.mem D (hF.home_spec hR x).1

omit hR in
theorem T_of_desc {a b : ℕ} (h : S.desc a b) : a < S.T ∧ b < S.T := by
  induction h with
  | single h => exact ⟨((hF.ch _ _).1 h).1, ((hF.ch _ _).1 h).2.1⟩
  | tail _ h ih => exact ⟨ih.1, ((hF.ch _ _).1 h).2.1⟩

/-- Below or equal in the numbering, for numbered bags. -/
theorem le_bag {a b : ℕ} (ha : a < S.T) (hb : b < S.T) (h : ReflTransGen D.child (bag a) (bag b)) :
    a = b ∨ S.desc a b := by
  have := hF.le_of hR h
  rwa [hR.idx_bag a ha, hR.idx_bag b hb] at this

theorem home_low {x : V} {X : ℕ} (hX : S.chain x X) : S.home x = X ∨ S.desc (S.home x) X := by
  obtain ⟨hXT, hc⟩ := (hF.chain x X).1 hX
  have hl := D.bottom_low hc (hF.home_spec hR x).1 (hF.home_spec hR x).2
  rw [← hF.bag_home hR] at hl
  exact hF.le_bag hR (by rw [hF.home]; exact hR.idx_lt _) hXT hl

/-- The tree hypotheses of `ElimData.Valid` hold. -/
theorem valid (alt : ∀ e, IsAlternating (S.Ae e))
    (Ae_supp : ∀ e i j, i ∉ S.en e ∨ j ∉ S.en e → S.Ae e i j = 0)
    (en_W : ∀ e, S.en e ⊆ S.W)
    (hM : ∀ X, S.M X = ∑ Y ∈ S.kids X, S.out Y + ∑ e ∈ S.own X, S.Ae e)
    (hJ : ∀ X, S.J X = (S.kids X).biUnion S.ret ∪ (S.own X).biUnion S.en ∪ S.W.filter (S.home · = X))
    (loc : ∀ X < S.T, LocalStep (S.M X) (S.I X) (S.J X) (S.P X) (S.Q X))
    (indep : ∀ X < S.T, LinearIndependent K
      fun q : S.Q X => fun j : ↥(S.J X \ S.I X) => elim (S.M X) (S.P X) q j) : S.Valid := by
  have hJv := hF.J_verts hR hJ loc
  refine ⟨fun {c b} h => ?_, fun h => ((hF.ch _ _).1 h).2.1, fun {c b b'} h h' => ?_, alt, Ae_supp, en_W,
    fun e => ?_, fun x _ => ?_, fun _ hX => hF.home_low hR hX, fun {x X Y} hX hY => ?_,
    fun {x X e} hx hX => ?_, fun {x X} hx => ?_, hM, hJ, loc, fun X hX hroot => ?_, indep⟩
  · obtain ⟨hc, hb, h⟩ := (hF.ch _ _).1 h
    have := hR.order h; rwa [hR.idx_bag _ hc, hR.idx_bag _ hb] at this
  · obtain ⟨-, hb, h⟩ := (hF.ch _ _).1 h
    obtain ⟨-, hb', h'⟩ := (hF.ch _ _).1 h'
    have e := hR.par_uniq h h'
    rw [← hR.idx_bag b hb, ← hR.idx_bag b' hb', e]
  · rw [← hF.idx_bag_as hR]; exact hR.idx_lt _
  · rw [hF.home]; exact hR.idx_lt _
  · obtain ⟨hXT, hc⟩ := (hF.chain x X).1 hX
    obtain ⟨hYT, hxY⟩ := hJv Y x hY
    rcases D.comparable hc (hR.below (bag Y)) hxY with e | t | t
    · exact Or.inl (by rw [← hR.idx_bag Y hYT, e, hR.idx_bag X hXT])
    · have := hF.desc_of hR t; rw [hR.idx_bag Y hYT, hR.idx_bag X hXT] at this; exact Or.inr (Or.inl this)
    · have := hF.desc_of hR t; rw [hR.idx_bag Y hYT, hR.idx_bag X hXT] at this; exact Or.inr (Or.inr this)
  · -- Fact 1: the bag of the edge lies on or below the chains of its ends
    obtain ⟨hXT, hc⟩ := (hF.chain x X).1 hX
    have hxle := D.bottom_low hc (hF.home_spec hR x).1 (hF.home_spec hR x).2
    have hasT : S.as e < S.T := by rw [← hF.idx_bag_as hR]; exact hR.idx_lt _
    refine hF.le_bag hR hasT hXT ?_
    rw [hF.bag_as hR]
    rw [hF.en, Finset.mem_insert, Finset.mem_singleton] at hx
    split_ifs with hcnd
    · rcases hx with rfl | rfl
      · exact hcnd.trans hxle
      · exact hxle
    · rcases hx with rfl | rfl
      · exact hxle
      · rcases D.fact1 (hF.arc e) with ⟨h', -⟩ | ⟨h', -⟩
        · exact absurd h' hcnd
        · exact h'.trans hxle
  · rw [ElimData.I, Finset.mem_sdiff] at hx
    obtain ⟨hXT, hxX⟩ := hJv X x hx.1
    refine (hF.chain x X).2 ⟨hXT, ?_⟩
    by_contra hn
    exact hx.2 ((hF.bd X x).2 ⟨hxX, hn⟩)
  · refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
    have hr : bag X = r := by
      rcases ReflTransGen.cases_head (hR.below (bag X)) with e | ⟨c, hc, -⟩
      · exact e
      · exact absurd ((hF.ch X (idx c)).2 ⟨hX, hR.idx_lt c, by rw [hR.bag_idx]; exact hc⟩) (hroot _)
    have := (hF.bd X x).1 hx
    rw [hr] at this
    exact this.2 (.here (hR.root_verts x))

/-- **Lemma 2** on a rooted tree of bags: every vertex of `W` is pivoted or dropped at exactly one bag, the rank of
`A` is the number of pivots `B`, and `A_{B,B}` is nonsingular. -/
theorem correct (alt : ∀ e, IsAlternating (S.Ae e))
    (Ae_supp : ∀ e i j, i ∉ S.en e ∨ j ∉ S.en e → S.Ae e i j = 0)
    (en_W : ∀ e, S.en e ⊆ S.W)
    (hM : ∀ X, S.M X = ∑ Y ∈ S.kids X, S.out Y + ∑ e ∈ S.own X, S.Ae e)
    (hJ : ∀ X, S.J X = (S.kids X).biUnion S.ret ∪ (S.own X).biUnion S.en ∪ S.W.filter (S.home · = X))
    (loc : ∀ X < S.T, LocalStep (S.M X) (S.I X) (S.J X) (S.P X) (S.Q X))
    (indep : ∀ X < S.T, LinearIndependent K
      fun q : S.Q X => fun j : ↥(S.J X \ S.I X) => elim (S.M X) (S.P X) q j) :
    (∀ x ∈ S.W, ∃! t, t < S.T ∧ x ∈ S.P t ∪ S.D t) ∧
      S.A.rank = (Run.pivots S.P S.T).card ∧ (principal S.A (Run.pivots S.P S.T)).det ≠ 0 :=
  (hF.valid hR alt Ae_supp en_W hM hJ loc indep).correct

end ElimData.FromDecomp

end PlanarMatching
