import Dominators.Lemma2

/-!
# Semidominators and immediate dominators

Everything here is proved from the abstract properties of a depth-first tree, `IsDfsTree`, and
`DfsTree.lean` shows that the executable search of `DFS.lean` has them. No classical result on dominators is
assumed.

* `sdom_formula`: the formula for the semidominator.
* `idom_iff_nca`: `idom(w)` is the nearest common ancestor of
  `parent(w)` and `sdom(w)` in the dominator tree.
-/

namespace Dominators

universe u

variable {V : Type u}

/-- The data of a search tree. -/
structure DfsTree (V : Type u) where
  /-- The preorder number. -/
  pre : V → ℕ
  /-- The tree parent. -/
  parent : V → Option V
  /-- The tree vertices in decreasing preorder. -/
  order : List V

/-- `a` is a tree ancestor of `x`, or `x` itself. -/
inductive Anc (parent : V → Option V) : V → V → Prop
  | refl (a : V) : Anc parent a a
  | step {a x y : V} (h : parent x = some y) (ha : Anc parent a y) : Anc parent a x

theorem Anc.trans {parent : V → Option V} {a b c : V} (h1 : Anc parent a b) (h2 : Anc parent b c) :
    Anc parent a c := by
  induction h2 with
  | refl => exact h1
  | step h _ ih => exact .step h ih

/-- A proper ancestor of `x` is an ancestor of its parent. -/
theorem Anc.of_ne {parent : V → Option V} {a x y : V} (h : Anc parent a x) (hne : a ≠ x)
    (hp : parent x = some y) : Anc parent a y := by
  cases h with
  | refl => exact absurd rfl hne
  | step h ha =>
    rw [hp] at h
    cases h
    exact ha

/-- A depth-first tree of the part of `E` reachable from `r`, numbered by preorder. Two properties make it
depth-first, and not any spanning tree: an edge to a larger number comes from an ancestor (`forward`), and the
descendants of a vertex form an interval of numbers (`interval`). -/
structure IsDfsTree (E : V → V → Prop) (r : V) (T : DfsTree V) : Prop where
  parent_root : T.parent r = none
  parent_spec : ∀ w, Reach E r w → w ≠ r →
    ∃ p, T.parent w = some p ∧ E p w ∧ Reach E r p ∧ T.pre p < T.pre w
  pre_inj : ∀ x y, Reach E r x → Reach E r y → T.pre x = T.pre y → x = y
  forward : ∀ v w, Reach E r v → E v w → T.pre v < T.pre w → Anc T.parent v w
  interval : ∀ a x y, Reach E r x → Reach E r y → Anc T.parent a x → T.pre a ≤ T.pre y → T.pre y ≤ T.pre x →
    Anc T.parent a y
  mem_order : ∀ x, x ∈ T.order ↔ Reach E r x
  sorted : T.order.Pairwise (fun a b => T.pre b < T.pre a)

variable {E : V → V → Prop} {r : V} {T : DfsTree V}

section Tree

variable (hT : IsDfsTree E r T)
include hT

theorem IsDfsTree.parent_eq {w p : V} (hw : Reach E r w) (hp : T.parent w = some p) :
    E p w ∧ Reach E r p ∧ T.pre p < T.pre w := by
  have hwr : w ≠ r := by
    rintro rfl
    rw [hT.parent_root] at hp
    cases hp
  obtain ⟨p', h1, h2⟩ := hT.parent_spec w hw hwr
  rw [hp] at h1
  cases h1
  exact h2

/-- Ancestors have smaller numbers, and are reachable, and reach their descendants. -/
theorem IsDfsTree.anc_le {a x : V} (hx : Reach E r x) (h : Anc T.parent a x) :
    T.pre a ≤ T.pre x ∧ (a ≠ x → T.pre a < T.pre x) ∧ Reach E r a := by
  induction h with
  | refl => exact ⟨le_rfl, fun h => absurd rfl h, hx⟩
  | @step x y hp _ ih =>
    obtain ⟨_, hy, hlt⟩ := hT.parent_eq hx hp
    obtain ⟨h1, _, h3⟩ := ih hy
    exact ⟨by omega, fun _ => by omega, h3⟩

/-- The tree path from an ancestor. -/
theorem IsDfsTree.anc_walk {a x : V} (hx : Reach E r x) (h : Anc T.parent a x) :
    ∃ p : Walk E a x, ∀ z ∈ p.support, Anc T.parent a z ∧ Anc T.parent z x := by
  induction h with
  | refl =>
    refine ⟨.nil a, ?_⟩
    simp only [Walk.support_nil, List.mem_singleton]
    rintro z rfl
    exact ⟨.refl _, .refl _⟩
  | @step x y hp ha ih =>
    obtain ⟨he, hy, _⟩ := hT.parent_eq hx hp
    obtain ⟨q, hq⟩ := ih hy
    refine ⟨q.snoc he, ?_⟩
    intro z hz
    rw [Walk.mem_support_snoc] at hz
    rcases hz with hz | rfl
    · exact ⟨(hq z hz).1, .step hp (hq z hz).2⟩
    · exact ⟨.step hp ha, .refl _⟩

/-- Every reachable vertex descends from the root. -/
theorem IsDfsTree.anc_root {x : V} (hx : Reach E r x) : Anc T.parent r x := by
  induction h : T.pre x using Nat.strong_induction_on generalizing x with
  | _ k ih =>
    by_cases hxr : x = r
    · rw [hxr]
      exact .refl _
    · obtain ⟨p, hp, _, hrp, hlt⟩ := hT.parent_spec x hx hxr
      exact .step hp (ih _ (h ▸ hlt) hrp rfl)

theorem IsDfsTree.root_le {x : V} (hx : Reach E r x) : T.pre r ≤ T.pre x :=
  (hT.anc_le hx (hT.anc_root hx)).1

/-- A dominator is a tree ancestor, since the tree path is a walk. -/
theorem IsDfsTree.anc_of_dominates {d x : V} (hx : Reach E r x) (h : Dominates E r d x) :
    Anc T.parent d x := by
  obtain ⟨p, hp⟩ := hT.anc_walk hx (hT.anc_root hx)
  exact (hp d (h p)).2

/-- If all vertices of a walk are at least `a`, and it starts at a descendant of `a`, it ends at one. -/
theorem IsDfsTree.anc_of_walk {a c b : V} (p : Walk E c b) (hc : Reach E r c) (hac : Anc T.parent a c)
    (hall : ∀ z ∈ p.support, T.pre a ≤ T.pre z) : Anc T.parent a b := by
  induction p with
  | nil _ => exact hac
  | @cons c y b hcy p ih =>
    have hy : Reach E r y := hc.tail hcy
    have hya : T.pre a ≤ T.pre y := hall y (by simp [p.start_mem])
    refine ih hy ?_ (fun z hz => hall z (by simp [hz]))
    by_cases hlt : T.pre c < T.pre y
    · exact hac.trans (hT.forward c y hc hcy hlt)
    · exact hT.interval a c y hc hy hac hya (by omega)

end Tree

/-! ## Semidominator paths -/

/-- `v` has a semidominator path to `w`: a path `v = v₀, …, v_k = w`, `k ≥ 1`, with `v_i` numbered above `w` for
`0 < i < k`. -/
inductive SemiPath (E : V → V → Prop) (pre : V → ℕ) (w : V) : V → Prop
  | edge {v : V} (h : E v w) : SemiPath E pre w v
  | step {v y : V} (h : E v y) (hy : pre w < pre y) (hp : SemiPath E pre w y) : SemiPath E pre w v

/-- `s` is the semidominator of `w`: the least-numbered reachable vertex with a semidominator path to `w`. -/
structure IsSdom (E : V → V → Prop) (r : V) (pre : V → ℕ) (s w : V) : Prop where
  reach : Reach E r s
  path : SemiPath E pre w s
  min : ∀ v, Reach E r v → SemiPath E pre w v → pre s ≤ pre v

/-- A nonempty set has an element of least value. -/
theorem exists_min_of {α : Type*} (P : α → Prop) (f : α → ℕ) (h : ∃ a, P a) :
    ∃ a, P a ∧ ∀ b, P b → f a ≤ f b := by
  classical
  have hk : ∃ k, ∃ a, P a ∧ f a = k := by
    obtain ⟨a, ha⟩ := h
    exact ⟨f a, a, ha, rfl⟩
  obtain ⟨a, ha, hfa⟩ := Nat.find_spec hk
  refine ⟨a, ha, fun b hb => ?_⟩
  rw [hfa]
  exact Nat.find_min' hk ⟨b, hb, rfl⟩

/-- A semidominator path as a walk. -/
theorem SemiPath.walk {pre : V → ℕ} {w v : V} (h : SemiPath E pre w v) :
    ∃ p : Walk E v w, ∀ x ∈ p.support, x = v ∨ x = w ∨ pre w < pre x := by
  induction h with
  | @edge v he =>
    refine ⟨.cons he (.nil w), ?_⟩
    intro x hx
    simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  | @step v y he hy _ ih =>
    obtain ⟨p, hp⟩ := ih
    refine ⟨.cons he p, ?_⟩
    intro x hx
    simp only [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · rcases hp x hx with rfl | h | h
      · exact Or.inr (Or.inr hy)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-- A semidominator path, without its last edge, as a walk with all vertices above `w`, from a start above `w`. -/
theorem SemiPath.walk_edge {pre : V → ℕ} {w y : V} (h : SemiPath E pre w y) (hy : pre w < pre y) :
    ∃ (v : V) (q : Walk E y v), E v w ∧ ∀ z ∈ q.support, pre w < pre z := by
  induction h with
  | @edge v he =>
    exact ⟨v, .nil v, he, by simpa using hy⟩
  | @step v y' he hy' _ ih =>
    obtain ⟨u, q, hu, hq⟩ := ih hy'
    refine ⟨u, .cons he q, hu, ?_⟩
    intro z hz
    simp only [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hy
    · exact hq z hz

/-- A walk whose vertices are all above `w`, followed by an edge to `w`, is a semidominator path. -/
theorem semiPath_of_walk {pre : V → ℕ} {w a v : V} (p : Walk E a v) (he : E v w)
    (hall : ∀ z ∈ p.support, pre w < pre z) : SemiPath E pre w a := by
  induction p with
  | nil _ => exact .edge he
  | @cons a y v hay p ih =>
    exact .step hay (hall y (by simp [p.start_mem])) (ih he (fun z hz => hall z (by simp [hz])))

/-- Concatenation: a semidominator path to `u`, with `u` above `w`, followed by one from `u` to `w`. -/
theorem SemiPath.trans {pre : V → ℕ} {w u a : V} (h : SemiPath E pre u a) (hu : pre w < pre u)
    (h' : SemiPath E pre w u) : SemiPath E pre w a := by
  induction h with
  | edge he => exact .step he hu h'
  | step he hy _ ih => exact .step he (by omega) ih

/-- Any walk from a vertex below `w` to `w` has a prefix to a vertex below `w` with a semidominator path to
`w`. -/
theorem exists_semi_prefix {pre : V → ℕ} (hinj : ∀ x y, Reach E r x → Reach E r y → pre x = pre y → x = y)
    {a w : V} (ha : Reach E r a) (q : Walk E a w) (hne : a ≠ w) :
    SemiPath E pre w a ∨ ∃ (x : V) (q1 : Walk E a x), q1.support ⊆ q.support ∧ pre x < pre w ∧ SemiPath E pre w x := by
  induction q with
  | nil _ => exact absurd rfl hne
  | @cons a y w hay q ih =>
    by_cases hyw : y = w
    · subst hyw
      exact Or.inl (.edge hay)
    · have hy : Reach E r y := ha.tail hay
      have hw : Reach E r w := hy.trans ⟨q⟩
      rcases ih hy hyw with h | ⟨x, q1, h1, h2, h3⟩
      · rcases Nat.lt_trichotomy (pre y) (pre w) with hlt | heq | hgt
        · right
          refine ⟨y, .cons hay (.nil y), ?_, hlt, h⟩
          intro t ht
          simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at ht ⊢
          rcases ht with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr q.start_mem
        · exact absurd (hinj y w hy hw heq) hyw
        · exact Or.inl (.step hay hgt h)
      · right
        refine ⟨x, .cons hay q1, ?_, h2, h3⟩
        intro t ht
        simp only [Walk.support_cons, List.mem_cons] at ht ⊢
        rcases ht with rfl | ht
        · exact Or.inl rfl
        · exact Or.inr (h1 ht)

/-- On a walk, take the first vertex of least number. The part before it gives a semidominator path to it. -/
theorem exists_min_on_walk {pre : V → ℕ} {y v : V} (q : Walk E y v) :
    ∃ u, u ∈ q.support ∧ (∀ x ∈ q.support, pre u ≤ pre x) ∧ (∃ q2 : Walk E u v, q2.support ⊆ q.support) ∧
      ∀ s, E s y → SemiPath E pre u s := by
  induction q with
  | nil v =>
    refine ⟨v, by simp, by simp, ⟨.nil v, by simp⟩, fun s hs => .edge hs⟩
  | @cons y y' v hyy' q ih =>
    obtain ⟨u, hu, hmin, ⟨q2, hq2⟩, hsemi⟩ := ih
    by_cases hle : pre y ≤ pre u
    · refine ⟨y, by simp, ?_, ⟨.cons hyy' q, by simp⟩, fun s hs => .edge hs⟩
      intro x hx
      simp only [Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact le_rfl
      · exact hle.trans (hmin x hx)
    · refine ⟨u, by simp [hu], ?_, ⟨q2, ?_⟩, fun s hs => .step hs (by omega) (hsemi y hyy')⟩
      · intro x hx
        simp only [Walk.support_cons, List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · exact hmin x hx
      · intro t ht
        simp only [Walk.support_cons, List.mem_cons]
        exact Or.inr (hq2 ht)

section Tree

variable (hT : IsDfsTree E r T)
include hT

/-- Every reachable non-root vertex has a semidominator. -/
theorem IsDfsTree.exists_sdom {w : V} (hw : Reach E r w) (hwr : w ≠ r) : ∃ s, IsSdom E r T.pre s w := by
  obtain ⟨p, _, he, hp, _⟩ := hT.parent_spec w hw hwr
  obtain ⟨s, ⟨h1, h2⟩, h3⟩ := exists_min_of (fun v => Reach E r v ∧ SemiPath E T.pre w v) T.pre
    ⟨p, hp, .edge he⟩
  exact ⟨s, h1, h2, fun v hv hv' => h3 v ⟨hv, hv'⟩⟩

theorem IsDfsTree.sdom_lt {s w : V} (hw : Reach E r w) (hwr : w ≠ r) (hs : IsSdom E r T.pre s w) :
    T.pre s < T.pre w := by
  obtain ⟨p, _, he, hp, hlt⟩ := hT.parent_spec w hw hwr
  exact (hs.min p hp (.edge he)).trans_lt hlt

omit hT in
/-- The semidominator value is unique. -/
theorem IsSdom.pre_eq {pre : V → ℕ} {s s' w : V} (h : IsSdom E r pre s w) (h' : IsSdom E r pre s' w) :
    pre s = pre s' :=
  le_antisymm (h.min s' h'.reach h'.path) (h'.min s h.reach h.path)

/-- A vertex below `w` with a semidominator path to `w` is a tree ancestor of `w`. -/
theorem IsDfsTree.anc_of_semi {x w : V} (hx : Reach E r x) (h : SemiPath E T.pre w x) (hlt : T.pre x < T.pre w) :
    Anc T.parent x w := by
  obtain ⟨p, hp⟩ := h.walk
  refine hT.anc_of_walk p hx (.refl _) ?_
  intro z hz
  rcases hp z hz with rfl | rfl | h
  · exact le_rfl
  · exact hlt.le
  · omega

/-- The key step for `idom_iff_nca`: the common dominators of `parent(w)` and `sdom(w)` are exactly the strict
dominators of `w`. -/
theorem IsDfsTree.sdom_key {w p s : V} (hw : Reach E r w) (hwr : w ≠ r) (hp : T.parent w = some p)
    (hs : IsSdom E r T.pre s w) (d : V) :
    (Dominates E r d p ∧ Dominates E r d s) ↔ (Dominates E r d w ∧ d ≠ w) := by
  obtain ⟨he, hrp, hplt⟩ := hT.parent_eq hw hp
  constructor
  · rintro ⟨hdp, hds⟩
    have hAdp := hT.anc_of_dominates hrp hdp
    have hAds := hT.anc_of_dominates hs.reach hds
    have hle1 := (hT.anc_le hrp hAdp).1
    have hdw : d ≠ w := by
      rintro rfl
      omega
    refine ⟨?_, hdw⟩
    intro P
    by_contra hdP
    have hrlt : T.pre r < T.pre w := by
      have := hT.parent_spec w hw hwr
      obtain ⟨_, _, _, h1, h2⟩ := this
      exact (hT.root_le h1).trans_lt h2
    -- the last vertex of `P` numbered below `w`
    obtain ⟨x, q1, hq1, hxlt, hxs⟩ : ∃ (x : V) (q1 : Walk E r x), q1.support ⊆ P.support ∧
        T.pre x < T.pre w ∧ SemiPath E T.pre w x := by
      rcases exists_semi_prefix hT.pre_inj (Reach.refl E r) P (Ne.symm hwr) with h | h
      · exact ⟨r, .nil r, by simp [P.start_mem], hrlt, h⟩
      · exact h
    have hrx : Reach E r x := ⟨q1⟩
    have hsx : T.pre s ≤ T.pre x := hs.min x hrx hxs
    have hxw : x ≠ w := by
      rintro rfl
      omega
    have hAxp : Anc T.parent x p := (hT.anc_of_semi hrx hxs hxlt).of_ne hxw hp
    obtain ⟨t, ht⟩ := hT.anc_walk hrp hAxp
    have hd := hdp (q1.append t)
    rw [Walk.mem_support_append] at hd
    rcases hd with hd | hd
    · exact hdP (hq1 hd)
    · have hAxd : Anc T.parent x d := (ht d hd).1
      have hrd : Reach E r d := (hT.anc_le hrp hAdp).2.2
      have hdx : x ≠ d := by
        rintro rfl
        exact hdP (hq1 q1.end_mem)
      have h1 := (hT.anc_le hrd hAxd).2.1 hdx
      have h2 := (hT.anc_le hs.reach hAds).1
      omega
  · rintro ⟨hdw, hne⟩
    constructor
    · intro Q
      have := hdw (Q.snoc he)
      rw [Walk.mem_support_snoc] at this
      exact this.resolve_right hne
    · intro Q
      obtain ⟨sp, hsp⟩ := hs.path.walk
      have := hdw (Q.append sp)
      rw [Walk.mem_support_append] at this
      rcases this with h | h
      · exact h
      · rcases hsp d h with rfl | h1 | h1
        · exact Q.end_mem
        · exact absurd h1 hne
        · have hA := hT.anc_of_dominates hw hdw
          have := (hT.anc_le hw hA).1
          omega

/-- **The semidominator formula.** `sdom(w)` is the least of the numbers of predecessors of `w` below `w`,
and of `sdom(u)` over `u` above `w` with some predecessor of `w` descending from `u`. -/
def FormulaSet (E : V → V → Prop) (r : V) (T : DfsTree V) (w : V) : Set ℕ :=
  {k | ∃ v, Reach E r v ∧ E v w ∧ T.pre v < T.pre w ∧ k = T.pre v} ∪
  {k | ∃ u v s', Reach E r v ∧ E v w ∧ T.pre w < T.pre u ∧ Anc T.parent u v ∧ IsSdom E r T.pre s' u ∧ k = T.pre s'}

theorem IsDfsTree.sdom_formula {s w : V} (hw : Reach E r w) (hwr : w ≠ r) (hs : IsSdom E r T.pre s w) :
    IsLeast (FormulaSet E r T w) (T.pre s) := by
  have hlower : ∀ k ∈ FormulaSet E r T w, T.pre s ≤ k := by
    rintro k (⟨v, hv, he, _, rfl⟩ | ⟨u, v, s', hv, he, hu, hA, hs', rfl⟩)
    · exact hs.min v hv (.edge he)
    · obtain ⟨t, ht⟩ := hT.anc_walk hv hA
      have hsemi : SemiPath E T.pre w u := semiPath_of_walk t he (fun z hz => by
        have hru : Reach E r z := by
          obtain ⟨Q⟩ := (hT.anc_le hv hA).2.2
          obtain ⟨t1, _⟩ := t.prefix hz
          exact ⟨Q.append t1⟩
        have := (hT.anc_le hru (ht z hz).1).1
        omega)
      exact hs.min s' hs'.reach (hs'.path.trans hu hsemi)
  refine ⟨?_, hlower⟩
  obtain he | ⟨he, hy, hp⟩ := hs.path
  · exact Or.inl ⟨s, hs.reach, he, hT.sdom_lt hw hwr hs, rfl⟩
  · obtain ⟨v, q, hvw, hq⟩ := hp.walk_edge hy
    obtain ⟨u, hu, hmin, ⟨q2, hq2⟩, hsemi⟩ := exists_min_on_walk (pre := T.pre) q
    have hry := hs.reach.tail he
    have hru : Reach E r u := by
      obtain ⟨t⟩ := hry
      obtain ⟨t1, _⟩ := q.prefix hu
      exact ⟨t.append t1⟩
    have hrv : Reach E r v := by
      obtain ⟨t⟩ := hry
      exact ⟨t.append q⟩
    have hA : Anc T.parent u v := hT.anc_of_walk q2 hru (.refl _) (fun z hz => hmin z (hq2 hz))
    have huw : T.pre w < T.pre u := hq u hu
    have hur : u ≠ r := by
      rintro rfl
      have := hT.root_le hw
      omega
    obtain ⟨s', hs'⟩ := hT.exists_sdom hru hur
    have hle : T.pre s' ≤ T.pre s := hs'.min s hs.reach (hsemi s he)
    have hge : T.pre s ≤ T.pre s' := hlower _ (Or.inr ⟨u, v, s', hrv, hvw, huw, hA, hs', rfl⟩)
    exact Or.inr ⟨u, v, s', hrv, hvw, huw, hA, hs', le_antisymm hge hle⟩

end Tree

/-! ## The immediate dominator from the semidominator -/

/-- `c` is the nearest common ancestor of `a` and `b` in the dominator tree: it dominates both, and every common
dominator of both dominates it. -/
def IsNCA (E : V → V → Prop) (r a b c : V) : Prop :=
  Dominates E r c a ∧ Dominates E r c b ∧ ∀ d, Dominates E r d a → Dominates E r d b → Dominates E r d c

theorem IsNCA.symm {a b c : V} (h : IsNCA E r a b c) : IsNCA E r b a c :=
  ⟨h.2.1, h.1, fun d h1 h2 => h.2.2 d h2 h1⟩

theorem IsNCA.self (a : V) : IsNCA E r a a a :=
  ⟨Dominates.refl r a, Dominates.refl r a, fun _ h _ => h⟩

/-- **Nearest common ancestor form.** `idom(w)` is the nearest common ancestor of `parent(w)` and
`sdom(w)` in the dominator tree. -/
theorem IsDfsTree.idom_iff_nca (hT : IsDfsTree E r T) {w p s : V} (hw : Reach E r w) (hwr : w ≠ r)
    (hp : T.parent w = some p) (hs : IsSdom E r T.pre s w) (u : V) :
    IsIdom E r u w ↔ IsNCA E r p s u := by
  have key := hT.sdom_key hw hwr hp hs
  constructor
  · rintro ⟨_, hne, hdom, hmin⟩
    obtain ⟨h1, h2⟩ := (key u).mpr ⟨hdom, hne⟩
    refine ⟨h1, h2, fun d hd1 hd2 => ?_⟩
    obtain ⟨hdw, hdne⟩ := (key d).mp ⟨hd1, hd2⟩
    exact hmin d hdne hdw
  · rintro ⟨h1, h2, hmin⟩
    obtain ⟨hdw, hne⟩ := (key u).mp ⟨h1, h2⟩
    refine ⟨hw, hne, hdw, fun d hdne hd => ?_⟩
    obtain ⟨hd1, hd2⟩ := (key d).mpr ⟨hd, hdne⟩
    exact hmin d hd1 hd2

/-- A vertex numbered above `a` does not dominate `a`. -/
theorem IsDfsTree.not_dominates_of_lt (hT : IsDfsTree E r T) {a b : V} (ha : Reach E r a)
    (hlt : T.pre a < T.pre b) : ¬ Dominates E r b a := by
  intro h
  have := (hT.anc_le ha (hT.anc_of_dominates ha h)).1
  omega

/-- Replacing the larger of two vertices by its immediate dominator keeps the nearest common ancestor. This is
the step of the climb that computes it. -/
theorem IsNCA.of_idom (hT : IsDfsTree E r T) {a b b' c : V} (ha : Reach E r a) (hlt : T.pre a < T.pre b)
    (hb : IsIdom E r b' b) (h : IsNCA E r a b' c) : IsNCA E r a b c := by
  refine ⟨h.1, h.2.1.trans hb.2.2.1, fun d hd1 hd2 => ?_⟩
  have hne : d ≠ b := by
    rintro rfl
    exact hT.not_dominates_of_lt ha hlt hd1
  exact h.2.2 d hd1 (hb.2.2.2 d hne hd2)

end Dominators
