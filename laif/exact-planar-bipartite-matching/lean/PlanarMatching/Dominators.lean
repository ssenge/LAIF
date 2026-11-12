import PlanarMatching.GeneralSearch

/-!
# Dominators along one path

`notes/DOMINATORS.md`, Sections 3 to 5, on any digraph. `PathStep` is the setting of Section 3, with the virtual root as
`p 0` and the flow graph as `D[K]`. `lemma1a` and `lemma1b` are Lemma 1, and `dom_path` and `dom_off` are its last claim. `closed_end` and
`closed_le` are Lemma 2(a), through `closedJ_iff`, and `laminar` is Lemma 2(b). `class_dom` and `split_out` are the core of
Lemma 4(b): `class_dom` holds for any set with the property that `split_out` proves of a class, and it is not tied to `E_K` or to
the split of a problem. `closed_parts`, `closed_mem` and `candidate` are Lemma 5. `ring` is Lemma 6, `delta_ring` is the rule for `δ`,
and `readoff` is the case of Lemma 7 with `a` and `b` in one segment.

Not here: Lemma 3, Lemma 4(a), the cases `a = 0` and `a = b` and the higher segments of Lemma 7, the marks and their single sender,
the claim that aggregates and sweeps compute these values, and all round bounds.
-/

namespace PlanarMatching.Dominators

open Relation PlanarMatching.DagSearch PlanarMatching.GeneralSearch

variable {V : Type*}

/-- The setting of Section 3: the flow graph `D[K]`, with `p 0` the root, and the simple path `p 0, ..., p k`. -/
structure PathStep (V : Type*) where
  D : V → V → Prop
  K : Set V
  k : ℕ
  p : ℕ → V
  path : IsPath D K k p

namespace PathStep

variable (S : PathStep V)

/-- The vertex lies on the path. -/
def OnPath (y : V) : Prop := ∃ i ≤ S.k, S.p i = y

/-- `O`: the vertices off the path. -/
def O : Set V := {y | y ∈ S.K ∧ ¬ S.OnPath y}

/-- `w` is in `R_j`: it is reached from the root without `p j`. -/
def Rj (j : ℕ) (w : V) : Prop := Reach S.D (S.K \ {S.p j}) (S.p 0) w

/-- The index `i` feeds `y`: a path from `p i` to `y` with all vertices after `p i` off the path. -/
def Feeds (i : ℕ) (y : V) : Prop := i ≤ S.k ∧ ∃ u, S.D (S.p i) u ∧ u ∈ S.O ∧ Reach S.D S.O u y

/-- The index `i` jumps to `t`. -/
def Jumps (i t : ℕ) : Prop :=
  i ≤ S.k ∧ (S.D (S.p i) (S.p t) ∨ ∃ u, u ∈ S.O ∧ S.Feeds i u ∧ S.D u (S.p t))

/-- `m` is `m(j)`: the first index after `j` reached without `p j`, or `k + 1`. -/
structure IsEnd (j m : ℕ) : Prop where
  lt : j < m
  le : m ≤ S.k + 1
  none : ∀ t, j < t → t < m → ¬ S.Rj j (S.p t)
  some : m ≤ S.k → S.Rj j (S.p m)

/-- Every jump into `t` with `j < t < x` starts in `j, ..., x - 1`. -/
def ClosedJ (j x : ℕ) : Prop := ∀ t i, j < t → t < x → S.Jumps i t → j ≤ i ∧ i < x

variable {S}

theorem O_sub {y : V} (j : ℕ) (hj : j ≤ S.k) (hy : y ∈ S.O) : y ∈ S.K \ {S.p j} :=
  ⟨hy.1, fun h => hy.2 ⟨j, hj, h.symm⟩⟩

theorem p_mem {i j : ℕ} (hi : i ≤ S.k) (hj : j ≤ S.k) (hij : i ≠ j) : S.p i ∈ S.K \ {S.p j} :=
  ⟨S.path.mem i hi, fun h => hij (S.path.inj i hi j hj h)⟩

/-- The path from `a` to `b` avoids `p j` if `j` is outside `a, ..., b`. -/
theorem path_avoid {j a b : ℕ} (hj : j ≤ S.k) (hab : a ≤ b) (hb : b ≤ S.k) (h : j < a ∨ b < j) :
    Reach S.D (S.K \ {S.p j}) (S.p a) (S.p b) := by
  induction b, hab using Nat.le_induction with
  | base => exact ReflTransGen.refl
  | succ b hab ih =>
    refine (ih (by omega) (by omega)).tail
      ⟨S.path.arc b (by omega), p_mem (by omega) hj (by omega), p_mem hb hj (by omega)⟩

/-- **Lemma 1(a).** -/
theorem lemma1a {j m i : ℕ} (hm : S.IsEnd j m) (hj : j ≤ S.k) (hi : i ≤ S.k) (hij : i ≠ j) :
    S.Rj j (S.p i) ↔ i < j ∨ m ≤ i := by
  constructor
  · intro h
    by_contra hc
    exact hm.none i (by omega) (by omega) h
  · rintro (h | h)
    · exact path_avoid hj (Nat.zero_le i) hi (Or.inr h)
    · exact (hm.some (by omega)).trans (path_avoid hj h hi (Or.inl (by have := hm.lt; omega)))

/-- A vertex off the path reached without `p j` is fed from a vertex of the path reached without `p j`. -/
theorem fed_of_Rj {j : ℕ} {w : V} (h : S.Rj j w) (hw : w ∈ S.O) :
    ∃ i, S.Feeds i w ∧ i ≠ j ∧ S.Rj j (S.p i) := by
  induction h with
  | refl => exact absurd ⟨0, Nat.zero_le _, rfl⟩ hw.2
  | @tail v w hv hvw ih =>
    by_cases hvO : v ∈ S.O
    · obtain ⟨i, ⟨hi, u, hu, huO, hr⟩, hij, hRi⟩ := ih hvO
      exact ⟨i, ⟨hi, u, hu, huO, hr.tail ⟨hvw.1, hvO, hw⟩⟩, hij, hRi⟩
    · have hvK := hvw.2.1.1
      have hon : S.OnPath v := by
        by_contra hc
        exact hvO ⟨hvK, hc⟩
      obtain ⟨i, hi, rfl⟩ := hon
      refine ⟨i, ⟨hi, w, hvw.1, hw, ReflTransGen.refl⟩, ?_, hv⟩
      rintro rfl
      exact hvw.2.1.2 rfl

theorem Rj_of_feeds {j i : ℕ} {y : V} (hj : j ≤ S.k) (hij : i ≠ j) (hRi : S.Rj j (S.p i)) (hf : S.Feeds i y) :
    S.Rj j y := by
  obtain ⟨hi, u, hu, huO, hr⟩ := hf
  exact (hRi.tail ⟨hu, p_mem hi hj hij, O_sub j hj huO⟩).trans
    (reach_mono (fun _ hx => O_sub j hj hx) hr)

/-- **Lemma 1(b)**, with any index in place of the extreme ones. -/
theorem lemma1b {j m : ℕ} {y : V} (hm : S.IsEnd j m) (hj : j ≤ S.k) (hy : y ∈ S.O) :
    S.Rj j y ↔ ∃ i, S.Feeds i y ∧ (i < j ∨ m ≤ i) := by
  constructor
  · intro h
    obtain ⟨i, hf, hij, hRi⟩ := fed_of_Rj h hy
    exact ⟨i, hf, (lemma1a hm hj hf.1 hij).1 hRi⟩
  · rintro ⟨i, hf, h⟩
    have hij : i ≠ j := by
      have := hm.lt
      omega
    exact Rj_of_feeds hj hij ((lemma1a hm hj hf.1 hij).2 h) hf

/-- **Lemma 1, last claim**: `p j` dominates `p i` if and only if `j < i < m(j)`. -/
theorem dom_path {j m i : ℕ} (hm : S.IsEnd j m) (hj : j ≤ S.k) (hi : i ≤ S.k) (hij : i ≠ j) :
    ¬ S.Rj j (S.p i) ↔ j < i ∧ i < m := by
  rw [lemma1a hm hj hi hij]
  omega

/-- **Lemma 1, last claim**: `p j` dominates `y` off the path if and only if `j ≤ a(y)` and `b(y) < m(j)`. -/
theorem dom_off {j m a b : ℕ} {y : V} (hm : S.IsEnd j m) (hj : j ≤ S.k) (hy : y ∈ S.O)
    (ha : IsLeast {i | S.Feeds i y} a) (hb : IsGreatest {i | S.Feeds i y} b) :
    ¬ S.Rj j y ↔ j ≤ a ∧ b < m := by
  rw [lemma1b hm hj hy]
  constructor
  · intro h
    constructor
    · by_contra hc
      exact h ⟨a, ha.1, Or.inl (by omega)⟩
    · by_contra hc
      exact h ⟨b, hb.1, Or.inr (by omega)⟩
  · rintro ⟨h₁, h₂⟩ ⟨i, hf, h⟩
    have h₃ := ha.2 hf
    have h₄ := hb.2 hf
    omega

/-- **Lemma 2(a)**, first half: `(j, m(j))` is closed. -/
theorem closedJ_end {j m : ℕ} (hm : S.IsEnd j m) (hj : j ≤ S.k) : S.ClosedJ j m := by
  intro t i hjt htm hjump
  by_contra hc
  have hle := hm.le
  have htk : t ≤ S.k := by omega
  have hij : i ≠ j ∧ (i < j ∨ m ≤ i) := by omega
  obtain ⟨hik, h⟩ := hjump
  have hRi := (lemma1a hm hj hik hij.1).2 hij.2
  refine hm.none t hjt htm ?_
  rcases h with h | ⟨u, huO, hf, hut⟩
  · exact hRi.tail ⟨h, p_mem hik hj hij.1, p_mem htk hj (by omega)⟩
  · have hu : S.Rj j u := Rj_of_feeds hj hij.1 hRi hf
    exact hu.tail ⟨hut, O_sub j hj huO, p_mem htk hj (by omega)⟩

/-- No path from the root without `p j` enters a closed interval. -/
theorem not_enter {j x : ℕ} (hj : j ≤ S.k) (hx : x ≤ S.k + 1) (hc : S.ClosedJ j x) {w : V} (h : S.Rj j w) :
    (∀ t, j < t → t < x → w ≠ S.p t) ∧ (w ∈ S.O → ∃ i, S.Feeds i w ∧ (i < j ∨ x ≤ i)) := by
  induction h with
  | refl =>
    refine ⟨fun t hjt htx h0 => ?_, fun hw => absurd ⟨0, Nat.zero_le _, rfl⟩ hw.2⟩
    have := S.path.inj 0 (Nat.zero_le _) t (by omega) h0
    omega
  | @tail v w hv hvw ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have hvK := hvw.2.1.1
    have hvj : v ≠ S.p j := hvw.2.1.2
    -- the vertex `v` as a source
    have hsrc : (v ∈ S.O ∧ ∃ i, S.Feeds i v ∧ (i < j ∨ x ≤ i)) ∨
        ∃ i, i ≤ S.k ∧ v = S.p i ∧ (i < j ∨ x ≤ i) := by
      by_cases hvO : v ∈ S.O
      · exact Or.inl ⟨hvO, ih₂ hvO⟩
      · have hon : S.OnPath v := by
          by_contra hn
          exact hvO ⟨hvK, hn⟩
        obtain ⟨i, hi, rfl⟩ := hon
        refine Or.inr ⟨i, hi, rfl, ?_⟩
        by_contra hn
        have hij : i ≠ j := by
          rintro rfl
          exact hvj rfl
        exact ih₁ i (by omega) (by omega) rfl
    constructor
    · rintro t hjt htx rfl
      have htk : t ≤ S.k := by omega
      rcases hsrc with ⟨hvO, i, hf, hi⟩ | ⟨i, hik, rfl, hi⟩
      · have := hc t i hjt htx ⟨hf.1, Or.inr ⟨v, hvO, hf, hvw.1⟩⟩
        omega
      · have := hc t i hjt htx ⟨hik, Or.inl hvw.1⟩
        omega
    · intro hw
      rcases hsrc with ⟨hvO, i, ⟨hi, u, hu, huO, hr⟩, hii⟩ | ⟨i, hik, rfl, hi⟩
      · exact ⟨i, ⟨hi, u, hu, huO, hr.tail ⟨hvw.1, hvO, hw⟩⟩, hii⟩
      · exact ⟨i, ⟨hik, w, hvw.1, hw, ReflTransGen.refl⟩, hi⟩

/-- **Lemma 2(a)**, second half: `m(j)` is the largest closed end. -/
theorem closedJ_le {j m x : ℕ} (hm : S.IsEnd j m) (hj : j ≤ S.k) (hx : x ≤ S.k + 1) (hc : S.ClosedJ j x) : x ≤ m := by
  by_contra hlt
  have hmk : m ≤ S.k := by omega
  exact (not_enter hj hx hc (hm.some hmk)).1 m hm.lt (by omega) rfl

/-- A path without `p j` either avoids `p j'`, or it has reached `p j'`. -/
theorem avoid_or_pass {j j' : ℕ} {w : V} (h : S.Rj j w) : S.Rj j' w ∨ S.Rj j (S.p j') := by
  by_cases h0 : S.p 0 = S.p j'
  · exact Or.inr (h0 ▸ ReflTransGen.refl)
  induction h with
  | refl => exact Or.inl ReflTransGen.refl
  | @tail v w hv hvw ih =>
    rcases ih with ih | ih
    · by_cases hw : w = S.p j'
      · exact Or.inr (hw ▸ hv.tail hvw)
      · have hvj : v ∈ S.K \ {S.p j'} := Reach.mem ih ⟨S.path.mem 0 (Nat.zero_le _), h0⟩
        exact Or.inl (ih.tail ⟨hvw.1, hvj, ⟨hvw.2.2.1, hw⟩⟩)
    · exact Or.inr ih

/-- **Lemma 2(b).** -/
theorem laminar {j j' m m' : ℕ} (hm : S.IsEnd j m) (hm' : S.IsEnd j' m') (hjj : j < j') (hj'm : j' < m) : m' ≤ m := by
  by_contra hlt
  have h1 := hm'.le
  have hmk : m ≤ S.k := by omega
  rcases avoid_or_pass (j' := j') (hm.some hmk) with h | h
  · exact hm'.none m hj'm (by omega) h
  · exact hm.none j' hjj hj'm h

/-- Extreme jumps of each position, with `A t` large and `B t = 0` if there is no jump. -/
structure Extremes (S : PathStep V) (A B : ℕ → ℕ) : Prop where
  bounds : ∀ t i, S.Jumps i t → A t ≤ i ∧ i ≤ B t
  least : ∀ t, (∃ i, S.Jumps i t) → S.Jumps (A t) t
  greatest : ∀ t, (∃ i, S.Jumps i t) → S.Jumps (B t) t
  none : ∀ t, (¬ ∃ i, S.Jumps i t) → S.k < A t ∧ B t = 0

end PathStep

/-- `(j, x)` is closed. -/
def Closed (A B : ℕ → ℕ) (j x : ℕ) : Prop := ∀ t, j < t → t < x → j ≤ A t ∧ B t < x

namespace PathStep

variable {S : PathStep V}

theorem closedJ_iff {A B : ℕ → ℕ} (hE : Extremes S A B) {j x : ℕ} (hj : j ≤ S.k) :
    S.ClosedJ j x ↔ Closed A B j x := by
  constructor
  · intro h t hjt htx
    by_cases hex : ∃ i, S.Jumps i t
    · exact ⟨(h t _ hjt htx (hE.least t hex)).1, (h t _ hjt htx (hE.greatest t hex)).2⟩
    · have := hE.none t hex
      omega
  · intro h t i hjt htx hi
    have h₁ := h t hjt htx
    have h₂ := hE.bounds t i hi
    omega

/-- **Lemma 2(a).** -/
theorem closed_end {A B : ℕ → ℕ} (hE : Extremes S A B) {j m : ℕ} (hm : S.IsEnd j m) (hj : j ≤ S.k) : Closed A B j m :=
  (closedJ_iff hE hj).1 (closedJ_end hm hj)

/-- **Lemma 2(a).** -/
theorem closed_le {A B : ℕ → ℕ} (hE : Extremes S A B) {j m x : ℕ} (hm : S.IsEnd j m) (hj : j ≤ S.k)
    (hx : x ≤ S.k + 1) (hc : Closed A B j x) : x ≤ m :=
  closedJ_le hm hj hx ((closedJ_iff hE hj).2 hc)

end PathStep

/-! ## Classes -/

/-- **Lemma 4(b)**, for any set `K₀` such that all else is reached from the root with no vertex of `K₀`. A vertex is an
entry of `K₀` if it has an arc from outside, and the root counts as outside. -/
theorem class_dom {D : V → V → Prop} {F K₀ : Set V} {ρ w y : V} (hρK : ρ ∉ K₀) (hK : K₀ ⊆ F)
    (hout : ∀ v ∈ F \ K₀, Reach D (F \ K₀) ρ v) (hw : w ∈ K₀) (hy : y ∈ K₀) :
    Reach D (F \ {w}) ρ y ↔ ∃ e u, e ∈ K₀ ∧ e ≠ w ∧ u ∈ F \ K₀ ∧ D u e ∧ Reach D (K₀ \ {w}) e y := by
  constructor
  · intro h
    have key : ∀ z, Reach D (F \ {w}) ρ z → z ∈ K₀ → ∃ e u, e ∈ K₀ ∧ e ≠ w ∧ u ∈ F \ K₀ ∧ D u e ∧ Reach D (K₀ \ {w}) e z := by
      intro z hz
      induction hz with
      | refl => exact fun hc => absurd hc hρK
      | @tail v z _ hvz ih =>
        intro hzK
        have hzw : z ≠ w := hvz.2.2.2
        by_cases hvK : v ∈ K₀
        · obtain ⟨e, u, he, hew, hu, hue, hr⟩ := ih hvK
          exact ⟨e, u, he, hew, hu, hue, hr.tail ⟨hvz.1, ⟨hvK, hvz.2.1.2⟩, ⟨hzK, hzw⟩⟩⟩
        · exact ⟨z, v, hzK, hzw, ⟨hvz.2.1.1, hvK⟩, hvz.1, ReflTransGen.refl⟩
    exact key y h hy
  · rintro ⟨e, u, he, hew, hu, hue, hr⟩
    have h₁ : Reach D (F \ {w}) ρ u :=
      reach_mono (R := F \ K₀) (T := F \ {w}) (fun x hx => ⟨hx.1, fun hxw => hx.2 (by rw [hxw]; exact hw)⟩) (hout u hu)
    have huw : u ∈ F \ {w} := ⟨hu.1, fun hc => hu.2 (by rw [hc]; exact hw)⟩
    have h₂ : Reach D (K₀ \ {w}) e y := hr
    exact (h₁.tail ⟨hue, huw, ⟨hK he, hew⟩⟩).trans (reach_mono (R := K₀ \ {w}) (T := F \ {w}) (fun x hx => ⟨hK hx.1, hx.2⟩) h₂)

section SplitOut

variable (S : Split V)

/-- **Lemma 4**, the first remark of its proof: outside a class, all is reached from the root with no vertex of the class. -/
theorem split_out {z v : V} (hv : v ∈ S.K) (hvz : v ∉ S.cls z) : Reach S.D (S.K \ S.cls z) (S.v 0) v := by
  have hpath : ∀ i ≤ S.k, Reach S.D (S.K \ S.cls z) (S.v 0) (S.v i) := by
    intro i hi
    induction i with
    | zero => exact ReflTransGen.refl
    | succ i ih =>
      have hmem : ∀ l ≤ S.k, S.v l ∈ S.K \ S.cls z := fun l hl =>
        ⟨S.path.mem l hl, fun hc => hc.1.2 ⟨l, hl, rfl⟩⟩
      exact (ih (by omega)).tail ⟨S.path.arc i (by omega), hmem i (by omega), hmem (i + 1) hi⟩
  by_cases hon : S.OnPath v
  · obtain ⟨i, hi, rfl⟩ := hon
    exact hpath i hi
  · have hR : v ∈ S.R := ⟨hv, hon⟩
    obtain ⟨hl, hm⟩ := Split.isClassHead_lead hR
    have hne : ∀ y ∈ S.cls (S.lead v), y ∉ S.cls z := by
      intro y hy hyz
      apply hvz
      exact ⟨hR, by rw [hm.2, ← hy.2, hyz.2]⟩
    have hsub : S.cls (S.lead v) ⊆ S.K \ S.cls z := fun y hy => ⟨hy.1.1, hne y hy⟩
    have h₁ := Split.lemma1a_reach hl.1 hm
    have h₂ := hpath _ (Split.depth_le (S.lead v))
    have hp : S.D (S.p (S.lead v)) (S.lead v) := Split.p_arc hl.1
    have hmemp : S.v (S.depth (S.lead v)) ∈ S.K \ S.cls z :=
      ⟨S.path.mem _ (Split.depth_le _), fun hc => hc.1.2 ⟨_, Split.depth_le _, rfl⟩⟩
    exact (h₂.tail ⟨hp, hmemp, hsub hl.2⟩).trans (reach_mono hsub h₁)

end SplitOut

/-! ## One segment -/

section Segment

variable {A B : ℕ → ℕ}

/-- The four conditions in the proof of Lemma 5. -/
theorem closed_parts {j c x : ℕ} :
    Closed A B j x ↔ (∀ t, j < t → t ≤ c → t < x → j ≤ A t) ∧ (∀ t, j < t → t ≤ c → t < x → B t < x) ∧
      (∀ t, j < t → c < t → t < x → j ≤ A t) ∧ (∀ t, j < t → c < t → t < x → B t < x) := by
  constructor
  · intro h
    exact ⟨fun t h₁ _ h₂ => (h t h₁ h₂).1, fun t h₁ _ h₂ => (h t h₁ h₂).2, fun t h₁ _ h₂ => (h t h₁ h₂).1,
      fun t h₁ _ h₂ => (h t h₁ h₂).2⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩ t hjt htx
    by_cases htc : t ≤ c
    · exact ⟨h₁ t hjt htc htx, h₂ t hjt htc htx⟩
    · exact ⟨h₃ t hjt (by omega) htx, h₄ t hjt (by omega) htx⟩

/-- `x` is good: the jumps into `c + 1, ..., x - 1` all start before `x`. -/
def Good (B : ℕ → ℕ) (c x : ℕ) : Prop := ∀ t, c < t → t < x → B t < x

/-- `X` is `X(j)`: the first `t` of `Y` with `A t < j`, or `r + 1`. -/
structure IsFirst (A : ℕ → ℕ) (j c r X : ℕ) : Prop where
  lo : c < X
  hi : X ≤ r + 1
  before : ∀ t, c < t → t < X → j ≤ A t
  at_ : X ≤ r → A X < j

/-- **Lemma 5.** A closed end in `Y` is good and at most `X(j)`. -/
theorem closed_mem {j c r X x : ℕ} (hX : IsFirst A j c r X) (hjc : j ≤ c) (hxr : x ≤ r + 1) (h : Closed A B j x) :
    x ≤ X ∧ Good B c x := by
  constructor
  · by_contra hlt
    have := hX.at_ (by omega)
    have := (h X (by have := hX.lo; omega) (by omega)).1
    omega
  · intro t hct htx
    exact (h t (by omega) htx).2

/-- **Lemma 5.** With `g` the largest good value at most `X(j)`, the candidate test is right. -/
theorem candidate {j c r X g : ℕ} (hX : IsFirst A j c r X) (hjc : j ≤ c)
    (hg : IsGreatest {x | c + 2 ≤ x ∧ x ≤ X ∧ Good B c x} g)
    (h₁ : ∀ t, j < t → t ≤ c → j ≤ A t) (h₂ : ∀ t, j < t → t ≤ c → B t < g) :
    Closed A B j g ∧ ∀ x, c + 2 ≤ x → x ≤ r + 1 → Closed A B j x → x ≤ g := by
  obtain ⟨⟨hg₁, hg₂, hg₃⟩, hgmax⟩ := hg
  constructor
  · intro t hjt htg
    by_cases htc : t ≤ c
    · exact ⟨h₁ t hjt htc, h₂ t hjt htc⟩
    · exact ⟨hX.before t (by omega) (by omega), hg₃ t (by omega) htg⟩
  · intro x hx hxr hc
    obtain ⟨h₃, h₄⟩ := closed_mem hX hjc hxr hc
    exact hgmax ⟨hx, h₃, h₄⟩

/-- **Lemma 5.** If some end in `Y` is closed, then the test accepts. -/
theorem candidate_exists {j c r X g x : ℕ} (hX : IsFirst A j c r X) (hjc : j ≤ c)
    (hg : IsGreatest {x | c + 2 ≤ x ∧ x ≤ X ∧ Good B c x} g) (hx : c + 2 ≤ x) (hxr : x ≤ r + 1) (hc : Closed A B j x) :
    (∀ t, j < t → t ≤ c → j ≤ A t) ∧ (∀ t, j < t → t ≤ c → B t < g) := by
  obtain ⟨h₃, h₄⟩ := closed_mem hX hjc hxr hc
  have hxg := hg.2 ⟨hx, h₃, h₄⟩
  constructor
  · exact fun t h₁ h₂ => (hc t h₁ (by omega)).1
  · intro t h₁ h₂
    have := (hc t h₁ (by omega)).2
    omega

/-- **Lemma 6.** -/
theorem ring {j j' m m' c r X : ℕ} (hj'j : j' < j) (hmm : m < m') (hjc : j ≤ c) (hm : c + 2 ≤ m)
    (hm' : m' ≤ r + 1) (hX : IsFirst A j c r X) (hc' : Closed A B j' m') (hc : Closed A B j m)
    (hmax : ∀ x, Closed A B j x → x ≤ m) : m ≤ X ∧ X < m' ∧ j' ≤ A X ∧ A X < j := by
  have hnot : ¬ Closed A B j m' := fun h => by
    have := hmax m' h
    omega
  have hex : ∃ t, j < t ∧ t < m' ∧ ¬ (j ≤ A t ∧ B t < m') := by
    by_contra hn
    refine hnot fun t h₁ h₂ => ?_
    by_contra h₃
    exact hn ⟨t, h₁, h₂, h₃⟩
  obtain ⟨t, hjt, htm', ht⟩ := hex
  have hB := (hc' t (by omega) htm').2
  have hAj : A t < j := by
    by_contra hn
    exact ht ⟨by omega, hB⟩
  have htm : m ≤ t := by
    by_contra hn
    have := (hc t hjt (by omega)).1
    omega
  have hXt : X ≤ t := by
    by_contra hn
    have := hX.before t (by omega) (by omega)
    omega
  have hmX : m ≤ X := by
    by_contra hn
    have hXr : X ≤ r := by omega
    have h₁ := hX.at_ hXr
    have h₂ := (hc X (by have := hX.lo; omega) (by omega)).1
    omega
  have hXr : X ≤ r := by omega
  have h₁ := hX.at_ hXr
  have h₂ := (hc' X (by omega) (by omega)).1
  exact ⟨hmX, by omega, h₂, h₁⟩

end Segment

/-! ## Reading off -/

section Readoff

variable {m : ℕ → ℕ}

/-- The intervals are laminar, and each `m j` is above `j`. -/
structure Laminar (m : ℕ → ℕ) : Prop where
  above : ∀ j, j < m j
  nested : ∀ j j', j < j' → j' < m j → m j' ≤ m j

/-- The rule for `δ`: between the ends of two consecutive members, the last member with a larger end is the earlier one. -/
theorem delta_ring (hL : Laminar m) {l c t j₀ j₁ : ℕ} (hj₀ : l ≤ j₀) (hj₀₁ : j₀ < j₁) (hj₁c : j₁ ≤ c) (hc₁ : c + 1 < m j₁)
    (hnext : ∀ j, j₀ < j → j < j₁ → m j ≤ c + 1) (ht₁ : m j₁ ≤ t) (ht₀ : t < m j₀) :
    IsGreatest {j | l ≤ j ∧ j ≤ c ∧ c + 1 < m j ∧ t < m j} j₀ := by
  refine ⟨⟨hj₀, by omega, by omega, ht₀⟩, ?_⟩
  rintro j ⟨-, hjc, hjm, htj⟩
  by_contra hlt
  by_cases hj : j < j₁
  · have := hnext j (by omega) hj
    omega
  · by_cases hne : j = j₁
    · rw [hne] at htj
      omega
    · have := hL.nested j₁ j (by omega) (by omega)
      omega

/-- **Lemma 7.** The last common member of the two prefixes is the earlier of `λ` and `δ`. -/
theorem readoff (hL : Laminar m) {l c a b lam dlt : ℕ} (hal : a ≤ c) (hbc : c + 1 ≤ b)
    (hlam : IsGreatest {j | l ≤ j ∧ j ≤ c ∧ c + 1 < m j ∧ j ≤ a} lam)
    (hdlt : IsGreatest {j | l ≤ j ∧ j ≤ c ∧ c + 1 < m j ∧ b < m j} dlt) :
    IsGreatest {j | l ≤ j ∧ j ≤ a ∧ b < m j} (min lam dlt) := by
  obtain ⟨⟨h₁, h₂, h₃, h₄⟩, hlmax⟩ := hlam
  obtain ⟨⟨h₅, h₆, h₇, h₈⟩, hdmax⟩ := hdlt
  refine ⟨?_, ?_⟩
  · by_cases hle : lam ≤ dlt
    · rw [min_eq_left hle]
      refine ⟨h₁, h₄, ?_⟩
      by_cases heq : lam = dlt
      · rw [heq]
        exact h₈
      · have := hL.nested lam dlt (by omega) (by omega)
        omega
    · rw [min_eq_right (by omega)]
      exact ⟨h₅, by omega, h₈⟩
  · rintro j ⟨hj₁, hj₂, hj₃⟩
    have h₉ := hlmax ⟨hj₁, by omega, by omega, hj₂⟩
    have h₁₀ := hdmax ⟨hj₁, by omega, by omega, hj₃⟩
    exact le_min h₉ h₁₀

/-- **Lemma 7.** If a set of members is empty, no vertex of `Z` qualifies. -/
theorem readoff_none {l c a b : ℕ} (hal : a ≤ c) (hbc : c + 1 ≤ b)
    (h : ∀ j, l ≤ j → j ≤ c → c + 1 < m j → ¬ (j ≤ a ∧ b < m j)) {j : ℕ} (hj₁ : l ≤ j) (hj₂ : j ≤ a) : m j ≤ b := by
  by_contra hn
  exact h j hj₁ (by omega) (by omega) ⟨hj₂, by omega⟩

end Readoff

end PlanarMatching.Dominators
