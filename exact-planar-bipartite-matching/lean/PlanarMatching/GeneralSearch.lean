import PlanarMatching.DagSearch
import Mathlib.Data.Set.Finite.Basic

/-!
# Depth-first search of any digraph: end, pivot, cycle and pass

`notes/GENERAL_DFS.md`, Sections 3 to 6, on any finite digraph. Planarity enters only through the separator, which is a
hypothesis here. `end_a` and `end_b` are Lemma 1. `pivot` is Lemma 2. `join` and `close` are Lemma 3. `pass_a` and `pass_b`
are Lemma 5, and `pass_piece` is its last claim.

The hypothesis of `pivot` on the separator is weaker than in the note: only the set reached from `y` off the two paths has
to be small, not the whole connected component of `y`.
-/

namespace PlanarMatching.GeneralSearch

open Relation PlanarMatching.DagSearch

variable {V : Type*}

theorem reach_mono {D : V → V → Prop} {R T : Set V} (h : R ⊆ T) {a b : V} (hr : Reach D R a b) : Reach D T a b := by
  induction hr with
  | refl => exact ReflTransGen.refl
  | tail _ hab ih => exact ih.tail ⟨hab.1, h hab.2.1, h hab.2.2⟩

/-- The set reached from `v` in `D[Q]`. -/
def rset (D : V → V → Prop) (Q : Set V) (v : V) : Set V := {w | Reach D Q v w}

/-- `f(v)`, the size of `rset`. -/
noncomputable def f (D : V → V → Prop) (Q : Set V) (v : V) : ℕ := (rset D Q v).ncard

section Sizes

variable [Finite V] {D : V → V → Prop} {Q : Set V}

theorem f_le {a b : V} (h : Reach D Q a b) : f D Q b ≤ f D Q a :=
  Set.ncard_le_ncard (fun _ hw => h.trans hw) (Set.toFinite _)

end Sizes

/-! ## Lemma 1 -/

section End

variable {S : Split V}

/-- **Lemma 1(a).** -/
theorem end_a {z y : V} (hz : S.IsHead z) (hy : y ∈ S.cls z) (h : Reach S.D S.K (S.v S.k) (S.p z)) :
    Reach S.D S.K (S.v S.k) y := by
  have hRK : S.cls z ⊆ S.K := fun _ hw => hw.1.1
  have hp : S.p z ∈ S.K := S.path.mem _ (Split.depth_le z)
  exact (h.tail ⟨Split.p_arc hz, hp, hz.1.1⟩).trans (reach_mono hRK (Split.lemma1a_reach hz hy))

/-- Every vertex reached from the path leaves it for the last time. -/
theorem last_exit {a : ℕ} (ha : a ≤ S.k) {w : V} (h : Reach S.D S.K (S.v a) w) :
    (∃ i ≤ S.k, S.v i = w ∧ Reach S.D S.K (S.v a) (S.v i)) ∨
      ∃ i ≤ S.k, Reach S.D S.K (S.v a) (S.v i) ∧ ∃ z, S.IsHead z ∧ S.D (S.v i) z ∧ Reach S.D S.R z w := by
  induction h with
  | refl => exact Or.inl ⟨a, ha, rfl, ReflTransGen.refl⟩
  | @tail c w' hr h ih =>
    by_cases hw' : S.OnPath w'
    · obtain ⟨i, hi, rfl⟩ := hw'
      exact Or.inl ⟨i, hi, rfl, hr.tail h⟩
    · have hw'R : w' ∈ S.R := ⟨h.2.2, hw'⟩
      rcases ih with ⟨i, hi, rfl, hri⟩ | ⟨i, hi, hri, z, hz, hd, hrz⟩
      · exact Or.inr ⟨i, hi, hri, w', ⟨hw'R, i, hi, h.1⟩, h.1, ReflTransGen.refl⟩
      · exact Or.inr ⟨i, hi, hri, z, hz, hd, hrz.tail ⟨h.1, hrz.mem hz.1, hw'R⟩⟩

/-- **Lemma 1(b).** -/
theorem end_b {z y : V} (hy : y ∈ S.cls z) (h : ¬ Reach S.D S.K (S.v S.k) (S.p z)) :
    ¬ Reach S.D S.K (S.v S.k) y := by
  intro hm
  rcases last_exit le_rfl hm with ⟨i, _, rfl, _⟩ | ⟨i, hi, hri, z', hz', hd, hrz⟩
  · exact hy.1.2 ⟨i, by assumption, rfl⟩
  · have hdz := Split.depth_le (S := S) z
    have hlt : S.depth z < i := by
      by_contra hc
      exact h (hri.trans (S.path.reach (not_lt.1 hc) hdz))
    have h₁ : S.e y ≤ S.key z' := Split.e_le hz' hrz
    have h₂ : S.key z' ≤ S.arcKey i z' := (Split.key_isLeast hz').2 ⟨i, hi, hd, rfl⟩
    have h₃ : S.arcKey i z' < S.key z := by
      simp only [Split.key, Split.arcKey]
      exact Prod.Lex.toLex_lt_toLex.2 (Or.inl (by simp only []; omega))
    have h₄ := hy.2
    exact absurd (h₁.trans_lt (h₂.trans_lt h₃)) (by rw [h₄]; exact lt_irrefl _)

end End

/-! ## Lemma 2 -/

section Pivot

variable [Finite V] {D : V → V → Prop} {Q : Set V} {W : ℕ}

/-- One of the two paths, with the last high vertex `v j` and the next vertex low. -/
structure Arm (D : V → V → Prop) (Q : Set V) (W : ℕ) (k : ℕ) (v : ℕ → V) (j : ℕ) : Prop where
  path : IsPath D Q k v
  le : j ≤ k
  low : j < k → 16 * f D Q (v (j + 1)) < W

/-- What one arm contributes to the set reached from `y`, if `y` does not reach its last high vertex. -/
theorem Arm.cover {k j : ℕ} {v : ℕ → V} (h : Arm D Q W k v j) {y : V} (hy : ¬ Reach D Q y (v j)) :
    ∃ A : Set V, 16 * A.ncard ≤ W ∧ (∀ t ≤ k, Reach D Q y (v t) → v t ∈ A) ∧
      ∀ a b, a ∈ A → Induced D Q a b → b ∈ A := by
  classical
  by_cases hex : ∃ t, t ≤ k ∧ Reach D Q y (v t)
  · have htm := Nat.find_spec hex
    set m := Nat.find hex with hm
    have hjm : j < m := by
      by_contra hc
      exact hy (htm.2.trans (h.path.reach (not_lt.1 hc) h.le))
    have hlow := h.low (by omega)
    refine ⟨rset D Q (v m), ?_, ?_, ?_⟩
    · have := f_le (D := D) (Q := Q) (h.path.reach (show j + 1 ≤ m by omega) htm.1)
      have h' : (rset D Q (v m)).ncard = f D Q (v m) := rfl
      omega
    · intro t ht hr
      have : m ≤ t := Nat.find_min' hex ⟨ht, hr⟩
      exact h.path.reach this ht
    · intro a b ha hab
      exact ReflTransGen.tail ha hab
  · refine ⟨∅, by simp, fun t ht hr => absurd ⟨t, ht, hr⟩ hex, fun _ _ ha => absurd ha (by simp)⟩

/-- The vertices of the two paths. -/
def Sep (k₁ : ℕ) (v₁ : ℕ → V) (k₂ : ℕ) (v₂ : ℕ → V) : Set V :=
  {w | (∃ t ≤ k₁, v₁ t = w) ∨ ∃ t ≤ k₂, v₂ t = w}

/-- A high vertex on an arm reaches the last high vertex of the arm. -/
theorem Arm.on_arm {k j t : ℕ} {v : ℕ → V} (h : Arm D Q W k v j) (ht : t ≤ k) (hh : 7 * W < 8 * f D Q (v t)) :
    Reach D Q (v t) (v j) := by
  by_cases hc : t ≤ j
  · exact h.path.reach hc h.le
  · have hlow := h.low (by omega)
    have := f_le (D := D) (Q := Q) (h.path.reach (show j + 1 ≤ t by omega) ht)
    omega

/-- **Lemma 2.** No vertex strictly below the chosen component is high. -/
theorem pivot {k₁ k₂ j₁ j₂ : ℕ} {v₁ v₂ : ℕ → V} (h₁ : Arm D Q W k₁ v₁ j₁) (h₂ : Arm D Q W k₂ v₂ j₂)
    (hsep : ∀ y ∈ Q, y ∉ Sep k₁ v₁ k₂ v₂ → 4 * (rset D (Q \ Sep k₁ v₁ k₂ v₂) y).ncard ≤ 3 * W)
    {c : V}
    (hc : (c = v₂ j₂ ∧ Reach D Q (v₁ j₁) (v₂ j₂) ∧ ¬ Reach D Q (v₂ j₂) (v₁ j₁)) ∨
      (c = v₁ j₁ ∧ ¬ (Reach D Q (v₁ j₁) (v₂ j₂) ∧ ¬ Reach D Q (v₂ j₂) (v₁ j₁))))
    {y : V} (hy : y ∈ Q) (hcy : Reach D Q c y) (hyc : ¬ Reach D Q y c) : 8 * f D Q y ≤ 7 * W := by
  classical
  by_contra hhigh
  have hhigh' : 7 * W < 8 * f D Q y := by omega
  -- first, `y` reaches one of the two last high vertices
  have key : Reach D Q y (v₁ j₁) ∨ Reach D Q y (v₂ j₂) := by
    by_contra hno
    push Not at hno
    obtain ⟨hn₁, hn₂⟩ := hno
    by_cases hs : y ∈ Sep k₁ v₁ k₂ v₂
    · rcases hs with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
      · exact hn₁ (h₁.on_arm ht hhigh')
      · exact hn₂ (h₂.on_arm ht hhigh')
    · obtain ⟨A₁, hA₁, hc₁, hcl₁⟩ := h₁.cover hn₁
      obtain ⟨A₂, hA₂, hc₂, hcl₂⟩ := h₂.cover hn₂
      set X := rset D (Q \ Sep k₁ v₁ k₂ v₂) y with hX
      have hyoff : y ∈ Q \ Sep k₁ v₁ k₂ v₂ := ⟨hy, hs⟩
      have hcov : rset D Q y ⊆ X ∪ (A₁ ∪ A₂) := by
        intro w hw
        induction hw with
        | refl => exact Or.inl ReflTransGen.refl
        | @tail a b hr hab ih =>
          have hrb : Reach D Q y b := hr.tail hab
          by_cases hbs : b ∈ Sep k₁ v₁ k₂ v₂
          · rcases hbs with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
            · exact Or.inr (Or.inl (hc₁ t ht hrb))
            · exact Or.inr (Or.inr (hc₂ t ht hrb))
          · rcases ih with hX' | hA | hA
            · refine Or.inl (ReflTransGen.tail hX' ⟨hab.1, ?_, hab.2.2, hbs⟩)
              exact Reach.mem hX' hyoff
            · exact Or.inr (Or.inl (hcl₁ a b hA hab))
            · exact Or.inr (Or.inr (hcl₂ a b hA hab))
      have hle : f D Q y ≤ X.ncard + (A₁.ncard + A₂.ncard) :=
        (Set.ncard_le_ncard hcov (Set.toFinite _)).trans
          ((Set.ncard_union_le _ _).trans (Nat.add_le_add_left (Set.ncard_union_le _ _) _))
      have hXs : 4 * X.ncard ≤ 3 * W := hsep y hy hs
      omega
  rcases hc with ⟨rfl, _, hn⟩ | ⟨rfl, hn⟩
  · rcases key with hk | hk
    · exact hn (hcy.trans hk)
    · exact hyc hk
  · rcases key with hk | hk
    · exact hyc hk
    · have hr : Reach D Q (v₁ j₁) (v₂ j₂) := hcy.trans hk
      have : Reach D Q (v₂ j₂) (v₁ j₁) := by
        by_contra hc'
        exact hn ⟨hr, hc'⟩
      exact hyc (hk.trans this)

end Pivot

/-! ## Lemma 5 -/

section Pass

variable [Finite V] {S : Split V} {W : ℕ}

theorem disjoint_card {z : V} (h : ¬ Reach S.D S.K (S.v S.k) (S.p z)) :
    (S.cls z).ncard + f S.D S.K (S.v S.k) ≤ S.K.ncard := by
  have hd : Disjoint (S.cls z) (rset S.D S.K (S.v S.k)) :=
    Set.disjoint_left.2 fun _ hy hw => end_b hy h hw
  rw [f, ← Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro w (hw | hw)
  · exact hw.1.1
  · exact Reach.mem hw (S.path.mem _ le_rfl)

/-- **Lemma 5(a).** A path that ends at a mid vertex leaves no bad class. -/
theorem pass_a (hQ : S.K.ncard ≤ W) (hlo : W ≤ 16 * f S.D S.K (S.v S.k)) (hhi : 8 * f S.D S.K (S.v S.k) ≤ 7 * W)
    {z : V} (hz : S.IsHead z) : 16 * (S.cls z).ncard ≤ 15 * W := by
  by_cases h : Reach S.D S.K (S.v S.k) (S.p z)
  · have : (S.cls z).ncard ≤ f S.D S.K (S.v S.k) :=
      Set.ncard_le_ncard (fun _ hy => end_a hz hy h) (Set.toFinite _)
    omega
  · have := disjoint_card h
    omega

/-- **Lemma 5(b).** Let `m`, the end of the path, be high, with nothing strictly below its component high. A vertex that
reaches more than `7W/8` vertices inside a bad class lies in the component of `m`. -/
theorem pass_b (hQ : S.K.ncard ≤ W) (hhi : 7 * W < 8 * f S.D S.K (S.v S.k))
    (hL : ∀ y ∈ S.K, Reach S.D S.K (S.v S.k) y → ¬ Reach S.D S.K y (S.v S.k) → 8 * f S.D S.K y ≤ 7 * W)
    {z y : V} (hz : S.IsHead z) (hbad : 15 * W < 16 * (S.cls z).ncard) (hy : y ∈ S.cls z)
    (hv : 7 * W < 8 * f S.D (S.cls z) y) :
    Reach S.D S.K (S.v S.k) y ∧ Reach S.D S.K y (S.v S.k) := by
  have hm : Reach S.D S.K (S.v S.k) (S.p z) := by
    by_contra h
    have := disjoint_card h
    omega
  have hmy := end_a hz hy hm
  refine ⟨hmy, ?_⟩
  by_contra hn
  have h₁ := hL y hy.1.1 hmy hn
  have hRK : S.cls z ⊆ S.K := fun _ hw => hw.1.1
  have h₂ : f S.D (S.cls z) y ≤ f S.D S.K y :=
    Set.ncard_le_ncard (fun _ hw => reach_mono hRK hw) (Set.toFinite _)
  omega

end Pass

/-! ## Lemma 3 -/

section Cycle

variable [Finite V] {D : V → V → Prop} {L : Set V}

/-- `X` is strongly connected in `D[X]`. -/
def Strong (D : V → V → Prop) (X : Set V) : Prop := ∀ a ∈ X, ∀ b ∈ X, Reach D X a b

/-- `D[L ∖ S]` holds a strongly connected set of more than `3/4` of `L`. -/
def HasHeavy (D : V → V → Prop) (L S : Set V) : Prop :=
  ∃ X, X ⊆ L \ S ∧ Strong D X ∧ 3 * L.ncard < 4 * X.ncard

omit [Finite V] in
theorem HasHeavy.anti {S T : Set V} (h : S ⊆ T) (ht : HasHeavy D L T) : HasHeavy D L S := by
  obtain ⟨X, hX, hs, hc⟩ := ht
  exact ⟨X, fun _ hx => ⟨(hX hx).1, fun hS => (hX hx).2 (h hS)⟩, hs, hc⟩

/-- Two heavy sets meet. -/
theorem heavy_meet {X Y : Set V} (hX : X ⊆ L) (hY : Y ⊆ L) (hx : 3 * L.ncard < 4 * X.ncard)
    (hy : 3 * L.ncard < 4 * Y.ncard) : ∃ w, w ∈ X ∧ w ∈ Y := by
  by_contra hne
  push Not at hne
  have hd : Disjoint X Y := Set.disjoint_left.2 hne
  have := Set.ncard_le_ncard (Set.union_subset hX hY) (Set.toFinite _)
  rw [Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)] at this
  omega

/-- The vertices `p a, ..., p (b - 1)`. -/
def seg (p : ℕ → V) (a b : ℕ) : Set V := {w | ∃ t, a ≤ t ∧ t < b ∧ p t = w}

omit [Finite V] in
/-- A heavy set that disappears when one more vertex is removed holds that vertex. -/
theorem heavy_holds {S : Set V} {u : V} (h : HasHeavy D L S) (hn : ¬ HasHeavy D L (S ∪ {u})) :
    ∃ X, X ⊆ L \ S ∧ Strong D X ∧ 3 * L.ncard < 4 * X.ncard ∧ u ∈ X := by
  obtain ⟨X, hX, hs, hc⟩ := h
  refine ⟨X, hX, hs, hc, ?_⟩
  by_contra hu
  refine hn ⟨X, fun x hx => ⟨(hX hx).1, ?_⟩, hs, hc⟩
  rintro (hS | rfl)
  · exact (hX hx).2 hS
  · exact hu hx

omit [Finite V] in
/-- The segment of `Trim`: a least prefix with no heavy set, then its shortest suffix. -/
theorem trim {s : ℕ} {p : ℕ → V} {O : Set V} (hO : HasHeavy D L O) (hall : ¬ HasHeavy D L (O ∪ seg p 0 (s + 1))) :
    ∃ h i, h ≤ i ∧ i ≤ s ∧ ¬ HasHeavy D L (O ∪ seg p h (i + 1)) ∧
      (∃ X, X ⊆ L \ (O ∪ seg p 0 i) ∧ Strong D X ∧ 3 * L.ncard < 4 * X.ncard ∧ p i ∈ X) ∧
      (∃ Y, Y ⊆ L \ (O ∪ seg p (h + 1) (i + 1)) ∧ Strong D Y ∧ 3 * L.ncard < 4 * Y.ncard ∧ p h ∈ Y) := by
  classical
  have hex : ∃ i, ¬ HasHeavy D L (O ∪ seg p 0 (i + 1)) := ⟨s, hall⟩
  set i := Nat.find hex with hi
  have hspec : ¬ HasHeavy D L (O ∪ seg p 0 (i + 1)) := Nat.find_spec hex
  have his : i ≤ s := Nat.find_min' hex hall
  have hseg : ∀ a b, a ≤ b → seg p a (b + 1) = seg p a b ∪ {p b} := by
    intro a b hab
    ext w
    constructor
    · rintro ⟨t, h₁, h₂, rfl⟩
      by_cases ht : t = b
      · exact Or.inr (by rw [ht]; rfl)
      · exact Or.inl ⟨t, h₁, by omega, rfl⟩
    · rintro (⟨t, h₁, h₂, rfl⟩ | hw)
      · exact ⟨t, h₁, by omega, rfl⟩
      · exact ⟨b, hab, by omega, hw.symm⟩
  have hprev : HasHeavy D L (O ∪ seg p 0 i) := by
    cases hi0 : i with
    | zero =>
      have : O ∪ seg p 0 0 = O := by
        ext w
        constructor
        · rintro (hw | ⟨t, _, h₂, _⟩)
          · exact hw
          · omega
        · exact Or.inl
      rw [this]
      exact hO
    | succ i' =>
      have : i' < Nat.find hex := by omega
      have hm := Nat.find_min hex this
      exact not_not.1 hm
  have hX := heavy_holds (u := p i) hprev (by
    rw [Set.union_assoc, ← hseg 0 i (Nat.zero_le _)]
    exact hspec)
  -- the suffix: greatest start with no heavy set
  let P : ℕ → Prop := fun h => ¬ HasHeavy D L (O ∪ seg p h (i + 1))
  have hP0 : P 0 := hspec
  set h := Nat.findGreatest P i with hh
  have hPh : P h := Nat.findGreatest_spec (P := P) (Nat.zero_le i) hP0
  have hhi : h ≤ i := Nat.findGreatest_le _
  have hnext : HasHeavy D L (O ∪ seg p (h + 1) (i + 1)) := by
    by_cases hlt : h < i
    · have := Nat.findGreatest_is_greatest (P := P) (n := i) (k := h + 1) (Nat.lt_succ_self _) (by omega)
      exact not_not.1 this
    · have heq : h = i := by omega
      have : seg p (h + 1) (i + 1) ⊆ seg p 0 i := by
        rintro _ ⟨t, h₁, h₂, _⟩
        omega
      exact HasHeavy.anti (Set.union_subset_union_right _ this) hprev
  have hsplit : seg p h (i + 1) = seg p (h + 1) (i + 1) ∪ {p h} := by
    ext w
    constructor
    · rintro ⟨t, h₁, h₂, rfl⟩
      by_cases ht : t = h
      · exact Or.inr (by rw [ht]; rfl)
      · exact Or.inl ⟨t, by omega, h₂, rfl⟩
    · rintro (⟨t, h₁, h₂, rfl⟩ | hw)
      · exact ⟨t, by omega, h₂, rfl⟩
      · exact ⟨h, le_rfl, by omega, hw.symm⟩
  have hY := heavy_holds (u := p h) hnext (by
    rw [Set.union_assoc, ← hsplit]
    exact hPh)
  exact ⟨h, i, hhi, his, hPh, hX, hY⟩

omit [Finite V] in
/-- Concatenation of two simple paths that share only an end. -/
theorem IsPath.append {K : Set V} {a b : ℕ} {u w : ℕ → V} (hu : IsPath D K a u) (hw : IsPath D K b w)
    (hend : u a = w 0) (hd : ∀ i ≤ a, ∀ j ≤ b, u i = w j → i = a ∧ j = 0) :
    IsPath D K (a + b) (fun t => if t ≤ a then u t else w (t - a)) := by
  refine ⟨fun t ht => ?_, fun s hs t ht e => ?_, fun t ht => ?_⟩
  · by_cases h : t ≤ a
    · simpa [h] using hu.mem t h
    · simpa [h] using hw.mem (t - a) (by omega)
  · by_cases h₁ : s ≤ a <;> by_cases h₂ : t ≤ a <;> simp only [h₁, h₂, ite_true, ite_false] at e
    · exact hu.inj s h₁ t h₂ e
    · have := hd s h₁ (t - a) (by omega) e
      omega
    · have := hd t h₂ (s - a) (by omega) e.symm
      omega
    · have := hw.inj (s - a) (by omega) (t - a) (by omega) e
      omega
  · by_cases h₁ : t < a
    · have h₂ : t + 1 ≤ a := h₁
      have h₃ : t ≤ a := by omega
      simpa [h₂, h₃] using hu.arc t h₁
    · by_cases h₂ : t = a
      · subst h₂
        have h₃ : ¬ t + 1 ≤ t := by omega
        simp only [le_refl, ite_true, h₃, ite_false]
        rw [hend, show t + 1 - t = 0 + 1 by omega]
        exact hw.arc 0 (by omega)
      · have h₃ : ¬ t ≤ a := by omega
        have h₄ : ¬ t + 1 ≤ a := by omega
        simp only [h₃, h₄, ite_false]
        rw [show t + 1 - a = (t - a) + 1 by omega]
        exact hw.arc (t - a) (by omega)

omit [Finite V] in
/-- A segment of a simple path is a simple path. -/
theorem IsPath.slice {K : Set V} {k h i : ℕ} {p : ℕ → V} (hp : IsPath D K k p) (hh : h ≤ i) (hi : i ≤ k) :
    IsPath D K (i - h) (fun t => p (h + t)) :=
  ⟨fun t ht => hp.mem _ (by omega), fun s hs t ht e => by
    have := hp.inj _ (by omega) _ (by omega) e
    omega, fun t ht => hp.arc _ (by omega)⟩

omit [Finite V] in
/-- A simple path in `D[X ∪ Y]` from a vertex of `X` to a vertex of `Y`, if they meet. -/
theorem link {X Y : Set V} (hX : Strong D X) (hY : Strong D Y) {a b : V} (ha : a ∈ X) (hb : b ∈ Y) {w : V} (hwX : w ∈ X)
    (hwY : w ∈ Y) : ∃ n q, IsPath D (X ∪ Y) n q ∧ q 0 = a ∧ q n = b := by
  have h₁ := reach_mono (T := X ∪ Y) Set.subset_union_left (hX a ha w hwX)
  have h₂ := reach_mono (T := X ∪ Y) Set.subset_union_right (hY w hwY b hb)
  exact exists_path (h₁.trans h₂) (Or.inl ha)

/-- **Lemma 3, Close.** A path that leaves no heavy set gives a cycle that leaves no heavy set. A cycle of one vertex has
`n = 0`. -/
theorem close {s : ℕ} {u : ℕ → V} (hu : IsPath D L s u) (hL : Strong D L) (hne : 0 < L.ncard)
    (hall : ¬ HasHeavy D L (seg u 0 (s + 1))) :
    ∃ n c, IsPath D L n c ∧ (n = 0 ∨ D (c n) (c 0)) ∧ ¬ HasHeavy D L {w | ∃ t ≤ n, c t = w} := by
  classical
  have hO : HasHeavy D L ∅ :=
    ⟨L, by simp, hL, by omega⟩
  have hall' : ¬ HasHeavy D L (∅ ∪ seg u 0 (s + 1)) := by simpa using hall
  obtain ⟨h, i, hhi, his, hP, ⟨X, hX, hXs, hXc, hXi⟩, ⟨Y, hY, hYs, hYc, hYh⟩⟩ := trim hO hall'
  by_cases heq : h = i
  · subst heq
    refine ⟨0, fun _ => u h, ⟨fun _ _ => hu.mem h his, fun a ha b hb _ => by omega, fun a ha => by omega⟩,
      Or.inl rfl, ?_⟩
    intro hheavy
    refine hP (HasHeavy.anti ?_ hheavy)
    rintro w (hw | ⟨t, h₁, h₂, rfl⟩)
    · exact absurd hw (by simp)
    · have : t = h := by omega
      exact ⟨0, le_rfl, by simp [this]⟩
  · have hlt : h < i := by omega
    have hXL : X ⊆ L := fun _ hx => (hX hx).1
    have hYL : Y ⊆ L := fun _ hx => (hY hx).1
    obtain ⟨w, hwX, hwY⟩ := heavy_meet hXL hYL hXc hYc
    obtain ⟨n, q, hq, hq0, hqn⟩ := link hXs hYs hXi hYh hwX hwY
    have hqL : IsPath D L n q :=
      ⟨fun t ht => Set.union_subset hXL hYL (hq.mem t ht), hq.inj, hq.arc⟩
    -- inner vertices of `q` miss the segment
    have hmiss : ∀ t ≤ n, ∀ a, h ≤ a → a ≤ i → q t = u a → (t = 0 ∧ a = i) ∨ (t = n ∧ a = h) := by
      intro t ht a h₁ h₂ e
      rcases hq.mem t ht with hx | hy
      · have hai : a = i := by
          by_contra hne'
          exact (hX hx).2 (Or.inr ⟨a, Nat.zero_le _, by omega, e.symm⟩)
        subst hai
        have : t = 0 := hq.inj t ht 0 (Nat.zero_le _) (by rw [e, hq0])
        exact Or.inl ⟨this, rfl⟩
      · have hah : a = h := by
          by_contra hne'
          exact (hY hy).2 (Or.inr ⟨a, by omega, by omega, e.symm⟩)
        subst hah
        have : t = n := hq.inj t ht n le_rfl (by rw [e, hqn])
        exact Or.inr ⟨this, rfl⟩
    have hn : 0 < n := by
      by_contra h0
      have : n = 0 := by omega
      subst this
      have : u i = u h := by rw [← hq0, hqn]
      have := hu.inj i his h (by omega) this
      omega
    -- the cycle: the segment, then `q` without its two ends
    have hseg := IsPath.slice hu hhi his
    have hqin : IsPath D L (n - 1) q := ⟨fun t ht => hqL.mem t (by omega),
      fun a ha b hb e => hqL.inj a (by omega) b (by omega) e, fun t ht => hqL.arc t (by omega)⟩
    have hc := IsPath.append (D := D) (K := L) (a := i - h) (b := n - 1) (u := fun t => u (h + t)) (w := q) hseg hqin
      (by simp only [show h + (i - h) = i by omega]; exact hq0.symm)
      (by
        intro a ha b hb e
        rcases hmiss b (by omega) (h + a) (by omega) (by omega) e.symm with ⟨h₁, h₂⟩ | ⟨h₁, _⟩
        · exact ⟨by omega, h₁⟩
        · omega)
    refine ⟨i - h + (n - 1), _, hc, Or.inr ?_, ?_⟩
    · have h0 : (0 : ℕ) ≤ i - h := Nat.zero_le _
      simp only [h0, ite_true, Nat.add_zero]
      by_cases hn1 : n - 1 = 0
      · have h₂ : i - h + (n - 1) ≤ i - h := by omega
        simp only [h₂, ite_true]
        have hn2 : n = 1 := by omega
        have ha := hq.arc 0 (by omega)
        rw [hq0, show 0 + 1 = n by omega, hqn] at ha
        simpa [show h + (i - h + (n - 1)) = i by omega] using ha
      · have h₂ : ¬ i - h + (n - 1) ≤ i - h := by omega
        simp only [h₂, ite_false]
        have ha := hq.arc (n - 1) (by omega)
        rw [show n - 1 + 1 = n by omega, hqn] at ha
        simpa [show i - h + (n - 1) - (i - h) = n - 1 by omega] using ha
    · intro hheavy
      refine hP (HasHeavy.anti ?_ hheavy)
      rintro w (hw | ⟨t, h₁, h₂, rfl⟩)
      · exact absurd hw (by simp)
      · refine ⟨t - h, by omega, ?_⟩
        have h₃ : t - h ≤ i - h := by omega
        simp [h₃, show h + (t - h) = t by omega]

/-- **Lemma 3, Join.** Two disjoint paths that leave no heavy set give one path that leaves no heavy set. -/
theorem join {a b : ℕ} {A B : ℕ → V} (hA : IsPath D L a A) (hB : IsPath D L b B)
    (hd : ∀ i ≤ a, ∀ j ≤ b, A i ≠ B j)
    (hall : ¬ HasHeavy D L (seg A 0 (a + 1) ∪ seg B 0 (b + 1))) :
    ∃ m U, IsPath D L m U ∧ ¬ HasHeavy D L (seg U 0 (m + 1)) := by
  classical
  by_cases hb0 : HasHeavy D L (seg B 0 (b + 1))
  · -- trim `A` against all of `B`
    have hall₁ : ¬ HasHeavy D L (seg B 0 (b + 1) ∪ seg A 0 (a + 1)) := by rwa [Set.union_comm]
    obtain ⟨h, i, hhi, hia, hP, ⟨X, hX, hXs, hXc, hXi⟩, -⟩ := trim hb0 hall₁
    set A' := seg A h (i + 1) with hA'
    by_cases ha0 : HasHeavy D L A'
    · -- trim `B` against the segment of `A`
      have hall₂ : ¬ HasHeavy D L (A' ∪ seg B 0 (b + 1)) := by
        rwa [Set.union_comm]
      obtain ⟨g, j, hgj, hjb, hQ, -, ⟨Y, hY, hYs, hYc, hYg⟩⟩ := trim ha0 hall₂
      have hXL : X ⊆ L := fun _ hx => (hX hx).1
      have hYL : Y ⊆ L := fun _ hx => (hY hx).1
      obtain ⟨w, hwX, hwY⟩ := heavy_meet hXL hYL hXc hYc
      obtain ⟨n, q, hq, hq0, hqn⟩ := link hXs hYs hXi hYg hwX hwY
      have hqL : IsPath D L n q :=
        ⟨fun t ht => Set.union_subset hXL hYL (hq.mem t ht), hq.inj, hq.arc⟩
      have hsA := IsPath.slice hA hhi hia
      have hsB := IsPath.slice hB hgj hjb
      -- `q` meets the segment of `A` only in its first vertex
      have hmissA : ∀ t ≤ n, ∀ s, h ≤ s → s ≤ i → q t = A s → t = 0 ∧ s = i := by
        intro t ht s h₁ h₂ e
        rcases hq.mem t ht with hx | hy
        · have hsi : s = i := by
            by_contra hne'
            exact (hX hx).2 (Or.inr ⟨s, Nat.zero_le _, by omega, e.symm⟩)
          subst hsi
          exact ⟨hq.inj t ht 0 (Nat.zero_le _) (by rw [e, hq0]), rfl⟩
        · exact absurd (Or.inl ⟨s, h₁, by omega, e.symm⟩) (hY hy).2
      have hmissB : ∀ t ≤ n, ∀ s, g ≤ s → s ≤ j → q t = B s → t = n ∧ s = g := by
        intro t ht s h₁ h₂ e
        rcases hq.mem t ht with hx | hy
        · exact absurd (Or.inl ⟨s, Nat.zero_le _, by omega, e.symm⟩) (hX hx).2
        · have hsg : s = g := by
            by_contra hne'
            exact (hY hy).2 (Or.inr ⟨s, by omega, by omega, e.symm⟩)
          subst hsg
          exact ⟨hq.inj t ht n le_rfl (by rw [e, hqn]), rfl⟩
      have h₁ := IsPath.append (D := D) (K := L) (u := fun t => A (h + t)) (w := q) hsA hqL
        (by simp only [show h + (i - h) = i by omega]; exact hq0.symm)
        (by
          intro s hs t ht e
          have := hmissA t ht (h + s) (by omega) (by omega) e.symm
          exact ⟨by omega, this.1⟩)
      have h₂ := IsPath.append (D := D) (K := L) (w := fun t => B (g + t)) h₁ hsB
        (by
          by_cases hn0 : n = 0
          · subst hn0
            simp only [Nat.add_zero, le_refl, ite_true, show h + (i - h) = i by omega]
            simpa using hq0.symm.trans hqn
          · have h₄ : ¬ i - h + n ≤ i - h := by omega
            simp only [h₄, ite_false, show i - h + n - (i - h) = n by omega, Nat.add_zero]
            exact hqn)
        (by
          intro s hs t ht e
          by_cases h₃ : s ≤ i - h
          · simp only [h₃, ite_true] at e
            exact absurd e (hd _ (by omega) _ (by omega))
          · simp only [h₃, ite_false] at e
            have := hmissB (s - (i - h)) (by omega) (g + t) (by omega) (by omega) e
            exact ⟨by omega, by omega⟩)
      refine ⟨_, _, h₂, ?_⟩
      intro hheavy
      refine hQ (HasHeavy.anti ?_ hheavy)
      rintro w' (⟨t, h₃, h₄, rfl⟩ | ⟨t, h₃, h₄, rfl⟩)
      · refine ⟨t - h, Nat.zero_le _, by omega, ?_⟩
        have h₅ : t - h ≤ i - h + n := by omega
        have h₆ : t - h ≤ i - h := by omega
        simp [h₅, h₆, show h + (t - h) = t by omega]
      · refine ⟨i - h + n + (t - g), Nat.zero_le _, by omega, ?_⟩
        by_cases h₅ : t = g
        · subst h₅
          have h₆ : i - h + n + (t - t) = i - h + n := by omega
          rw [h₆]
          by_cases hn0 : n = 0
          · subst hn0
            have hq' : q 0 = B t := hqn
            simp [show h + (i - h) = i by omega, ← hq', hq0]
          · have h₇ : i - h + n ≤ i - h + n := le_rfl
            have h₈ : ¬ i - h + n ≤ i - h := by omega
            simp [h₈, show i - h + n - (i - h) = n by omega, hqn]
        · have h₆ : ¬ i - h + n + (t - g) ≤ i - h + n := by omega
          simp [h₆, show i - h + n + (t - g) - (i - h + n) = t - g by omega, show g + (t - g) = t by omega]
    · -- the segment of `A` alone is enough
      refine ⟨i - h, _, IsPath.slice hA hhi hia, ?_⟩
      intro hheavy
      refine ha0 (HasHeavy.anti ?_ hheavy)
      rintro _ ⟨t, h₁, h₂, rfl⟩
      exact ⟨t - h, Nat.zero_le _, by omega, by simp [show h + (t - h) = t by omega]⟩
  · exact ⟨b, B, hB, hb0⟩

/-- **Lemma 3.** -/
theorem cycle_lemma {a b : ℕ} {A B : ℕ → V} (hA : IsPath D L a A) (hB : IsPath D L b B)
    (hd : ∀ i ≤ a, ∀ j ≤ b, A i ≠ B j) (hL : Strong D L) (hne : 0 < L.ncard)
    (hall : ¬ HasHeavy D L (seg A 0 (a + 1) ∪ seg B 0 (b + 1))) :
    ∃ n c, IsPath D L n c ∧ (n = 0 ∨ D (c n) (c 0)) ∧ ¬ HasHeavy D L {w | ∃ t ≤ n, c t = w} := by
  obtain ⟨m, U, hU, hUn⟩ := join hA hB hd hall
  exact close hU hL hne hUn

end Cycle

/-! ## The last claim of Lemma 5 -/

section Piece

variable [Finite V] {S : Split V} {W : ℕ}

/-- **Lemma 5(b), the size.** Let `L` be the component of the end of the path, `C` a set on the path that leaves no heavy set
in `L`. A strongly connected set of a bad class that holds a vertex with more than `7W/8` reached has at most `3/4` of `L`. -/
theorem pass_piece (hQ : S.K.ncard ≤ W) (hhi : 7 * W < 8 * f S.D S.K (S.v S.k))
    (hL : ∀ y ∈ S.K, Reach S.D S.K (S.v S.k) y → ¬ Reach S.D S.K y (S.v S.k) → 8 * f S.D S.K y ≤ 7 * W)
    {z v : V} (hz : S.IsHead z) (hbad : 15 * W < 16 * (S.cls z).ncard)
    {C : Set V} (hC : ∀ y ∈ C, S.OnPath y)
    (hnh : ¬ HasHeavy S.D {y | y ∈ S.K ∧ Reach S.D S.K (S.v S.k) y ∧ Reach S.D S.K y (S.v S.k)} C)
    {T : Set V} (hT : T ⊆ S.cls z) (hs : Strong S.D T) (hv : v ∈ T)
    (hvh : 7 * W < 8 * f S.D (S.cls z) v) :
    4 * T.ncard ≤ 3 * ({y | y ∈ S.K ∧ Reach S.D S.K (S.v S.k) y ∧ Reach S.D S.K y (S.v S.k)} : Set V).ncard := by
  obtain ⟨h₁, h₂⟩ := pass_b hQ hhi hL hz hbad (hT hv) hvh
  have hTK : T ⊆ S.K := fun _ hx => (hT hx).1.1
  by_contra hc
  refine hnh ⟨T, fun w hw => ⟨⟨hTK hw, ?_, ?_⟩, ?_⟩, hs, by omega⟩
  · exact h₁.trans (reach_mono hTK (hs v hv w hw))
  · exact (reach_mono hTK (hs w hw v hv)).trans h₂
  · exact fun hwC => (hT hw).1.2 (hC w hwC)

end Piece

end PlanarMatching.GeneralSearch
