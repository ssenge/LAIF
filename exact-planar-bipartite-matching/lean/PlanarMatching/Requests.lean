import Mathlib.Order.Basic
import Mathlib.Data.Set.Basic

/-!
# Disjoint intervals

`notes/MATCHING.md`, Lemma A and Lemma C. `R c` is reachability inside the child `c` of a bag `Y`, and `RY`
is reachability in `Y`. A path of `J` is a sequence `y 0, …, y k`, whose arc `i` is realized in the child
`lbl i`. All that is used of a least-hop path is `NoShortcut`, and `noShortcut_of_least` derives it.
-/

namespace PlanarMatching

variable {V C : Type*}

/-- The interval of a request, for a reachability relation. -/
def Interval (R : V → V → Prop) (u v : V) : Set V := {x | R u x ∧ R x v}

/-- A path of `J` from `u` to `v` with `k` hops, on the node set `N`. -/
structure JPath (N : Set V) (R : C → V → V → Prop) (u v : V) (k : ℕ) (y : ℕ → V) : Prop where
  start : y 0 = u
  stop : y k = v
  mem : ∀ i ≤ k, y i ∈ N
  arc : ∀ i < k, ∃ c, R c (y i) (y (i + 1))

/-- No arc of `J` jumps over a node of the path. -/
def NoShortcut (R : C → V → V → Prop) (k : ℕ) (y : ℕ → V) : Prop :=
  ∀ a b, a + 1 < b → b ≤ k → ∀ c, ¬ R c (y a) (y b)

/-- A least-hop path has no shortcut. -/
theorem noShortcut_of_least {N : Set V} {R : C → V → V → Prop} {u v : V} {k : ℕ} {y : ℕ → V}
    (hP : JPath N R u v k y)
    (hmin : ∀ k' y', JPath N R u v k' y' → k ≤ k') : NoShortcut R k y := by
  intro a b hab hb c hR
  let y' : ℕ → V := fun i => if i ≤ a then y i else y (i + (b - a - 1))
  have hP' : JPath N R u v (k - (b - a - 1)) y' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [y', hP.start]
    · have hk : k - (b - a - 1) > a := by omega
      have : ¬ (k - (b - a - 1) ≤ a) := by omega
      simp only [y', this, ite_false]
      have e : k - (b - a - 1) + (b - a - 1) = k := by omega
      rw [e, hP.stop]
    · intro i hi
      by_cases h : i ≤ a
      · simp only [y', h, ite_true]
        exact hP.mem i (by omega)
      · simp only [y', h, ite_false]
        exact hP.mem _ (by omega)
    · intro i hi
      by_cases h : i < a
      · have h1 : i ≤ a := by omega
        have h2 : i + 1 ≤ a := by omega
        simp only [y', h1, h2, ite_true]
        exact hP.arc i (by omega)
      · by_cases h' : i = a
        · subst h'
          have h3 : ¬ (i + 1 ≤ i) := by omega
          simp only [y', le_refl, ite_true, h3, ite_false]
          have e : i + 1 + (b - i - 1) = b := by omega
          rw [e]
          exact ⟨c, hR⟩
        · have h1 : ¬ (i ≤ a) := by omega
          have h2 : ¬ (i + 1 ≤ a) := by omega
          simp only [y', h1, h2, ite_false]
          have e : i + 1 + (b - a - 1) = i + (b - a - 1) + 1 := by omega
          rw [e]
          exact hP.arc _ (by omega)
  have := hmin _ _ hP'
  omega

/-- Lemma A, same request: two segments of a path without shortcut in one child have disjoint intervals. -/
theorem segments_disjoint {R : C → V → V → Prop} (trans : ∀ c a b d, R c a b → R c b d → R c a d)
    {k : ℕ} {y : ℕ → V} (hS : NoShortcut R k y) {a b : ℕ} (hab : a < b) (hb : b < k) (c : C) (x : V)
    (h1 : x ∈ Interval (R c) (y a) (y (a + 1))) (h2 : x ∈ Interval (R c) (y b) (y (b + 1))) : False :=
  hS a (b + 1) (by omega) (by omega) c (trans c _ _ _ h1.1 h2.2)

/-- Lemma A, different requests: the interval of a segment lies in the interval of its request. -/
theorem segment_sub_request {R : C → V → V → Prop} {RY : V → V → Prop}
    (mono : ∀ c a b, R c a b → RY a b) (transY : ∀ a b d, RY a b → RY b d → RY a d)
    {u v : V} {i : ℕ} {y : ℕ → V} (hu : RY u (y i)) (hv : RY (y (i + 1)) v) (c : C) :
    Interval (R c) (y i) (y (i + 1)) ⊆ Interval RY u v := fun _ hx =>
  ⟨transY _ _ _ hu (mono _ _ _ hx.1), transY _ _ _ (mono _ _ _ hx.2) hv⟩

/-- A node of a path reaches, and is reached from, the ends. -/
theorem path_reach {N : Set V} {R : C → V → V → Prop} {RY : V → V → Prop} {u v : V} {k : ℕ} {y : ℕ → V}
    (hP : JPath N R u v k y) (mono : ∀ c a b, R c a b → RY a b) (reflY : ∀ a, RY a a)
    (transY : ∀ a b d, RY a b → RY b d → RY a d) :
    (∀ i ≤ k, RY u (y i)) ∧ (∀ i ≤ k, RY (y i) v) := by
  constructor
  · intro i
    induction i with
    | zero => intro _; rw [hP.start]; exact reflY _
    | succ i ih =>
      intro hi
      obtain ⟨c, hc⟩ := hP.arc i (by omega)
      exact transY _ _ _ (ih (by omega)) (mono _ _ _ hc)
  · have key : ∀ m i, i + m = k → RY (y i) v := by
      intro m
      induction m with
      | zero => intro i hi; rw [show i = k by omega, hP.stop]; exact reflY _
      | succ m ih =>
        intro i hi
        obtain ⟨c, hc⟩ := hP.arc i (by omega)
        exact transY _ _ _ (mono _ _ _ hc) (ih (i + 1) (by omega))
    intro i hi
    exact key (k - i) i (by omega)

/-- Lemma A: a family of disjoint requests in `Y` gives disjoint segments in each child. -/
theorem lemmaA {ι : Type*} {N : ι → Set V} {R : C → V → V → Prop} {RY : V → V → Prop}
    (trans : ∀ c a b d, R c a b → R c b d → R c a d)
    (mono : ∀ c a b, R c a b → RY a b) (reflY : ∀ a, RY a a)
    (transY : ∀ a b d, RY a b → RY b d → RY a d)
    {u v : ι → V} {k : ι → ℕ} {y : ι → ℕ → V}
    (hP : ∀ r, JPath (N r) R (u r) (v r) (k r) (y r))
    (hS : ∀ r, NoShortcut R (k r) (y r))
    (hdisj : ∀ r r', r ≠ r' → ∀ x, x ∈ Interval RY (u r) (v r) → x ∉ Interval RY (u r') (v r'))
    {r r' : ι} {i i' : ℕ} (hi : i < k r) (hi' : i' < k r') (hne : (r, i) ≠ (r', i')) (c : C) (x : V)
    (h1 : x ∈ Interval (R c) (y r i) (y r (i + 1)))
    (h2 : x ∈ Interval (R c) (y r' i') (y r' (i' + 1))) : False := by
  by_cases hrr : r = r'
  · subst hrr
    have hii : i ≠ i' := fun e => hne (by rw [e])
    rcases lt_or_gt_of_ne hii with h | h
    · exact segments_disjoint trans (hS r) h hi' c x h1 h2
    · exact segments_disjoint trans (hS r) h hi c x h2 h1
  · have reach := fun s => path_reach (hP s) mono reflY transY
    have a1 := segment_sub_request (R := R) mono transY ((reach r).1 i (by omega)) ((reach r).2 (i + 1) (by omega)) c h1
    have a2 := segment_sub_request (R := R) mono transY ((reach r').1 i' (by omega)) ((reach r').2 (i' + 1) (by omega)) c h2
    exact hdisj r r' hrr x a1 a2

/-- Lemma C: if two segments of one request share a vertex, it lies on two children, so on the separator. -/
theorem lemmaC {R : C → V → V → Prop} (trans : ∀ c a b d, R c a b → R c b d → R c a d)
    {inBag : C → V → Prop} (mem : ∀ c a b, R c a b → inBag c a)
    {sep : Set V} (uniq : ∀ x, x ∉ sep → ∀ c c', inBag c x → inBag c' x → c = c')
    {k : ℕ} {y : ℕ → V} {lbl : ℕ → C} (hS : NoShortcut R k y)
    {a b : ℕ} (hab : a < b) (hb : b < k) (x : V)
    (h1 : x ∈ Interval (R (lbl a)) (y a) (y (a + 1))) (h2 : x ∈ Interval (R (lbl b)) (y b) (y (b + 1))) :
    x ∈ sep := by
  by_contra hx
  have e := uniq x hx _ _ (mem _ _ _ h1.2) (mem _ _ _ h2.2)
  rw [← e] at h2
  exact segments_disjoint trans hS hab hb _ x h1 h2

end PlanarMatching
