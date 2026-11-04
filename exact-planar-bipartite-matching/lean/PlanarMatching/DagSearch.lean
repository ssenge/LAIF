import Mathlib.Logic.Relation
import Mathlib.Order.WellFounded
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Find

/-!
# The Split Lemma and the blocks

`notes/DAG_DFS.md`, Section 3, and Fact 1 of its Section 2, on any digraph. `Split` is the setting of Section 3.
`lemma1a_partition`, `lemma1a_head_mem` and `lemma1a_reach` are Lemma 1(a), `lemma1b` is Lemma 1(b), `lemma1c` is
Lemma 1(c). `lemma2a` and `lemma2a_part` are Lemma 2(a), and `lemma2b_exists`, `lemma2b_path`, `lemma2b_strong` and
`lemma2b_dag` are Lemma 2(b). `left_isPath` is the remark after Lemma 2. `fact1` is Fact 1.

An ordered tree is given by addresses: `addr y` lists the child indices on the way from the root to `y`. So `a` is an
ancestor of `b` when `addr a` is a prefix of `addr b`, and `b` is right of `a` when `IsRight (addr a) (addr b)`, that is,
`addr a` is lexicographically below `addr b` and is not a prefix of it. Child indices may have gaps, since only their
order counts. The addresses of Lemma 1(c) leave index `0` unused below the last vertex of `π` in any case.

The note defines "right of" by `pre(b) > pre(a)` and `post(b) > post(a)`. On addresses pre-order is the lexicographic
order and post-order is `PostLt`, so `isRight_iff_pre_post` is the agreement of the two definitions. `Run.isRight_iff`
proves it again with the numbers that a real search assigns, and `Run.pre_sorted` and `Run.post_sorted` are the reason
that pre-order and post-order are these orders.
-/

namespace PlanarMatching.DagSearch

open Relation

/-! ## Addresses -/

/-- `IsRight l m`: the address `m` lies right of the address `l`. -/
def IsRight (l m : List ℕ) : Prop := l < m ∧ ¬ l <+: m

instance : DecidableRel IsRight := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

example : IsRight [0, 7] [1] := by decide
example : IsRight [2, 0] [2, 1, 5] := by decide
example : ¬ IsRight [2] [2, 1] := by decide
example : ¬ IsRight [2, 1] [2] := by decide
example : ¬ IsRight [1] [0, 7] := by decide
example : ¬ IsRight [1] [1] := by decide

/-- The order of post-order on addresses: a vertex comes after its descendants and after what is left of it. -/
def PostLt (l m : List ℕ) : Prop := IsRight l m ∨ (m <+: l ∧ m ≠ l)

theorem append_lt_append_iff (c l m : List ℕ) : c ++ l < c ++ m ↔ l < m := by
  induction c with
  | nil => rfl
  | cons a c ih => simp [ih]

/-- `T` and `τ` agree on "right of" below a common prefix. -/
theorem isRight_append (c l m : List ℕ) : IsRight (c ++ l) (c ++ m) ↔ IsRight l m := by
  simp [IsRight, List.prefix_append_right_inj]

theorem isRight_cons (a : ℕ) (l m : List ℕ) : IsRight (a :: l) (a :: m) ↔ IsRight l m :=
  isRight_append [a] l m

theorem IsRight.of_lt_of_append {c l m : List ℕ} {d e : ℕ} (h : d < e) :
    IsRight (c ++ d :: l) (c ++ e :: m) := by
  rw [isRight_append]
  refine ⟨by simp [List.cons_lt_cons_iff, h], fun hp => ?_⟩
  rw [List.cons_prefix_cons] at hp
  omega

theorem IsRight.exists {l m : List ℕ} (h : IsRight l m) :
    ∃ c d e r s, d < e ∧ l = c ++ d :: r ∧ m = c ++ e :: s := by
  obtain ⟨h₁, h₂⟩ := h
  induction l generalizing m with
  | nil => exact absurd List.nil_prefix h₂
  | cons a l ih =>
    cases m with
    | nil => exact absurd h₁ (List.not_lt_nil _)
    | cons b m =>
      rcases List.cons_lt_cons_iff.1 h₁ with hab | ⟨rfl, hlm⟩
      · exact ⟨[], a, b, l, m, hab, rfl, rfl⟩
      · have hnp : ¬ l <+: m := fun hp => h₂ ((List.cons_prefix_cons).2 ⟨rfl, hp⟩)
        obtain ⟨c, d, e, r, s, hde, rfl, rfl⟩ := ih hlm hnp
        exact ⟨a :: c, d, e, r, s, hde, rfl, rfl⟩

/-- Extensions of addresses stay right of each other. -/
theorem IsRight.extend {l m l' m' : List ℕ} (h : IsRight l m) (hl : l <+: l') (hm : m <+: m') :
    IsRight l' m' := by
  obtain ⟨c, d, e, r, s, hde, rfl, rfl⟩ := h.exists
  obtain ⟨t, rfl⟩ := hl
  obtain ⟨t', rfl⟩ := hm
  simpa using IsRight.of_lt_of_append (c := c) (l := r ++ t) (m := s ++ t') hde

theorem lt_of_prefix_of_ne {l m : List ℕ} (h : l <+: m) (hne : l ≠ m) : l < m := by
  obtain ⟨t, rfl⟩ := h
  cases t with
  | nil => simp at hne
  | cons a t =>
    have := (append_lt_append_iff l [] (a :: t)).2 (List.nil_lt_cons a t)
    simpa using this

theorem not_isRight_of_prefix {l m : List ℕ} (h : l <+: m) : ¬ IsRight l m := fun hr => hr.2 h

theorem not_isRight_of_prefix' {l m : List ℕ} (h : m <+: l) : ¬ IsRight l m := fun hr => by
  by_cases e : m = l
  · subst e
    exact lt_irrefl _ hr.1
  · exact lt_asymm hr.1 (lt_of_prefix_of_ne h e)

theorem not_isRight_of_lt {l m : List ℕ} (h : m < l) : ¬ IsRight l m :=
  fun hr => lt_asymm hr.1 h

/-- `pre(b) > pre(a)` and `post(b) > post(a)` of the note, on addresses. -/
theorem isRight_iff_pre_post (l m : List ℕ) : IsRight l m ↔ l < m ∧ PostLt l m := by
  constructor
  · exact fun h => ⟨h.1, Or.inl h⟩
  · rintro ⟨h, hr | ⟨hp, hne⟩⟩
    · exact hr
    · exact absurd h (lt_asymm (lt_of_prefix_of_ne hp hne))

theorem PostLt.asymm {l m : List ℕ} (h : PostLt l m) : ¬ PostLt m l := by
  rintro (h' | ⟨h', hne'⟩)
  · rcases h with h | ⟨h, hne⟩
    · exact lt_asymm h.1 h'.1
    · exact h'.2 h
  · rcases h with h | ⟨h, hne⟩
    · exact h.2 h'
    · exact hne (List.IsPrefix.eq_of_length_le h (h'.length_le))

theorem PostLt.irrefl (l : List ℕ) : ¬ PostLt l l := fun h => h.asymm h

/-- The address of a vertex with no arc to its right, against the address of a head. -/
theorem le_or_prefix_of_not_isRight {l m : List ℕ} (h : ¬ IsRight l m) : m ≤ l ∨ l <+: m := by
  by_cases hp : l <+: m
  · exact Or.inr hp
  · exact Or.inl (not_lt.1 fun hlt => h ⟨hlt, hp⟩)

theorem prefix_append_cases {l c m : List ℕ} (h : l <+: c ++ m) : l <+: c ∨ ∃ t, l = c ++ t ∧ t <+: m := by
  induction c generalizing l with
  | nil => exact Or.inr ⟨l, rfl, h⟩
  | cons a c ih =>
    rcases List.prefix_cons_iff.1 h with rfl | ⟨t, rfl, ht⟩
    · exact Or.inl List.nil_prefix
    · rcases ih ht with h' | ⟨s, rfl, hs⟩
      · exact Or.inl ((List.cons_prefix_cons).2 ⟨rfl, h'⟩)
      · exact Or.inr ⟨s, rfl, hs⟩

/-! ### Runs of zeros -/

/-- A run of zeros against a run of zeros with a positive entry after it. -/
theorem zeros_lt (j i r : ℕ) (t : List ℕ) :
    List.replicate j 0 < List.replicate i 0 ++ (r + 1) :: t := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => exact List.nil_lt_cons _ _
    | succ j => simp [List.replicate_succ, List.cons_lt_cons_iff]
  | succ i ih =>
    cases j with
    | zero => simp [List.replicate_succ]
    | succ j => simpa [List.replicate_succ, List.cons_lt_cons_iff] using ih j

theorem zeros_append_lt {i j : ℕ} (h : i < j) (r : ℕ) (t t' : List ℕ) :
    List.replicate j 0 ++ t' < List.replicate i 0 ++ (r + 1) :: t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
  have e : List.replicate (i + d + 1) 0 ++ t' = List.replicate i 0 ++ 0 :: (List.replicate d 0 ++ t') := by
    rw [Nat.add_assoc, List.replicate_add, List.replicate_succ]
    simp
  rw [e, append_lt_append_iff]
  simp [List.cons_lt_cons_iff]

theorem zeros_ne (j i r : ℕ) (t : List ℕ) :
    List.replicate j 0 ≠ List.replicate i 0 ++ (r + 1) :: t := (zeros_lt j i r t).ne

theorem zeros_prefix {i j : ℕ} (h : i ≤ j) (t : List ℕ) :
    List.replicate i 0 <+: List.replicate j 0 ++ t := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.replicate_add, List.append_assoc]
  exact List.prefix_append _ _

theorem prefix_zeros {l : List ℕ} {i : ℕ} (h : l <+: List.replicate i 0) :
    ∃ j ≤ i, l = List.replicate j 0 := by
  refine ⟨l.length, by simpa using h.length_le, ?_⟩
  rw [List.eq_replicate_iff]
  exact ⟨rfl, fun b hb => List.eq_of_mem_replicate (h.subset hb)⟩

theorem zeros_eq {d d' r r' : ℕ} {t t' : List ℕ}
    (h : List.replicate d 0 ++ (r + 1) :: t = List.replicate d' 0 ++ (r' + 1) :: t') :
    d = d' ∧ r = r' ∧ t = t' := by
  induction d generalizing d' with
  | zero =>
    cases d' with
    | zero => simpa using h
    | succ d' => simp [List.replicate_succ] at h
  | succ d ih =>
    cases d' with
    | zero => simp [List.replicate_succ] at h
    | succ d' =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl, rfl⟩

theorem zeros_eq_concat {d j r c : ℕ} {t : List ℕ}
    (h : List.replicate d 0 ++ (r + 1) :: t = List.replicate j 0 ++ [c]) : d = j ∧ t = [] := by
  rcases List.eq_nil_or_concat t with rfl | ⟨t', c', rfl⟩
  · have := (List.append_inj' h (by simp)).1
    simpa using this
  · exfalso
    rw [List.concat_eq_append] at h
    have e : List.replicate d 0 ++ (r + 1) :: (t' ++ [c']) =
        (List.replicate d 0 ++ (r + 1) :: t') ++ [c'] := by simp
    rw [e] at h
    exact zeros_ne j d r t' (List.append_inj' h (by simp)).1.symm

/-! ## Paths, reachability, search trees -/

variable {V : Type*}

/-- The arcs of `D[R]`. -/
def Induced (D : V → V → Prop) (R : Set V) (a b : V) : Prop := D a b ∧ a ∈ R ∧ b ∈ R

/-- Reachability in `D[R]`. It is reflexive, so use it from a start in `R`. -/
abbrev Reach (D : V → V → Prop) (R : Set V) : V → V → Prop := ReflTransGen (Induced D R)

theorem Reach.mem {D : V → V → Prop} {R : Set V} {a b : V} (h : Reach D R a b) (ha : a ∈ R) : b ∈ R := by
  induction h with
  | refl => exact ha
  | tail _ h _ => exact h.2.2

theorem Reach.toD {D : V → V → Prop} {R : Set V} {a b : V} (h : Reach D R a b) : ReflTransGen D a b := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ h ih => exact ih.tail h.1

/-- A path in `D[K]`, simple, with vertices `v 0, ..., v k`. -/
structure IsPath (D : V → V → Prop) (K : Set V) (k : ℕ) (v : ℕ → V) : Prop where
  mem : ∀ i ≤ k, v i ∈ K
  inj : ∀ i ≤ k, ∀ j ≤ k, v i = v j → i = j
  arc : ∀ i < k, D (v i) (v (i + 1))

theorem IsPath.reach {D : V → V → Prop} {K : Set V} {k : ℕ} {v : ℕ → V} (h : IsPath D K k v) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ k) : Reach D K (v i) (v j) := by
  induction j, hij using Nat.le_induction with
  | base => exact ReflTransGen.refl
  | succ j _ ih =>
    exact (ih (by omega)).tail ⟨h.arc j (by omega), h.mem j (by omega), h.mem (j + 1) hj⟩

/-- A walk in `D[K]` contains a simple path with the same ends. -/
theorem exists_path {D : V → V → Prop} {K : Set V} {a b : V} (h : Reach D K a b) (ha : a ∈ K) :
    ∃ n w, IsPath D K n w ∧ w 0 = a ∧ w n = b := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun _ => b, ⟨fun _ _ => ha, fun i hi j hj _ => by omega, fun i hi => by omega⟩, rfl, rfl⟩
  | @head a c h' _ ih =>
    obtain ⟨n, w, hw, h0, hn⟩ := ih h'.2.2
    by_cases hin : ∃ p ≤ n, w p = a
    · obtain ⟨p, hp, rfl⟩ := hin
      refine ⟨n - p, fun i => w (p + i), ⟨fun i hi => hw.mem _ (by omega), fun i hi j hj e => ?_,
        fun i hi => hw.arc _ (by omega)⟩, rfl, ?_⟩
      · have := hw.inj _ (by omega) _ (by omega) e
        omega
      · simpa [Nat.add_sub_cancel' hp] using hn
    · refine ⟨n + 1, fun i => Nat.casesOn i a w, ⟨fun i hi => ?_, fun i hi j hj e => ?_, fun i hi => ?_⟩,
        rfl, hn⟩
      · cases i with
        | zero => exact ha
        | succ i => exact hw.mem i (by omega)
      · cases i with
        | zero =>
          cases j with
          | zero => rfl
          | succ j => exact absurd ⟨j, by omega, e.symm⟩ hin
        | succ i =>
          cases j with
          | zero => exact absurd ⟨i, by omega, e⟩ hin
          | succ j => exact congrArg (· + 1) (hw.inj i (by omega) j (by omega) e)
      · cases i with
        | zero => simpa [h0] using h'.1
        | succ i => exact hw.arc i (by omega)

/-- The first time a walk meets the set `A`. -/
theorem first_entry {D : V → V → Prop} {K A : Set V} {u t : V} (h : Reach D K u t) (hu : u ∉ A) (ht : t ∈ A) :
    ∃ w t', Reach D (K \ A) u w ∧ D w t' ∧ t' ∈ A ∧ Reach D K t' t := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact absurd ht hu
  | @head a c h' hr ih =>
    by_cases hc : c ∈ A
    · exact ⟨a, c, ReflTransGen.refl, h'.1, hc, hr⟩
    · obtain ⟨w, t', h₁, h₂, h₃, h₄⟩ := ih hc
      exact ⟨w, t', ReflTransGen.head ⟨h'.1, ⟨h'.2.1, hu⟩, ⟨h'.2.2, hc⟩⟩ h₁, h₂, h₃, h₄⟩

/-- A search tree of `D[K]` from `x`, by addresses. -/
structure IsSearchTree (D : V → V → Prop) (K : Set V) (x : V) (addr : V → List ℕ) : Prop where
  root_mem : x ∈ K
  root : addr x = []
  inj : Set.InjOn addr K
  prefix_closed : ∀ y ∈ K, ∀ l, l <+: addr y → ∃ w ∈ K, addr w = l
  /-- The vertex at the parent address of `y` has an arc to `y`. -/
  parent : ∀ w ∈ K, ∀ y ∈ K, ∀ c, addr y = addr w ++ [c] → D w y
  /-- No arc of `D[K]` goes to a vertex right of its tail. -/
  no_right : ∀ a ∈ K, ∀ b ∈ K, D a b → ¬ IsRight (addr a) (addr b)

/-- The setting of Section 3: `D`, identifiers, the set `K` with every vertex reached from `x = v 0` in `D[K]`, and
the path `π = (v 0, ..., v k)` in `D[K]`. -/
structure Split (V : Type*) where
  D : V → V → Prop
  id : V → ℕ
  id_inj : Function.Injective id
  K : Set V
  k : ℕ
  v : ℕ → V
  path : IsPath D K k v
  reached : ∀ y ∈ K, Reach D K (v 0) y

namespace Split

variable (S : Split V)

/-- The vertex `y` lies on `π`. -/
def OnPath (y : V) : Prop := ∃ i ≤ S.k, S.v i = y

/-- `R = K ∖ V(π)`. -/
def R : Set V := {y | y ∈ S.K ∧ ¬ S.OnPath y}

/-- A vertex of `R` with an arc from `π`. -/
def IsHead (z : V) : Prop := z ∈ S.R ∧ ∃ i ≤ S.k, S.D (S.v i) z

/-- The key `(k − i, id z)` of the arc `(v i, z)`, ordered lexicographically. -/
def arcKey (i : ℕ) (z : V) : ℕ ×ₗ ℕ := toLex (S.k - i, S.id z)

open Classical in
/-- The index of `p(z)`: the deepest vertex of `π` with an arc to `z`. -/
noncomputable def depth (z : V) : ℕ := Nat.findGreatest (fun i => S.D (S.v i) z) S.k

/-- The key of a head. -/
noncomputable def key (z : V) : ℕ ×ₗ ℕ := S.arcKey (S.depth z) z

/-- The tail of the arc that gives `z` its key. -/
noncomputable def p (z : V) : V := S.v (S.depth z)

variable {S}

theorem depth_le (z : V) : S.depth z ≤ S.k := by
  classical
  unfold depth
  exact Nat.findGreatest_le _

theorem le_depth {z : V} {i : ℕ} (hi : i ≤ S.k) (h : S.D (S.v i) z) : i ≤ S.depth z := by
  classical
  unfold depth
  exact Nat.le_findGreatest hi h

theorem p_arc {z : V} (hz : S.IsHead z) : S.D (S.p z) z := by
  classical
  obtain ⟨-, i, hi, h⟩ := hz
  unfold p depth
  exact Nat.findGreatest_spec (P := fun i => S.D (S.v i) z) hi h

/-- The key of a head is the least key among the arcs it receives, and its tail is `p(z)`. -/
theorem key_isLeast {z : V} (hz : S.IsHead z) :
    IsLeast {κ | ∃ i ≤ S.k, S.D (S.v i) z ∧ κ = S.arcKey i z} (S.key z) := by
  refine ⟨⟨S.depth z, depth_le z, p_arc hz, rfl⟩, ?_⟩
  rintro _ ⟨i, hi, h, rfl⟩
  have h₁ := le_depth hi h
  have h₂ := depth_le (S := S) z
  simp only [key, arcKey, Prod.Lex.toLex_le_toLex]
  rcases h₁.lt_or_eq with h₃ | h₃
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, le_rfl⟩

theorem key_inj {a b : V} (h : S.key a = S.key b) : a = b := by
  have : S.id a = S.id b := by
    simpa [key, arcKey] using congrArg (fun κ => (ofLex κ).2) h
  exact S.id_inj this

variable (S)

/-- The heads that reach `y` in `D[R]`. -/
def reachers (y : V) : Set V := {z | S.IsHead z ∧ Reach S.D S.R z y}

variable {S}

/-- The first step of Lemma 1(a): each `y` in `R` has a head that reaches it. -/
theorem reachers_nonempty {y : V} (hy : y ∈ S.R) : (S.reachers y).Nonempty := by
  have key : ∀ w, Reach S.D S.K (S.v 0) w → S.OnPath w ∨ (S.reachers w).Nonempty := by
    intro w hw
    induction hw with
    | refl => exact Or.inl ⟨0, Nat.zero_le _, rfl⟩
    | @tail c w' _ h ih =>
      by_cases hw' : S.OnPath w'
      · exact Or.inl hw'
      · refine Or.inr ?_
        have hw'R : w' ∈ S.R := ⟨h.2.2, hw'⟩
        rcases ih with ⟨i, hi, rfl⟩ | ⟨z, hz, hr⟩
        · exact ⟨w', ⟨hw'R, i, hi, h.1⟩, ReflTransGen.refl⟩
        · exact ⟨z, hz, hr.tail ⟨h.1, hr.mem hz.1, hw'R⟩⟩
  rcases key y (S.reached y hy.1) with h | h
  · exact absurd h hy.2
  · exact h

variable (S)

open Classical in
/-- A head of least key among those that reach `y`. -/
noncomputable def lead (y : V) : V :=
  if h : (S.reachers y).Nonempty then Function.argminOn S.key (S.reachers y) h else y

/-- `e(y)`: the least key of a head that reaches `y` in `D[R]`. -/
noncomputable def e (y : V) : ℕ ×ₗ ℕ := S.key (S.lead y)

/-- The class `K_z = {y : e(y) = key(z)}`. -/
def cls (z : V) : Set V := {y | y ∈ S.R ∧ S.e y = S.key z}

/-- A head that lies in its own class. These are the classes that count in the note. -/
def IsClassHead (z : V) : Prop := S.IsHead z ∧ z ∈ S.cls z

variable {S}

theorem lead_eq_argmin {y : V} (h : (S.reachers y).Nonempty) :
    S.lead y = Function.argminOn S.key (S.reachers y) h := by
  classical
  exact dite_eq_left h

theorem lead_mem {y : V} (hy : y ∈ S.R) : S.lead y ∈ S.reachers y := by
  rw [lead_eq_argmin (reachers_nonempty hy)]
  exact Function.argminOn_mem _ _ _

theorem e_le {y z : V} (hz : S.IsHead z) (h : Reach S.D S.R z y) : S.e y ≤ S.key z := by
  have hm : z ∈ S.reachers y := ⟨hz, h⟩
  rw [e, lead_eq_argmin ⟨z, hm⟩]
  exact Function.argminOn_le S.key _ hm

/-- `e(y)` is what the note says it is. -/
theorem e_isLeast {y : V} (hy : y ∈ S.R) : IsLeast (S.key '' S.reachers y) (S.e y) :=
  ⟨⟨_, lead_mem hy, rfl⟩, by rintro _ ⟨z, ⟨hz, hr⟩, rfl⟩; exact e_le hz hr⟩

/-- **Lemma 1(b).** An arc of `D[R]` does not raise `e`. -/
theorem lemma1b {y y' : V} (h : Induced S.D S.R y y') : S.e y' ≤ S.e y := by
  obtain ⟨hl, hr⟩ := lead_mem h.2.1
  exact e_le hl (hr.tail h)

/-- Keys do not rise along paths of `D[R]`. -/
theorem e_antitone {y y' : V} (h : Reach S.D S.R y y') : S.e y' ≤ S.e y := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact (lemma1b h).trans ih

/-- A path of `D[R]` between two vertices of a class stays in the class. -/
theorem reach_cls {u t z : V} (h : Reach S.D S.R u t) (hu : u ∈ S.cls z) (ht : t ∈ S.cls z) :
    Reach S.D (S.cls z) u t := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ReflTransGen.refl
  | @head a c h' hr ih =>
    have hc : c ∈ S.cls z := by
      refine ⟨h'.2.2, le_antisymm ?_ ?_⟩
      · exact (lemma1b h').trans hu.2.le
      · rw [← ht.2]
        exact e_antitone hr
    exact ReflTransGen.head ⟨h'.1, hu, hc⟩ (ih hc)

/-- If `y` lies in the class of a head `z`, then `z` is the lead of `y`. -/
theorem lead_eq {y z : V} (hy : y ∈ S.cls z) : S.lead y = z := key_inj hy.2

/-- **Lemma 1(a).** Each class of a head that holds a vertex holds its head. -/
theorem lemma1a_head_mem {y z : V} (hz : S.IsHead z) (hy : y ∈ S.cls z) : z ∈ S.cls z := by
  have hr : Reach S.D S.R z y := by
    have := (lead_mem hy.1).2
    rwa [lead_eq hy] at this
  refine ⟨hz.1, le_antisymm (e_le hz ReflTransGen.refl) ?_⟩
  rw [← hy.2]
  exact e_antitone hr

/-- A head out of its own class has an empty class. So "it counts only if `z` is in it" drops only empty sets. -/
theorem cls_eq_empty {z : V} (hz : S.IsHead z) (h : z ∉ S.cls z) : S.cls z = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hy => h (lemma1a_head_mem hz hy)

/-- The vertex `y` of `R` lies in the class of its lead, and that class counts. -/
theorem isClassHead_lead {y : V} (hy : y ∈ S.R) : S.IsClassHead (S.lead y) ∧ y ∈ S.cls (S.lead y) := by
  have hl := (lead_mem hy).1
  have hm : y ∈ S.cls (S.lead y) := ⟨hy, rfl⟩
  exact ⟨⟨hl, lemma1a_head_mem hl hm⟩, hm⟩

/-- **Lemma 1(a).** The classes partition `R`: each class lies in `R` by the definition of `cls`, and each vertex of `R`
lies in exactly one class that counts. -/
theorem lemma1a_partition {y : V} (hy : y ∈ S.R) : ∃! z, S.IsClassHead z ∧ y ∈ S.cls z :=
  ⟨S.lead y, isClassHead_lead hy, fun _ h => (lead_eq h.2).symm⟩

/-- **Lemma 1(a).** Each vertex of `K_z` is reached from `z` in `D[K_z]`. -/
theorem lemma1a_reach {y z : V} (hz : S.IsHead z) (hy : y ∈ S.cls z) : Reach S.D (S.cls z) z y := by
  have hr : Reach S.D S.R z y := by
    have := (lead_mem hy.1).2
    rwa [lead_eq hy] at this
  exact reach_cls hr (lemma1a_head_mem hz hy) hy

/-! ## Lemma 1(c) -/

variable (S)

/-- The class heads with the same `p` as `z` and a smaller identifier. -/
def earlier (z : V) : Set V := {z' | S.IsClassHead z' ∧ S.depth z' = S.depth z ∧ S.id z' < S.id z}

/-- The rank of `z` among the heads of `p(z)`, in the order of identifiers, which is the order of keys there. -/
noncomputable def rank (z : V) : ℕ := (S.earlier z).ncard

/-- The addresses of the tree of Lemma 1(c): `v i` gets `i` zeros, and `y` in the class of `z` gets
`(depth z zeros) ++ [rank z + 1] ++ T z y`. Off `K` the value means nothing. -/
noncomputable def addr (T : V → V → List ℕ) (y : V) : List ℕ := by
  classical
  exact if h : S.OnPath y then List.replicate (Classical.choose h) 0
    else List.replicate (S.depth (S.lead y)) 0 ++ (S.rank (S.lead y) + 1) :: T (S.lead y) y

variable {S}

theorem earlier_finite (z : V) : (S.earlier z).Finite := by
  refine ((Set.finite_lt_nat (S.id z)).preimage S.id_inj.injOn).subset ?_
  rintro z' ⟨-, -, h⟩
  exact h

theorem rank_lt {z z' : V} (hz' : S.IsClassHead z') (hd : S.depth z' = S.depth z) (hid : S.id z' < S.id z) :
    S.rank z' < S.rank z := by
  refine Set.ncard_lt_ncard ⟨?_, fun h => ?_⟩ (earlier_finite z)
  · rintro w ⟨hw, hwd, hwid⟩
    exact ⟨hw, hwd.trans hd, hwid.trans hid⟩
  · exact lt_irrefl _ (h (⟨hz', hd, hid⟩ : z' ∈ S.earlier z)).2.2

theorem rank_inj {z z' : V} (hz : S.IsClassHead z) (hz' : S.IsClassHead z') (hd : S.depth z = S.depth z')
    (hr : S.rank z = S.rank z') : z = z' := by
  rcases lt_trichotomy (S.id z) (S.id z') with h | h | h
  · exact absurd hr (rank_lt hz hd h).ne
  · exact S.id_inj h
  · exact absurd hr (rank_lt hz' hd.symm h).ne'

theorem addr_v (T : V → V → List ℕ) {i : ℕ} (hi : i ≤ S.k) : S.addr T (S.v i) = List.replicate i 0 := by
  classical
  have h : S.OnPath (S.v i) := ⟨i, hi, rfl⟩
  have hc := Classical.choose_spec h
  simp only [addr]
  rw [dite_eq_left h, S.path.inj _ hc.1 _ hi hc.2]

theorem addr_cls (T : V → V → List ℕ) {y z : V} (hy : y ∈ S.cls z) :
    S.addr T y = List.replicate (S.depth z) 0 ++ (S.rank z + 1) :: T z y := by
  classical
  have h : ¬ S.OnPath y := hy.1.2
  simp only [addr]
  rw [dite_eq_right h, lead_eq hy]

theorem mem_K_cases {y : V} (hy : y ∈ S.K) :
    (∃ i ≤ S.k, S.v i = y) ∨ ∃ z, S.IsClassHead z ∧ y ∈ S.cls z := by
  by_cases h : S.OnPath y
  · exact Or.inl h
  · exact Or.inr ⟨S.lead y, isClassHead_lead ⟨hy, h⟩⟩

section Compose

variable {T : V → V → List ℕ} (hT : ∀ z, S.IsClassHead z → IsSearchTree S.D (S.cls z) z (T z))
include hT

theorem addr_injOn : Set.InjOn (S.addr T) S.K := by
  intro a ha b hb hab
  rcases mem_K_cases ha with ⟨i, hi, rfl⟩ | ⟨z, hz, haz⟩ <;>
    rcases mem_K_cases hb with ⟨j, hj, rfl⟩ | ⟨z', hz', hbz⟩
  · rw [addr_v T hi, addr_v T hj] at hab
    have := congrArg List.length hab
    simp only [List.length_replicate] at this
    rw [this]
  · rw [addr_v T hi, addr_cls T hbz] at hab
    exact absurd hab (zeros_ne _ _ _ _)
  · rw [addr_cls T haz, addr_v T hj] at hab
    exact absurd hab.symm (zeros_ne _ _ _ _)
  · rw [addr_cls T haz, addr_cls T hbz] at hab
    obtain ⟨hd, hr, ht⟩ := zeros_eq hab
    obtain rfl := rank_inj hz hz' hd hr
    exact (hT z hz).inj haz hbz ht

theorem addr_prefix {y : V} (hy : y ∈ S.K) {l : List ℕ} (hl : l <+: S.addr T y) :
    ∃ w ∈ S.K, S.addr T w = l := by
  have onZeros : ∀ i ≤ S.k, l <+: List.replicate i 0 → ∃ w ∈ S.K, S.addr T w = l := by
    intro i hi hl'
    obtain ⟨j, hj, rfl⟩ := prefix_zeros hl'
    exact ⟨S.v j, S.path.mem j (hj.trans hi), addr_v T (hj.trans hi)⟩
  rcases mem_K_cases hy with ⟨i, hi, rfl⟩ | ⟨z, hz, hyz⟩
  · rw [addr_v T hi] at hl
    exact onZeros i hi hl
  · rw [addr_cls T hyz] at hl
    rcases prefix_append_cases hl with h | ⟨t, rfl, ht⟩
    · exact onZeros _ (depth_le z) h
    · rcases List.prefix_cons_iff.1 ht with rfl | ⟨t', rfl, ht'⟩
      · exact onZeros _ (depth_le z) (by simp)
      · obtain ⟨w, hw, rfl⟩ := (hT z hz).prefix_closed y hyz t' ht'
        exact ⟨w, hw.1.1, addr_cls T hw⟩

theorem addr_parent {w y : V} (hw : w ∈ S.K) (hy : y ∈ S.K) {c : ℕ} (h : S.addr T y = S.addr T w ++ [c]) :
    S.D w y := by
  rcases mem_K_cases hw with ⟨j, hj, rfl⟩ | ⟨z', hz', hwz⟩ <;>
    rcases mem_K_cases hy with ⟨i, hi, rfl⟩ | ⟨z, hz, hyz⟩
  · rw [addr_v T hi, addr_v T hj] at h
    have hl := congrArg List.length h
    simp only [List.length_replicate, List.length_append, List.length_cons, List.length_nil] at hl
    subst hl
    exact S.path.arc j (by omega)
  · rw [addr_cls T hyz, addr_v T hj] at h
    obtain ⟨rfl, ht⟩ := zeros_eq_concat h
    have hyzz : y = z := (hT z hz).inj hyz hz.2 (ht.trans (hT z hz).root.symm)
    subst hyzz
    exact p_arc hz.1
  · rw [addr_v T hi, addr_cls T hwz] at h
    rw [List.append_assoc, List.cons_append] at h
    exact absurd h (zeros_ne _ _ _ _)
  · rw [addr_cls T hyz, addr_cls T hwz, List.append_assoc, List.cons_append] at h
    obtain ⟨hd, hr, ht⟩ := zeros_eq h
    obtain rfl := rank_inj hz hz' hd hr
    exact (hT z hz).parent w hwz y hyz c ht

theorem addr_no_right {a b : V} (ha : a ∈ S.K) (hb : b ∈ S.K) (h : S.D a b) :
    ¬ IsRight (S.addr T a) (S.addr T b) := by
  rcases mem_K_cases ha with ⟨i, hi, rfl⟩ | ⟨z, hz, haz⟩ <;>
    rcases mem_K_cases hb with ⟨j, hj, rfl⟩ | ⟨z', hz', hbz⟩
  · -- both on `π`
    rw [addr_v T hi, addr_v T hj]
    rcases le_total i j with hij | hji
    · exact not_isRight_of_prefix (by simpa using zeros_prefix hij [])
    · exact not_isRight_of_prefix' (by simpa using zeros_prefix hji [])
  · -- from `π` to `R`: here the keys matter, for a head with several arcs from `π` and a head out of its class alike
    rw [addr_v T hi, addr_cls T hbz]
    have hbh : S.IsHead b := ⟨hbz.1, i, hi, h⟩
    have h₁ : S.key z' ≤ S.arcKey i b :=
      (hbz.2.symm.le.trans (e_le hbh ReflTransGen.refl)).trans ((key_isLeast hbh).2 ⟨i, hi, h, rfl⟩)
    have h₂ := depth_le (S := S) z'
    have h₃ : i ≤ S.depth z' := by
      simp only [key, arcKey, Prod.Lex.toLex_le_toLex] at h₁
      rcases h₁ with h₁ | ⟨h₁, -⟩ <;> omega
    exact not_isRight_of_prefix (zeros_prefix h₃ _)
  · -- from `R` to `π`
    rw [addr_cls T haz, addr_v T hj]
    exact not_isRight_of_lt (zeros_lt ..)
  · rw [addr_cls T haz, addr_cls T hbz]
    by_cases hzz : z' = z
    · -- in one class
      subst hzz
      rw [isRight_append, isRight_cons]
      exact (hT z' hz).no_right a haz b hbz h
    · -- between two classes: the subtree of `z'` comes wholly before the subtree of `z`
      have h₁ : S.e b ≤ S.e a := lemma1b ⟨h, haz.1, hbz.1⟩
      rw [haz.2, hbz.2] at h₁
      have h₂ : S.key z' < S.key z := lt_of_le_of_ne h₁ fun h' => hzz (key_inj h')
      have h₃ := depth_le (S := S) z
      have h₄ := depth_le (S := S) z'
      simp only [key, arcKey, Prod.Lex.toLex_lt_toLex] at h₂
      rcases h₂ with h₂ | ⟨h₂, h₅⟩
      · exact not_isRight_of_lt (zeros_append_lt (by omega) _ _ _)
      · have hd : S.depth z' = S.depth z := by omega
        rw [hd]
        refine not_isRight_of_lt ?_
        rw [append_lt_append_iff, List.cons_lt_cons_iff]
        exact Or.inl (by have := rank_lt hz' hd h₅; omega)

/-- **Lemma 1(c).** With a search tree `T z` of `D[K_z]` from `z` for each class, the composition is a search tree of
`D[K]` from `x`. -/
theorem lemma1c : IsSearchTree S.D S.K (S.v 0) (S.addr T) where
  root_mem := S.path.mem 0 (Nat.zero_le _)
  root := addr_v T (Nat.zero_le _)
  inj := addr_injOn hT
  prefix_closed _ hy _ hl := addr_prefix hT hy hl
  parent _ hw _ hy _ h := addr_parent hT hw hy h
  no_right _ ha _ hb h := addr_no_right hT ha hb h

end Compose

/-- A class head is the child of `p(z)` with index `rank z + 1`, and `rank_lt` says that these indices follow the
identifiers. Index `0` belongs to the next vertex of `π`, by `addr_v`. -/
theorem addr_head {T : V → V → List ℕ} {z : V} (hz : S.IsClassHead z) (h0 : T z z = []) :
    S.addr T z = S.addr T (S.p z) ++ [S.rank z + 1] := by
  rw [addr_cls T hz.2, h0, p, addr_v T (depth_le z)]

/-! ## Lemma 2 -/

section Blocks

variable {m a b k : ℕ} {s : ℕ → V} {z : V}

/-- **Lemma 2(a).** A class meets a path of `D[R]` in a contiguous part. -/
theorem lemma2a (hτ : IsPath S.D S.R m s) {i j l : ℕ} (hil : i ≤ l) (hlj : l ≤ j) (hj : j ≤ m)
    (hi : s i ∈ S.cls z) (hjc : s j ∈ S.cls z) : s l ∈ S.cls z := by
  refine ⟨hτ.mem l (hlj.trans hj), le_antisymm ?_ ?_⟩
  · exact (e_antitone (hτ.reach hil (hlj.trans hj))).trans hi.2.le
  · rw [← hjc.2]
    exact e_antitone (hτ.reach hlj hj)

/-- **Lemma 2(a)**, as an interval: a class that meets `τ` holds exactly the part `(s a, ..., s b)` of it. -/
theorem lemma2a_part (hτ : IsPath S.D S.R m s) (h : ∃ i ≤ m, s i ∈ S.cls z) :
    ∃ a b, a ≤ b ∧ b ≤ m ∧ ∀ i ≤ m, (s i ∈ S.cls z ↔ a ≤ i ∧ i ≤ b) := by
  classical
  have hP : ∃ i, i ≤ m ∧ s i ∈ S.cls z := h
  obtain ⟨ha₁, ha₂⟩ := Nat.find_spec hP
  have hb₁ : s (Nat.findGreatest (fun i => s i ∈ S.cls z) m) ∈ S.cls z :=
    Nat.findGreatest_spec (P := fun i => s i ∈ S.cls z) ha₁ ha₂
  have hb₂ : Nat.findGreatest (fun i => s i ∈ S.cls z) m ≤ m := Nat.findGreatest_le m
  refine ⟨Nat.find hP, Nat.findGreatest (fun i => s i ∈ S.cls z) m,
    Nat.le_findGreatest ha₁ ha₂, hb₂, fun i hi => ⟨fun hc => ⟨Nat.find_min' hP ⟨hi, hc⟩,
      Nat.le_findGreatest hi hc⟩, fun hab => lemma2a hτ hab.1 hab.2 hb₂ ha₂ hb₁⟩⟩

/-- The vertices `s a, ..., s b`. -/
def beta (s : ℕ → V) (a b : ℕ) : Set V := {y | ∃ i, a ≤ i ∧ i ≤ b ∧ s i = y}

variable (S)

/-- A part `β = (s a, ..., s b)` of the class of `z`, on the path `τ = (s 0, ..., s m)` of `D[R]`. The note counts `τ`
from `s 1`. Only `β ⊆ K_z` is used, not that `β` is all of the part, so this covers the note's case by `lemma2a_part`. -/
structure IsBlock (z : V) (m : ℕ) (s : ℕ → V) (a b : ℕ) : Prop where
  head : S.IsClassHead z
  path : IsPath S.D S.R m s
  le : a ≤ b
  le_m : b ≤ m
  mem : ∀ i, a ≤ i → i ≤ b → s i ∈ S.cls z

/-- `Z`: the set reached from `z` in `D[K_z ∖ β]`. -/
def Zset (z : V) (s : ℕ → V) (a b : ℕ) : Set V := {y | Reach S.D (S.cls z \ beta s a b) z y}

/-- The index `k` of the note: `s k = z` if `z` lies in `β`, and otherwise `s k` is the vertex of `β` of least index
with an arc from `Z`. -/
def IsEntry (z : V) (s : ℕ → V) (a b k : ℕ) : Prop :=
  a ≤ k ∧ k ≤ b ∧
    (s k = z ∨
      z ∉ beta s a b ∧ (∃ w ∈ S.Zset z s a b, S.D w (s k)) ∧
        ∀ l, a ≤ l → l < k → ∀ w ∈ S.Zset z s a b, ¬ S.D w (s l))

variable {S}

/-- By Lemma 2(a), a class head whose class meets `τ` has its part as a block. -/
theorem exists_isBlock (hz : S.IsClassHead z) (hτ : IsPath S.D S.R m s) (h : ∃ i ≤ m, s i ∈ S.cls z) :
    ∃ a b, S.IsBlock z m s a b ∧ ∀ i ≤ m, (s i ∈ S.cls z ↔ a ≤ i ∧ i ≤ b) := by
  obtain ⟨a, b, hab, hb, hi⟩ := lemma2a_part hτ h
  exact ⟨a, b, ⟨hz, hτ, hab, hb, fun i h₁ h₂ => (hi i (h₂.trans hb)).2 ⟨h₁, h₂⟩⟩, hi⟩

theorem IsBlock.along (hB : S.IsBlock z m s a b) {i j : ℕ} (hai : a ≤ i) (hij : i ≤ j) (hjb : j ≤ b) :
    Reach S.D (S.cls z) (s i) (s j) := by
  induction j, hij using Nat.le_induction with
  | base => exact ReflTransGen.refl
  | succ j hj ih =>
    exact (ih (by omega)).tail ⟨hB.path.arc j (by have := hB.le_m; omega), hB.mem j (by omega) (by omega),
      hB.mem (j + 1) (by omega) hjb⟩

/-- **Lemma 2(b).** `s k` exists. -/
theorem lemma2b_exists (hB : S.IsBlock z m s a b) : ∃ k, S.IsEntry z s a b k := by
  classical
  by_cases hzβ : z ∈ beta s a b
  · obtain ⟨i, hai, hib, hi⟩ := hzβ
    exact ⟨i, hai, hib, Or.inl hi⟩
  · have hr : Reach S.D (S.cls z) z (s a) := lemma1a_reach hB.head.1 (hB.mem a le_rfl hB.le)
    obtain ⟨w, t', h₁, h₂, ⟨i, hai, hib, rfl⟩, -⟩ :=
      first_entry (A := beta s a b) hr hzβ ⟨a, le_rfl, hB.le, rfl⟩
    have hP : ∃ i, a ≤ i ∧ i ≤ b ∧ ∃ w ∈ S.Zset z s a b, S.D w (s i) := ⟨i, hai, hib, w, h₁, h₂⟩
    obtain ⟨h₃, h₄, h₅⟩ := Nat.find_spec hP
    refine ⟨Nat.find hP, h₃, h₄, Or.inr ⟨hzβ, h₅, fun l hal hlk w hw hD => ?_⟩⟩
    exact Nat.find_min hP hlk ⟨hal, by omega, w, hw, hD⟩

/-- `k` is well defined. -/
theorem lemma2b_unique (hB : S.IsBlock z m s a b) {k' : ℕ} (hk : S.IsEntry z s a b k)
    (hk' : S.IsEntry z s a b k') : k = k' := by
  obtain ⟨hak, hkb, hk⟩ := hk
  obtain ⟨hak', hkb', hk'⟩ := hk'
  have hb := hB.le_m
  rcases hk with hk | ⟨hzβ, ⟨w, hw, hD⟩, hmin⟩ <;> rcases hk' with hk' | ⟨hzβ', ⟨w', hw', hD'⟩, hmin'⟩
  · exact hB.path.inj _ (by omega) _ (by omega) (hk.trans hk'.symm)
  · exact absurd ⟨k, hak, hkb, hk⟩ hzβ'
  · exact absurd ⟨k', hak', hkb', hk'⟩ hzβ
  · rcases lt_trichotomy k k' with h | h | h
    · exact absurd hD (hmin' k hak h w hw)
    · exact h
    · exact absurd hD' (hmin k' hak' h w' hw')

/-- **Lemma 2(b).** For `a ≤ l < k`, the vertices `s l` and `s k` lie in one strong component of `D[K_z]`. -/
theorem lemma2b_strong (hB : S.IsBlock z m s a b) (hk : S.IsEntry z s a b k) {l : ℕ} (hal : a ≤ l) (hlk : l < k) :
    Reach S.D (S.cls z) (s l) (s k) ∧ Reach S.D (S.cls z) (s k) (s l) := by
  obtain ⟨hak, hkb, hk⟩ := hk
  refine ⟨hB.along hal hlk.le hkb, ?_⟩
  have hr : Reach S.D (S.cls z) z (s l) := lemma1a_reach hB.head.1 (hB.mem l hal (by omega))
  rcases hk with hz | ⟨hzβ, -, hmin⟩
  · rwa [hz]
  · obtain ⟨w, t', h₁, h₂, ⟨k', hak', hk'b, rfl⟩, h₄⟩ :=
      first_entry (A := beta s a b) hr hzβ ⟨l, hal, by omega, rfl⟩
    have hkk' : k ≤ k' := by
      by_contra hlt
      exact hmin k' hak' (by omega) w h₁ h₂
    exact (hB.along hak hkk' hk'b).trans h₄

/-- **Lemma 2(b).** On a digraph with no cycle, `k = a`. -/
theorem lemma2b_dag (hB : S.IsBlock z m s a b) (hk : S.IsEntry z s a b k) (hD : ∀ u, ¬ TransGen S.D u u) : k = a := by
  by_contra hne
  have hak : a ≤ k := hk.1
  have hkb : k ≤ b := hk.2.1
  have hlt : a < k := by omega
  have hs := lemma2b_strong hB hk le_rfl hlt
  have h₁ : S.D (s a) (s (a + 1)) := hB.path.arc a (by have := hB.le_m; omega)
  have h₂ : ReflTransGen S.D (s (a + 1)) (s k) := (hB.along (by omega) hlt hkb).toD
  exact hD _ (TransGen.head' h₁ (h₂.trans hs.2.toD))

/-- **Lemma 2(b).** The path `π′`: a simple path of `D[K_z]` from `z`, first through `Z` on the indices below `c`, then
along `β` from `s k` to `s b`. It starts at `s k` if `s k = z`, and it misses what is left of `τ`, that is
`s a, ..., s (k − 1)`. -/
theorem lemma2b_path (hB : S.IsBlock z m s a b) (hk : S.IsEntry z s a b k) :
    ∃ c n w, IsPath S.D (S.cls z) n w ∧ w 0 = z ∧ n = c + (b - k) ∧ w n = s b ∧
      (∀ i < c, w i ∈ S.Zset z s a b) ∧ (∀ i, k + i ≤ b → w (c + i) = s (k + i)) ∧ (s k = z → c = 0) ∧
      ∀ l, a ≤ l → l < k → ∀ i ≤ n, w i ≠ s l := by
  obtain ⟨hak, hkb, hk⟩ := hk
  have hb := hB.le_m
  rcases hk with hz | ⟨hzβ, ⟨w₀, hw₀, hD⟩, -⟩
  · refine ⟨0, b - k, fun i => s (k + i), ⟨fun i hi => hB.mem _ (by omega) (by omega), fun i hi j hj e => ?_,
      fun i hi => hB.path.arc _ (by omega)⟩, hz, by omega, ?_, fun i hi => by omega, fun i hi => by simp,
      fun _ => rfl, fun l hal hlk i hi e => ?_⟩
    · have := hB.path.inj _ (by omega) _ (by omega) e
      omega
    · simp only
      rw [Nat.add_sub_cancel' hkb]
    · have := hB.path.inj _ (by omega) _ (by omega) e
      omega
  · have hzK : z ∈ S.cls z \ beta s a b := ⟨hB.head.2, hzβ⟩
    obtain ⟨n₀, ρ, hρ, h0, hn⟩ := exists_path hw₀ hzK
    have hρβ : ∀ i ≤ n₀, ρ i ∈ S.cls z ∧ ∀ j, a ≤ j → j ≤ b → s j ≠ ρ i := fun i hi =>
      ⟨(hρ.mem i hi).1, fun j h₁ h₂ e => (hρ.mem i hi).2 ⟨j, h₁, h₂, e⟩⟩
    obtain ⟨w, hw_lo, hw_hi⟩ : ∃ w : ℕ → V, (∀ i ≤ n₀, w i = ρ i) ∧ ∀ i, w (n₀ + 1 + i) = s (k + i) := by
      refine ⟨fun i => if i ≤ n₀ then ρ i else s (k + (i - (n₀ + 1))), fun i hi => by simp [hi], fun i => ?_⟩
      have : ¬ n₀ + 1 + i ≤ n₀ := by omega
      simp [this]
    refine ⟨n₀ + 1, n₀ + 1 + (b - k), w,
      ⟨fun i hi => ?_, fun i hi j hj e => ?_, fun i hi => ?_⟩, ?_, rfl, ?_, fun i hi => ?_, fun i hi => hw_hi i,
      fun e => absurd ⟨k, hak, hkb, e⟩ hzβ, fun l hal hlk i hi e => ?_⟩
    · by_cases h : i ≤ n₀
      · rw [hw_lo i h]
        exact (hρβ i h).1
      · obtain ⟨d, rfl⟩ : ∃ d, i = n₀ + 1 + d := ⟨i - (n₀ + 1), by omega⟩
        rw [hw_hi]
        exact hB.mem _ (by omega) (by omega)
    · by_cases h : i ≤ n₀ <;> by_cases h' : j ≤ n₀
      · rw [hw_lo i h, hw_lo j h'] at e
        exact hρ.inj i h j h' e
      · obtain ⟨d, rfl⟩ : ∃ d, j = n₀ + 1 + d := ⟨j - (n₀ + 1), by omega⟩
        rw [hw_lo i h, hw_hi] at e
        exact absurd e.symm ((hρβ i h).2 _ (by omega) (by omega))
      · obtain ⟨d, rfl⟩ : ∃ d, i = n₀ + 1 + d := ⟨i - (n₀ + 1), by omega⟩
        rw [hw_lo j h', hw_hi] at e
        exact absurd e ((hρβ j h').2 _ (by omega) (by omega))
      · obtain ⟨d, rfl⟩ : ∃ d, i = n₀ + 1 + d := ⟨i - (n₀ + 1), by omega⟩
        obtain ⟨d', rfl⟩ : ∃ d', j = n₀ + 1 + d' := ⟨j - (n₀ + 1), by omega⟩
        rw [hw_hi, hw_hi] at e
        have := hB.path.inj _ (by omega) _ (by omega) e
        omega
    · by_cases h : i < n₀
      · rw [hw_lo i h.le, hw_lo (i + 1) h]
        exact hρ.arc i h
      · by_cases h' : i = n₀
        · subst h'
          have e : w (i + 1) = s k := by simpa using hw_hi 0
          rw [hw_lo i le_rfl, e, hn]
          exact hD
        · obtain ⟨d, rfl⟩ : ∃ d, i = n₀ + 1 + d := ⟨i - (n₀ + 1), by omega⟩
          rw [hw_hi, show n₀ + 1 + d + 1 = n₀ + 1 + (d + 1) by omega, hw_hi]
          exact hB.path.arc _ (by omega)
    · rw [hw_lo 0 (Nat.zero_le _), h0]
    · rw [hw_hi]
      rw [Nat.add_sub_cancel' hkb]
    · rw [hw_lo i (by omega)]
      have hr := hρ.reach (Nat.zero_le i) (by omega : i ≤ n₀)
      rwa [h0] at hr
    · by_cases h : i ≤ n₀
      · rw [hw_lo i h] at e
        exact (hρβ i h).2 l hal (by omega) e.symm
      · obtain ⟨d, rfl⟩ : ∃ d, i = n₀ + 1 + d := ⟨i - (n₀ + 1), by omega⟩
        rw [hw_hi] at e
        have := hB.path.inj _ (by omega) _ (by omega) e
        omega

variable (S)

/-- The next application of Lemma 1: the class `K_z` with a path in `D[K_z]` from `z`. -/
def ofClass (hz : S.IsClassHead z) {n : ℕ} {w : ℕ → V} (hw : IsPath S.D (S.cls z) n w) (h0 : w 0 = z) : Split V where
  D := S.D
  id := S.id
  id_inj := S.id_inj
  K := S.cls z
  k := n
  v := w
  path := hw
  reached y hy := by
    rw [h0]
    exact lemma1a_reach hz.1 hy

variable {S}

/-- What is left of `τ` after `π′` goes into Lemma 1 for `K_z` is the path `(s a, ..., s (k − 1))` in `D[R′]`, so
Lemma 2 applies to it again, and it is shorter than `β`. -/
theorem left_isPath (hB : S.IsBlock z m s a b) (hk : S.IsEntry z s a b k) {n : ℕ} {w : ℕ → V}
    (hw : IsPath S.D (S.cls z) n w) (h0 : w 0 = z) (hleft : ∀ l, a ≤ l → l < k → ∀ i ≤ n, w i ≠ s l)
    (hak : a < k) : IsPath S.D (S.ofClass hB.head hw h0).R (k - a - 1) (fun i => s (a + i)) := by
  have hkb : k ≤ b := hk.2.1
  have hb := hB.le_m
  refine ⟨fun i hi => ⟨hB.mem _ (by omega) (by omega), ?_⟩, fun i hi j hj e => ?_,
    fun i hi => hB.path.arc _ (by omega)⟩
  · rintro ⟨j, hj, e⟩
    exact hleft (a + i) (by omega) (by omega) j hj e
  · have := hB.path.inj _ (by omega) _ (by omega) e
    omega

end Blocks

end Split

/-- A problem `(x, K)` with `K` finite has a search tree, by Lemma 1(c) with `π = (x)` and recursion on the classes. So
the definition is not vacuous, and this is the recursion of Section 4 in its plainest form. -/
theorem exists_searchTree {D : V → V → Prop} {id : V → ℕ} (hid : Function.Injective id) (n : ℕ) :
    ∀ (K : Set V) (x : V), K.ncard = n → K.Finite → x ∈ K → (∀ y ∈ K, Reach D K x y) →
      ∃ addr, IsSearchTree D K x addr := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K x hn hK hx hr
    let S : Split V := ⟨D, id, hid, K, 0, fun _ => x,
      ⟨fun _ _ => hx, fun i hi j hj _ => by omega, fun i hi => by omega⟩, hr⟩
    have hlt : ∀ z, (S.cls z).ncard < n := by
      intro z
      rw [← hn]
      refine Set.ncard_lt_ncard ⟨fun y hy => hy.1.1, fun h => ?_⟩ hK
      exact (h hx).1.2 ⟨0, le_rfl, rfl⟩
    have hsub : ∀ z, (S.cls z).Finite := fun z => hK.subset fun y hy => hy.1.1
    have hex : ∀ z, ∃ t, S.IsClassHead z → IsSearchTree D (S.cls z) z t := by
      intro z
      by_cases hz : S.IsClassHead z
      · obtain ⟨t, ht⟩ := ih _ (hlt z) (S.cls z) z rfl (hsub z) hz.2
          (fun y hy => Split.lemma1a_reach hz.1 hy)
        exact ⟨t, fun _ => ht⟩
      · exact ⟨fun _ => [], fun h => absurd h hz⟩
    choose T hT using hex
    exact ⟨S.addr T, Split.lemma1c hT⟩

/-! ## Fact 1: a real depth-first search -/

/-- The scanning loop of a depth-first search with adjacency lists `adj`, as a big-step relation. In
`Dfs adj u vis l vis' E F`, the search is at `u`, the stack `vis` holds the visited vertices with the latest on top, and
`l` is what is left to scan of the arcs of `u`. An unvisited head is pushed and visited at once, with the scan of `u`
going on after that. The loop ends with the stack `vis'`, the tree arcs `E` in the order of their discovery, and the
vertices `F` it finished, in the order of finishing. -/
inductive Dfs (adj : V → List V) : V → List V → List V → List V → List (V × V) → List V → Prop
  | nil (u : V) (vis : List V) : Dfs adj u vis [] vis [] []
  | seen {u : V} {vis : List V} {w : V} {l vis' : List V} {E : List (V × V)} {F : List V} :
      w ∈ vis → Dfs adj u vis l vis' E F → Dfs adj u vis (w :: l) vis' E F
  | new {u : V} {vis : List V} {w : V} {l vis₁ : List V} {E₁ : List (V × V)} {F₁ vis₂ : List V}
      {E₂ : List (V × V)} {F₂ : List V} :
      w ∉ vis → Dfs adj w (w :: vis) (adj w) vis₁ E₁ F₁ → Dfs adj u vis₁ l vis₂ E₂ F₂ →
      Dfs adj u vis (w :: l) vis₂ ((u, w) :: (E₁ ++ E₂)) (F₁ ++ w :: F₂)

/-- The search from `x`: `pre` is the order of visits, `E` the tree arcs in the order of discovery, `post` the order of
finishing. -/
def DfsFrom (adj : V → List V) (x : V) (pre : List V) (E : List (V × V)) (post : List V) : Prop :=
  ∃ F, Dfs adj x [x] (adj x) pre.reverse E F ∧ post = F ++ [x]

/-- The search is deterministic, so it has one result. -/
theorem Dfs.det {adj : V → List V} {u : V} {vis l vis₁ F₁ vis₂ F₂ : List V} {E₁ E₂ : List (V × V)}
    (h₁ : Dfs adj u vis l vis₁ E₁ F₁) (h₂ : Dfs adj u vis l vis₂ E₂ F₂) : vis₁ = vis₂ ∧ E₁ = E₂ ∧ F₁ = F₂ := by
  induction h₁ generalizing vis₂ E₂ F₂ with
  | nil u vis =>
    cases h₂
    exact ⟨rfl, rfl, rfl⟩
  | seen hw _ ih =>
    cases h₂ with
    | seen _ h => exact ih h
    | new hn _ _ => exact absurd hw hn
  | new hn _ _ ih₃ ih₄ =>
    cases h₂ with
    | seen hw _ => exact absurd hw hn
    | new _ h₅ h₆ =>
      obtain ⟨rfl, rfl, rfl⟩ := ih₃ h₅
      obtain ⟨rfl, rfl, rfl⟩ := ih₄ h₆
      exact ⟨rfl, rfl, rfl⟩

theorem Dfs.append_seen {adj : V → List V} {u : V} {vis l vis' F os : List V} {E : List (V × V)}
    (h : Dfs adj u vis l vis' E F) (hos : ∀ w ∈ os, w ∈ vis') : Dfs adj u vis (l ++ os) vis' E F := by
  induction h with
  | nil u vis =>
    induction os with
    | nil => exact Dfs.nil _ _
    | cons w os ih =>
      exact Dfs.seen (hos w (by simp)) (ih fun w h => hos w (by simp [h]))
  | seen hw _ ih => exact Dfs.seen hw (ih hos)
  | new hn h₃ _ _ ih₄ => exact Dfs.new hn h₃ (ih₄ hos)

/-- Adjacency lists for `D[K]` where each vertex lists its children of the tree in order and then its other arcs. -/
structure IsAdj (D : V → V → Prop) (K : Set V) (addr : V → List ℕ) (adj : V → List V) : Prop where
  mem : ∀ u ∈ K, ∀ w, w ∈ adj u ↔ w ∈ K ∧ D u w
  children_first : ∀ u ∈ K, ∃ cs os, adj u = cs ++ os ∧ cs.Pairwise (fun a b => addr a < addr b) ∧
    ∀ w, w ∈ cs ↔ w ∈ K ∧ ∃ d, addr w = addr u ++ [d]

/-- What a search from `x` gives for the tree with addresses `addr`: it visits `K` in pre-order and finishes it in
post-order, and its tree arcs are the arcs of the tree, in the order of pre-order. -/
structure Run (K : Set V) (x : V) (addr : V → List ℕ) (pre : List V) (E : List (V × V)) (post : List V) : Prop where
  pre_head : pre.head? = some x
  pre_mem : ∀ w, w ∈ pre ↔ w ∈ K
  pre_sorted : pre.Pairwise (fun a b => addr a < addr b)
  post_mem : ∀ w, w ∈ post ↔ w ∈ K
  post_sorted : post.Pairwise (fun a b => PostLt (addr a) (addr b))
  arc_mem : ∀ a b, (a, b) ∈ E ↔ a ∈ K ∧ b ∈ K ∧ ∃ d, addr b = addr a ++ [d]
  arc_order : E.map Prod.snd = pre.tail

theorem isRight_of_siblings {P : List ℕ} {d d' : ℕ} (h : P ++ [d] < P ++ [d']) : IsRight (P ++ [d]) (P ++ [d']) := by
  rw [append_lt_append_iff, List.cons_lt_cons_iff] at h
  rcases h with h | ⟨-, h⟩
  · exact IsRight.of_lt_of_append h
  · exact absurd h (List.not_lt_nil _)

theorem exists_of_between {l m : List ℕ} {d : ℕ} (h₁ : l < m) (h₂ : m < l ++ [d]) :
    ∃ d' t, m = l ++ d' :: t ∧ d' < d := by
  induction l generalizing m with
  | nil =>
    cases m with
    | nil => exact absurd h₁ (List.not_lt_nil _)
    | cons e t =>
      rcases List.cons_lt_cons_iff.1 h₂ with h | ⟨-, h⟩
      · exact ⟨e, t, rfl, h⟩
      · exact absurd h (List.not_lt_nil _)
  | cons a l ih =>
    cases m with
    | nil => exact absurd h₁ (List.not_lt_nil _)
    | cons b m =>
      have h₃ := List.cons_lt_cons_iff.1 h₁
      have h₄ := List.cons_lt_cons_iff.1 h₂
      rcases h₃ with h₃ | ⟨rfl, h₃⟩
      · rcases h₄ with h₄ | ⟨rfl, -⟩ <;> omega
      · rcases h₄ with h₄ | ⟨-, h₄⟩
        · omega
        · obtain ⟨d', t, rfl, hd⟩ := ih h₃ h₄
          exact ⟨d', t, rfl, hd⟩

theorem le_nil_eq {l : List ℕ} (h : l ≤ []) : l = [] := by
  cases l with
  | nil => rfl
  | cons a l => exact absurd (List.nil_lt_cons a l) (not_lt.2 h)

section Fact1

variable {D : V → V → Prop} {K : Set V} {x : V} {addr : V → List ℕ} {adj : V → List V}

theorem IsSearchTree.child_of_desc (hT : IsSearchTree D K x addr) {u w : V} (hw : w ∈ K) (hu : u ∈ K)
    (hp : addr u <+: addr w) (hne : w ≠ u) : ∃ c ∈ K, (∃ d, addr c = addr u ++ [d]) ∧ addr c <+: addr w := by
  obtain ⟨t, ht⟩ := hp
  cases t with
  | nil => exact absurd (hT.inj hw hu (by simpa using ht.symm)) hne
  | cons d t =>
    have hl : addr u ++ [d] <+: addr w := ⟨t, by rw [← ht]; simp⟩
    obtain ⟨c, hc, hcc⟩ := hT.prefix_closed w hw _ hl
    exact ⟨c, hc, ⟨d, hcc⟩, by rw [hcc]; exact hl⟩

/-- What a part of the search leaves behind. `L` is what it visits, in order. -/
structure RunSpec (addr : V → List ℕ) (Mem : V → Prop) (Arc : V → V → Prop) (L : List V) (E : List (V × V))
    (F : List V) : Prop where
  mem_L : ∀ w, w ∈ L ↔ Mem w
  sorted_L : L.Pairwise (fun a b => addr a < addr b)
  snd_E : E.map Prod.snd = L
  mem_E : ∀ a b, (a, b) ∈ E ↔ Arc a b
  mem_F : ∀ w, w ∈ F ↔ Mem w
  sorted_F : F.Pairwise (fun a b => PostLt (addr a) (addr b))

/-- The claim of Lemma 9 for one vertex: started with exactly what comes up to `u` in pre-order on the stack, the visit
of `u` adds its proper descendants, and nothing else. -/
def VisitSpec (K : Set V) (addr : V → List ℕ) (adj : V → List V) (u : V) : Prop :=
  ∀ vis : List V, (∀ w, w ∈ vis ↔ w ∈ K ∧ addr w ≤ addr u) →
    ∃ L E F, Dfs adj u vis (adj u) (L.reverse ++ vis) E F ∧
      RunSpec addr (fun w => w ∈ K ∧ addr u <+: addr w ∧ w ≠ u)
        (fun a b => a ∈ K ∧ b ∈ K ∧ addr u <+: addr a ∧ ∃ d, addr b = addr a ++ [d]) L E F

/-- The scan of the children of `u`, given the claim for each of them. `done` are the children already visited. -/
theorem scan_children (hT : IsSearchTree D K x addr) {u : V}
    (hc : ∀ c ∈ K, (∃ d, addr c = addr u ++ [d]) → VisitSpec K addr adj c)
    (rest done : List V) (hsorted : (done ++ rest).Pairwise (fun a b => addr a < addr b))
    (hmem : ∀ w, w ∈ done ++ rest ↔ w ∈ K ∧ ∃ d, addr w = addr u ++ [d]) (vis : List V)
    (hvis : ∀ w, w ∈ vis ↔ w ∈ K ∧ (addr w ≤ addr u ∨ ∃ c ∈ done, addr c <+: addr w)) :
    ∃ L E F, Dfs adj u vis rest (L.reverse ++ vis) E F ∧
      RunSpec addr (fun w => w ∈ K ∧ ∃ c ∈ rest, addr c <+: addr w)
        (fun a b => (a = u ∧ b ∈ rest) ∨
          (a ∈ K ∧ b ∈ K ∧ (∃ c ∈ rest, addr c <+: addr a) ∧ ∃ d, addr b = addr a ++ [d])) L E F := by
  induction rest generalizing done vis with
  | nil =>
    refine ⟨[], [], [], by simpa using Dfs.nil u vis, ⟨fun w => ?_, List.Pairwise.nil, rfl, fun a b => ?_,
      fun w => ?_, List.Pairwise.nil⟩⟩ <;> simp
  | cons c rest ih =>
    obtain ⟨hcK, d, hd⟩ := (hmem c).1 (by simp)
    obtain ⟨-, hrest, hcross⟩ := List.pairwise_append.1 hsorted
    obtain ⟨hcrest, hrest'⟩ := List.pairwise_cons.1 hrest
    have hsib : ∀ c' ∈ done, IsRight (addr c') (addr c) := by
      intro c' hc'
      obtain ⟨-, d', hd'⟩ := (hmem c').1 (List.mem_append_left _ hc')
      have := hcross c' hc' c (by simp)
      rw [hd', hd] at this ⊢
      exact isRight_of_siblings this
    have hsib' : ∀ c' ∈ rest, IsRight (addr c) (addr c') := by
      intro c' hc'
      obtain ⟨-, d', hd'⟩ := (hmem c').1 (by simp [hc'])
      have := hcrest c' hc'
      rw [hd', hd] at this ⊢
      exact isRight_of_siblings this
    have hun : addr u < addr c := by
      rw [hd]
      exact lt_of_prefix_of_ne (List.prefix_append _ _) (by simp)
    have hcvis : c ∉ vis := by
      intro h
      rcases ((hvis c).1 h).2 with h | ⟨c', hc', hp⟩
      · exact absurd hun (not_lt.2 h)
      · exact (hsib c' hc').2 hp
    have hvisc : ∀ w, w ∈ c :: vis ↔ w ∈ K ∧ addr w ≤ addr c := by
      intro w
      constructor
      · intro h
        rcases List.mem_cons.1 h with rfl | h
        · exact ⟨hcK, le_rfl⟩
        · obtain ⟨hw, h | ⟨c', hc', hp⟩⟩ := (hvis w).1 h
          · exact ⟨hw, h.trans hun.le⟩
          · exact ⟨hw, ((hsib c' hc').extend hp List.prefix_rfl).1.le⟩
      · rintro ⟨hw, hle⟩
        rcases hle.eq_or_lt with h | hlt
        · exact List.mem_cons.2 (Or.inl (hT.inj hw hcK h))
        · refine List.mem_cons.2 (Or.inr ((hvis w).2 ⟨hw, ?_⟩))
          by_cases hwu : addr w ≤ addr u
          · exact Or.inl hwu
          · refine Or.inr ?_
            have hb : addr w < addr u ++ [d] := by rwa [hd] at hlt
            obtain ⟨d', t, ht, hdd⟩ := exists_of_between (not_le.1 hwu) hb
            have hl : addr u ++ [d'] <+: addr w := ⟨t, by rw [ht]; simp⟩
            obtain ⟨w', hw', hw'a⟩ := hT.prefix_closed w hw _ hl
            have hw'm : w' ∈ done ++ c :: rest := (hmem w').2 ⟨hw', d', hw'a⟩
            have hw'lt : addr w' < addr c := by
              rw [hw'a, hd, append_lt_append_iff]
              simp [List.cons_lt_cons_iff, hdd]
            rcases List.mem_append.1 hw'm with h | h
            · exact ⟨w', h, by rw [hw'a]; exact hl⟩
            · exfalso
              rcases List.mem_cons.1 h with rfl | h
              · exact lt_irrefl _ hw'lt
              · exact lt_asymm hw'lt (hcrest w' h)
    obtain ⟨Lc, Ec, Fc, hDc, hSc⟩ := hc c hcK ⟨d, hd⟩ (c :: vis) hvisc
    have hvis₁ : ∀ w, w ∈ Lc.reverse ++ c :: vis ↔
        w ∈ K ∧ (addr w ≤ addr u ∨ ∃ c' ∈ done ++ [c], addr c' <+: addr w) := by
      intro w
      constructor
      · intro h
        rcases List.mem_append.1 h with h | h
        · obtain ⟨hw, hp, -⟩ := (hSc.mem_L w).1 (List.mem_reverse.1 h)
          exact ⟨hw, Or.inr ⟨c, by simp, hp⟩⟩
        · rcases List.mem_cons.1 h with rfl | h
          · exact ⟨hcK, Or.inr ⟨w, by simp, List.prefix_rfl⟩⟩
          · obtain ⟨hw, h | ⟨c', hc', hp⟩⟩ := (hvis w).1 h
            · exact ⟨hw, Or.inl h⟩
            · exact ⟨hw, Or.inr ⟨c', by simp [hc'], hp⟩⟩
      · rintro ⟨hw, h | ⟨c', hc', hp⟩⟩
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ ((hvis w).2 ⟨hw, Or.inl h⟩))
        · rcases List.mem_append.1 hc' with hc' | hc'
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ ((hvis w).2 ⟨hw, Or.inr ⟨c', hc', hp⟩⟩))
          · obtain rfl := List.mem_singleton.1 hc'
            by_cases hwc : w = c'
            · subst hwc
              simp
            · exact List.mem_append_left _ (List.mem_reverse.2 ((hSc.mem_L w).2 ⟨hw, hp, hwc⟩))
    obtain ⟨L', E', F', hD', hS'⟩ := ih (done ++ [c])
      (by rw [List.append_assoc]; exact hsorted)
      (by rw [List.append_assoc]; exact hmem) (Lc.reverse ++ c :: vis) hvis₁
    have hsorted_c : ∀ y ∈ Lc, addr c < addr y := by
      intro y hy
      obtain ⟨hyK, hp, hne⟩ := (hSc.mem_L y).1 hy
      exact lt_of_prefix_of_ne hp fun e => hne (hT.inj hyK hcK e.symm)
    have hcross_L : ∀ y ∈ L', IsRight (addr c) (addr y) := by
      intro y hy
      obtain ⟨-, c', hc', hp⟩ := (hS'.mem_L y).1 hy
      exact (hsib' c' hc').extend List.prefix_rfl hp
    have hcross_LL : ∀ a ∈ Lc, ∀ b ∈ L', IsRight (addr a) (addr b) := by
      intro a ha b hb
      obtain ⟨-, hp, -⟩ := (hSc.mem_L a).1 ha
      exact (hcross_L b hb).extend hp List.prefix_rfl
    refine ⟨c :: (Lc ++ L'), (u, c) :: (Ec ++ E'), Fc ++ c :: F', ?_,
      ⟨fun w => ?_, ?_, ?_, fun a b => ?_, fun w => ?_, ?_⟩⟩
    · have := Dfs.new hcvis hDc hD'
      simpa [List.reverse_append, List.append_assoc] using this
    · constructor
      · intro h
        rcases List.mem_cons.1 h with rfl | h
        · exact ⟨hcK, w, by simp, List.prefix_rfl⟩
        · rcases List.mem_append.1 h with h | h
          · obtain ⟨hw, hp, -⟩ := (hSc.mem_L w).1 h
            exact ⟨hw, c, by simp, hp⟩
          · obtain ⟨hw, c', hc', hp⟩ := (hS'.mem_L w).1 h
            exact ⟨hw, c', List.mem_cons_of_mem _ hc', hp⟩
      · rintro ⟨hw, c', hc', hp⟩
        rcases List.mem_cons.1 hc' with rfl | hc'
        · by_cases hwc : w = c'
          · subst hwc
            simp
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ ((hSc.mem_L w).2 ⟨hw, hp, hwc⟩))
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ ((hS'.mem_L w).2 ⟨hw, c', hc', hp⟩))
    · refine List.pairwise_cons.2 ⟨fun y hy => ?_, List.pairwise_append.2 ⟨hSc.sorted_L, hS'.sorted_L,
        fun a ha b hb => (hcross_LL a ha b hb).1⟩⟩
      rcases List.mem_append.1 hy with hy | hy
      · exact hsorted_c y hy
      · exact (hcross_L y hy).1
    · simp [hSc.snd_E, hS'.snd_E]
    · constructor
      · intro h
        rcases List.mem_cons.1 h with h | h
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
          exact Or.inl ⟨rfl, by simp⟩
        · rcases List.mem_append.1 h with h | h
          · obtain ⟨ha, hb, hp, hd'⟩ := (hSc.mem_E a b).1 h
            exact Or.inr ⟨ha, hb, ⟨c, by simp, hp⟩, hd'⟩
          · rcases (hS'.mem_E a b).1 h with ⟨rfl, hb⟩ | ⟨ha, hb, ⟨c', hc', hp⟩, hd'⟩
            · exact Or.inl ⟨rfl, List.mem_cons_of_mem _ hb⟩
            · exact Or.inr ⟨ha, hb, ⟨c', List.mem_cons_of_mem _ hc', hp⟩, hd'⟩
      · rintro (⟨rfl, hb⟩ | ⟨ha, hb, ⟨c', hc', hp⟩, hd'⟩)
        · rcases List.mem_cons.1 hb with rfl | hb
          · simp
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ ((hS'.mem_E _ _).2 (Or.inl ⟨rfl, hb⟩)))
        · rcases List.mem_cons.1 hc' with rfl | hc'
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ ((hSc.mem_E _ _).2 ⟨ha, hb, hp, hd'⟩))
          · exact List.mem_cons_of_mem _ (List.mem_append_right _
              ((hS'.mem_E _ _).2 (Or.inr ⟨ha, hb, ⟨c', hc', hp⟩, hd'⟩)))
    · constructor
      · intro h
        rcases List.mem_append.1 h with h | h
        · obtain ⟨hw, hp, -⟩ := (hSc.mem_F w).1 h
          exact ⟨hw, c, by simp, hp⟩
        · rcases List.mem_cons.1 h with rfl | h
          · exact ⟨hcK, w, by simp, List.prefix_rfl⟩
          · obtain ⟨hw, c', hc', hp⟩ := (hS'.mem_F w).1 h
            exact ⟨hw, c', List.mem_cons_of_mem _ hc', hp⟩
      · rintro ⟨hw, c', hc', hp⟩
        rcases List.mem_cons.1 hc' with rfl | hc'
        · by_cases hwc : w = c'
          · subst hwc
            simp
          · exact List.mem_append_left _ ((hSc.mem_F w).2 ⟨hw, hp, hwc⟩)
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ ((hS'.mem_F w).2 ⟨hw, c', hc', hp⟩))
    · refine List.pairwise_append.2 ⟨hSc.sorted_F, List.pairwise_cons.2 ⟨fun y hy => ?_, hS'.sorted_F⟩,
        fun a ha b hb => ?_⟩
      · exact Or.inl (hcross_L y ((hS'.mem_L y).2 ((hS'.mem_F y).1 hy)))
      · have ha' := (hSc.mem_L a).2 ((hSc.mem_F a).1 ha)
        rcases List.mem_cons.1 hb with rfl | hb
        · obtain ⟨haK, hp, hne⟩ := (hSc.mem_L a).1 ha'
          exact Or.inr ⟨hp, fun e => hne (hT.inj haK hcK e.symm)⟩
        · exact Or.inl (hcross_LL a ha' b ((hS'.mem_L b).2 ((hS'.mem_F b).1 hb)))

/-- The claim of Lemma 9 for `u`, given the claim for its children. Here the arcs other than tree arcs are scanned, and
the rule that no arc goes right says that all of their heads are visited by then. -/
theorem visit_of_children (hT : IsSearchTree D K x addr) (hadj : IsAdj D K addr adj) {u : V} (hu : u ∈ K)
    (hc : ∀ c ∈ K, (∃ d, addr c = addr u ++ [d]) → VisitSpec K addr adj c) : VisitSpec K addr adj u := by
  intro vis hvis
  obtain ⟨cs, os, hadj_eq, hsorted, hmem⟩ := hadj.children_first u hu
  obtain ⟨L, E, F, hD, hS⟩ := scan_children hT hc cs [] hsorted hmem vis (by simpa using hvis)
  have hdesc : ∀ w, w ∈ K → addr u <+: addr w → w ≠ u → ∃ c ∈ cs, addr c <+: addr w := by
    intro w hw hp hne
    obtain ⟨c, hcK, hd, hcp⟩ := hT.child_of_desc hw hu hp hne
    exact ⟨c, (hmem c).2 ⟨hcK, hd⟩, hcp⟩
  have hcs_pref : ∀ c ∈ cs, addr u <+: addr c ∧ addr c ≠ addr u := by
    intro c hc'
    obtain ⟨-, d, hd⟩ := (hmem c).1 hc'
    rw [hd]
    exact ⟨List.prefix_append _ _, by simp⟩
  refine ⟨L, E, F, ?_, ?_⟩
  · rw [hadj_eq]
    refine hD.append_seen fun w hw => ?_
    obtain ⟨hwK, hDuw⟩ := (hadj.mem u hu w).1 (by rw [hadj_eq]; exact List.mem_append_right _ hw)
    rcases le_or_prefix_of_not_isRight (hT.no_right u hu w hwK hDuw) with h | h
    · exact List.mem_append_right _ ((hvis w).2 ⟨hwK, h⟩)
    · by_cases hne : w = u
      · subst hne
        exact List.mem_append_right _ ((hvis w).2 ⟨hwK, le_rfl⟩)
      · obtain ⟨c, hc', hcp⟩ := hdesc w hwK h hne
        exact List.mem_append_left _ (List.mem_reverse.2 ((hS.mem_L w).2 ⟨hwK, c, hc', hcp⟩))
  · have hM : ∀ w, (w ∈ K ∧ ∃ c ∈ cs, addr c <+: addr w) ↔ (w ∈ K ∧ addr u <+: addr w ∧ w ≠ u) := by
      intro w
      constructor
      · rintro ⟨hw, c, hc', hp⟩
        obtain ⟨h₁, h₂⟩ := hcs_pref c hc'
        refine ⟨hw, h₁.trans hp, ?_⟩
        rintro rfl
        exact h₂ (List.IsPrefix.eq_of_length_le hp h₁.length_le)
      · rintro ⟨hw, hp, hne⟩
        exact ⟨hw, hdesc w hw hp hne⟩
    refine ⟨fun w => (hS.mem_L w).trans (hM w), hS.sorted_L, hS.snd_E, fun a b => (hS.mem_E a b).trans ?_,
      fun w => (hS.mem_F w).trans (hM w), hS.sorted_F⟩
    constructor
    · rintro (⟨rfl, hb⟩ | ⟨ha, hb, ⟨c, hc', hp⟩, hd⟩)
      · obtain ⟨hbK, hd⟩ := (hmem b).1 hb
        exact ⟨hu, hbK, List.prefix_rfl, hd⟩
      · exact ⟨ha, hb, (hcs_pref c hc').1.trans hp, hd⟩
    · rintro ⟨ha, hb, hp, hd⟩
      by_cases hau : a = u
      · subst hau
        exact Or.inl ⟨rfl, (hmem b).2 ⟨hb, hd⟩⟩
      · exact Or.inr ⟨ha, hb, hdesc a ha hp hau, hd⟩

theorem visit_all (hK : K.Finite) (hT : IsSearchTree D K x addr) (hadj : IsAdj D K addr adj) {u : V} (hu : u ∈ K) :
    VisitSpec K addr adj u := by
  obtain ⟨M, hM'⟩ : ∃ M, ∀ w ∈ K, (addr w).length ≤ M :=
    ⟨hK.toFinset.sup fun w => (addr w).length, fun w hw =>
      Finset.le_sup (f := fun w => (addr w).length) (hK.mem_toFinset.2 hw)⟩
  have key : ∀ N, ∀ u ∈ K, M < (addr u).length + N → VisitSpec K addr adj u := by
    intro N
    induction N with
    | zero =>
      intro u hu h
      have := hM' u hu
      omega
    | succ N ih =>
      intro u hu h
      refine visit_of_children hT hadj hu fun c hc hd => ih c hc ?_
      obtain ⟨d, hd⟩ := hd
      rw [hd, List.length_append, List.length_singleton]
      omega
  exact key (M + 1) u hu (by omega)

/-- **Fact 1.** A search tree is the result of a real depth-first search that at each vertex visits its children in
order and then scans its other arcs. -/
theorem fact1 (hK : K.Finite) (hT : IsSearchTree D K x addr) (hadj : IsAdj D K addr adj) :
    ∃ pre E post, DfsFrom adj x pre E post ∧ Run K x addr pre E post := by
  have hvis : ∀ w, w ∈ [x] ↔ w ∈ K ∧ addr w ≤ addr x := by
    intro w
    constructor
    · intro h
      obtain rfl := List.mem_singleton.1 h
      exact ⟨hT.root_mem, le_rfl⟩
    · rintro ⟨hw, hle⟩
      rw [hT.root] at hle
      exact List.mem_singleton.2 (hT.inj hw hT.root_mem ((le_nil_eq hle).trans hT.root.symm))
  obtain ⟨L, E, F, hD, hS⟩ := visit_all hK hT hadj hT.root_mem [x] hvis
  have hne : ∀ w ∈ K, w ≠ x → [] ≠ addr w := fun w hw hne e =>
    hne (hT.inj hw hT.root_mem (e.symm.trans hT.root.symm))
  refine ⟨x :: L, E, F ++ [x], ⟨F, by simpa using hD, rfl⟩,
    ⟨rfl, fun w => ?_, ?_, fun w => ?_, ?_, fun a b => ?_, ?_⟩⟩
  · simp only [List.mem_cons]
    rw [hS.mem_L w]
    constructor
    · rintro (rfl | ⟨hw, -⟩)
      · exact hT.root_mem
      · exact hw
    · intro hw
      by_cases h : w = x
      · exact Or.inl h
      · exact Or.inr ⟨hw, by rw [hT.root]; exact List.nil_prefix, h⟩
  · refine List.pairwise_cons.2 ⟨fun y hy => ?_, hS.sorted_L⟩
    obtain ⟨hyK, -, hyx⟩ := (hS.mem_L y).1 hy
    rw [hT.root]
    exact lt_of_prefix_of_ne List.nil_prefix (hne y hyK hyx)
  · simp only [List.mem_append, List.mem_singleton]
    rw [hS.mem_F w]
    constructor
    · rintro (⟨hw, -⟩ | rfl)
      · exact hw
      · exact hT.root_mem
    · intro hw
      by_cases h : w = x
      · exact Or.inr h
      · exact Or.inl ⟨hw, by rw [hT.root]; exact List.nil_prefix, h⟩
  · refine List.pairwise_append.2 ⟨hS.sorted_F, by simp, fun a ha b hb => ?_⟩
    obtain rfl := List.mem_singleton.1 hb
    obtain ⟨haK, -, hax⟩ := (hS.mem_F a).1 ha
    rw [hT.root]
    exact Or.inr ⟨List.nil_prefix, hne a haK hax⟩
  · rw [hS.mem_E a b]
    constructor
    · rintro ⟨ha, hb, -, hd⟩
      exact ⟨ha, hb, hd⟩
    · rintro ⟨ha, hb, hd⟩
      exact ⟨ha, hb, by rw [hT.root]; exact List.nil_prefix, hd⟩
  · simpa using hS.snd_E

/-- The hypothesis of Fact 1 can be met: such adjacency lists exist on a finite set. -/
theorem exists_adj (hK : K.Finite) (hT : IsSearchTree D K x addr) : ∃ adj, IsAdj D K addr adj := by
  classical
  let le : V → V → Prop := fun a b => addr a ≤ addr b
  have : Std.Total le := ⟨fun a b => le_total (addr a) (addr b)⟩
  have : IsTrans V le := ⟨fun _ _ _ h₁ h₂ => le_trans h₁ h₂⟩
  let cs : V → List V := fun u =>
    ((hK.toFinset.filter fun w => ∃ d, addr w = addr u ++ [d]).toList).insertionSort le
  let os : V → List V := fun u => (hK.toFinset.filter fun w => D u w).toList
  have hcs : ∀ u w, w ∈ cs u ↔ w ∈ K ∧ ∃ d, addr w = addr u ++ [d] := by
    intro u w
    simp [cs, List.mem_insertionSort]
  have hos : ∀ u w, w ∈ os u ↔ w ∈ K ∧ D u w := by
    intro u w
    simp [os]
  refine ⟨fun u => cs u ++ os u, ⟨fun u hu w => ?_, fun u hu => ⟨cs u, os u, rfl, ?_, hcs u⟩⟩⟩
  · simp only [List.mem_append, hcs, hos]
    constructor
    · rintro (⟨hw, d, hd⟩ | h)
      · exact ⟨hw, hT.parent u hu w hw d hd⟩
      · exact h
    · exact Or.inr
  · have h₁ : (cs u).Pairwise le := List.pairwise_insertionSort le _
    have h₂ : (cs u).Nodup := (List.perm_insertionSort le _).nodup_iff.2 (Finset.nodup_toList _)
    refine (h₁.and h₂).imp_of_mem fun {a b} ha hb h => ?_
    exact lt_of_le_of_ne h.1 fun e => h.2 (hT.inj ((hcs u a).1 ha).1 ((hcs u b).1 hb).1 e)

/-- **Fact 1**, with the adjacency lists found. -/
theorem fact1_exists (hK : K.Finite) (hT : IsSearchTree D K x addr) :
    ∃ adj pre E post, IsAdj D K addr adj ∧ DfsFrom adj x pre E post ∧ Run K x addr pre E post := by
  obtain ⟨adj, hadj⟩ := exists_adj hK hT
  obtain ⟨pre, E, post, h₁, h₂⟩ := fact1 hK hT hadj
  exact ⟨adj, pre, E, post, hadj, h₁, h₂⟩

/-- The numbers of a run: `pre` and `post` number `K`, and `b` is right of `a` in the sense of the note, that is
`pre(b) > pre(a)` and `post(b) > post(a)`, exactly when `IsRight (addr a) (addr b)`. So the model by addresses agrees with
the definition of the note, for the numbers that the search assigns. -/
theorem Run.isRight_iff [DecidableEq V] {pre post : List V} {E : List (V × V)} (hR : Run K x addr pre E post) {a b : V}
    (ha : a ∈ K) (hb : b ∈ K) :
    IsRight (addr a) (addr b) ↔ pre.idxOf a < pre.idxOf b ∧ post.idxOf a < post.idxOf b := by
  have gen : ∀ {R : V → V → Prop} {l : List V}, l.Pairwise R → (∀ a, ¬ R a a) → (∀ a b, R a b → ¬ R b a) →
      a ∈ l → b ∈ l → (R a b ↔ l.idxOf a < l.idxOf b) := by
    intro R l hl hir has ha' hb'
    have key : ∀ {a b : V}, a ∈ l → b ∈ l → l.idxOf a < l.idxOf b → R a b := by
      intro a b ha hb hlt
      have := List.pairwise_iff_getElem.1 hl (l.idxOf a) (l.idxOf b) (List.idxOf_lt_length_iff.2 ha)
        (List.idxOf_lt_length_iff.2 hb) hlt
      simpa [List.getElem_idxOf] using this
    refine ⟨fun h => ?_, key ha' hb'⟩
    rcases lt_trichotomy (l.idxOf a) (l.idxOf b) with h' | h' | h'
    · exact h'
    · have e : a = b := (List.idxOf_inj ha').1 h'
      subst e
      exact absurd h (hir _)
    · exact absurd (key hb' ha' h') (has _ _ h)
  rw [isRight_iff_pre_post]
  have h₁ := gen hR.pre_sorted (fun a => lt_irrefl _) (fun a b h => lt_asymm h) ((hR.pre_mem a).2 ha)
    ((hR.pre_mem b).2 hb)
  have h₂ := gen hR.post_sorted (fun a => PostLt.irrefl _) (fun a b h => h.asymm) ((hR.post_mem a).2 ha)
    ((hR.post_mem b).2 hb)
  rw [h₁, h₂]

end Fact1

end PlanarMatching.DagSearch
