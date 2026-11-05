import SsspFlow.LabelOracle
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.Int.ConditionallyCompleteOrder

/-!
# Walks with integer weights

* `Walk.zw`, `Walk.len`, `Walk.cnt`: the weight of a walk under integer weights, its number of arcs,
  and the number of its arcs with a property. `Walk.lift` moves a walk to a larger arc relation.
* `Walk.exists_nodup_le`: if closed walks have nonnegative weight, every walk can be replaced by one
  without repeated vertices that is not heavier and not longer. Such a walk has fewer arcs than there
  are vertices (`Walk.len_lt_card`).
* `Congest.walkZ_iff`: the walks of `Net.NegSpec` are the walks along the arcs of finite weight.
* `Congest.zdist`: the least value of an integer offset plus the length of a walk, for natural
  lengths, and its relation to `ndsrc` (`Congest.ndsrc_shift`).
* `Congest.dsrc_restrict`, `Congest.exists_walk_le_of_dist`: lengths `⊤` outside a set of arcs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal
open Cslib.Congest

namespace SsspFlow

namespace Walk

variable {V : Type} {adj : V → V → Prop}

/-- The weight of a walk under integer weights. -/
def zw (y : V → V → ℤ) : {a b : V} → Walk adj a b → ℤ
  | _, _, nil _ => 0
  | _, _, @cons _ _ a m _ _ p => y a m + p.zw y

/-- The number of arcs of a walk. -/
def len : {a b : V} → Walk adj a b → ℕ
  | _, _, nil _ => 0
  | _, _, cons _ p => p.len + 1

open Classical in
/-- The number of arcs of a walk with the property `P`. -/
noncomputable def cnt (P : V → V → Prop) : {a b : V} → Walk adj a b → ℕ
  | _, _, nil _ => 0
  | _, _, @cons _ _ a m _ _ p => (if P a m then 1 else 0) + p.cnt P

/-- A walk along a smaller arc relation as a walk along a larger one. -/
def lift {adj' : V → V → Prop} (h : ∀ a b, adj a b → adj' a b) :
    {a b : V} → Walk adj a b → Walk adj' a b
  | _, _, nil a => nil a
  | _, _, cons e p => cons (h _ _ e) (lift h p)

section Basic

variable (y : V → V → ℤ)

@[simp] lemma zw_nil (a : V) : (nil a : Walk adj a a).zw y = 0 := rfl

@[simp] lemma zw_cons {a b c : V} (e : adj a b) (p : Walk adj b c) :
    (cons e p).zw y = y a b + p.zw y := rfl

@[simp] lemma len_nil (a : V) : (nil a : Walk adj a a).len = 0 := rfl

@[simp] lemma len_cons {a b c : V} (e : adj a b) (p : Walk adj b c) :
    (cons e p).len = p.len + 1 := rfl

@[simp] lemma cnt_nil (P : V → V → Prop) (a : V) : (nil a : Walk adj a a).cnt P = 0 := rfl

open Classical in
lemma cnt_cons (P : V → V → Prop) {a b c : V} (e : adj a b) (p : Walk adj b c) :
    (cons e p).cnt P = (if P a b then 1 else 0) + p.cnt P := rfl

lemma append_cons {a b c d : V} (e : adj a b) (p : Walk adj b c) (q : Walk adj c d) :
    (cons e p).append q = cons e (p.append q) := rfl

lemma zw_append : ∀ {a b c : V} (p : Walk adj a b) (q : Walk adj b c),
    (p.append q).zw y = p.zw y + q.zw y
  | _, _, _, nil _, q => by simp [append]
  | _, _, _, cons e p, q => by rw [append_cons, zw_cons, zw_cons, zw_append p q, add_assoc]

lemma len_append : ∀ {a b c : V} (p : Walk adj a b) (q : Walk adj b c),
    (p.append q).len = p.len + q.len
  | _, _, _, nil _, q => by simp [append]
  | _, _, _, cons e p, q => by
    rw [append_cons, len_cons, len_cons, len_append p q]
    omega

lemma cnt_append (P : V → V → Prop) : ∀ {a b c : V} (p : Walk adj a b) (q : Walk adj b c),
    (p.append q).cnt P = p.cnt P + q.cnt P
  | _, _, _, nil _, q => by simp [append]
  | _, _, _, cons e p, q => by
    rw [append_cons, cnt_cons, cnt_cons, cnt_append P p q, Nat.add_assoc]

lemma support_length : ∀ {a b : V} (p : Walk adj a b), p.support.length = p.len + 1
  | _, _, nil _ => rfl
  | _, _, cons e p => by simp [support_length p]

lemma cnt_le_len (P : V → V → Prop) : ∀ {a b : V} (p : Walk adj a b), p.cnt P ≤ p.len
  | _, _, nil _ => le_rfl
  | _, _, cons e p => by
    rw [cnt_cons, len_cons]
    have := cnt_le_len P p
    split_ifs <;> omega

/-- Counting a larger property along the arcs gives at least as much. -/
lemma cnt_mono {P P' : V → V → Prop} (h : ∀ a b, adj a b → P a b → P' a b) :
    ∀ {a b : V} (p : Walk adj a b), p.cnt P ≤ p.cnt P'
  | _, _, nil _ => le_rfl
  | _, _, @cons _ _ a m _ e p => by
    rw [cnt_cons, cnt_cons]
    have := cnt_mono h p
    split_ifs with h₁ h₂ <;> first | omega | exact absurd (h _ _ e h₁) h₂

lemma zw_red (φ : V → ℤ) : ∀ {a b : V} (p : Walk adj a b),
    p.zw (fun a b => y a b + φ a - φ b) = p.zw y + φ a - φ b
  | _, _, nil _ => by simp
  | _, _, cons e p => by
    rw [zw_cons, zw_cons, zw_red φ p]
    ring

lemma zw_nonneg (h : ∀ a b, adj a b → 0 ≤ y a b) : ∀ {a b : V} (p : Walk adj a b), 0 ≤ p.zw y
  | _, _, nil _ => le_rfl
  | _, _, cons e p => by
    rw [zw_cons]
    have := zw_nonneg h p
    have := h _ _ e
    omega

lemma neg_len_le_zw (h : ∀ a b, adj a b → -1 ≤ y a b) :
    ∀ {a b : V} (p : Walk adj a b), -(p.len : ℤ) ≤ p.zw y
  | _, _, nil _ => by simp
  | _, _, cons e p => by
    rw [zw_cons, len_cons]
    have := neg_len_le_zw h p
    have := h _ _ e
    omega

lemma zw_le_pos : ∀ {a b : V} (p : Walk adj a b), p.zw y ≤ p.zw (fun a b => max (y a b) 0)
  | _, _, nil _ => le_rfl
  | _, _, @cons _ _ a m _ e p => by
    rw [zw_cons, zw_cons]
    have := zw_le_pos p
    have := le_max_left (y a m) 0
    omega

lemma zw_pos_le (h : ∀ a b, adj a b → -1 ≤ y a b) :
    ∀ {a b : V} (p : Walk adj a b), p.zw (fun a b => max (y a b) 0) ≤ p.zw y + p.len
  | _, _, nil _ => by simp
  | _, _, @cons _ _ a m _ e p => by
    rw [zw_cons, zw_cons, len_cons]
    have := zw_pos_le h p
    have := h _ _ e
    have : max (y a m) 0 ≤ y a m + 1 := max_le (by omega) (by omega)
    omega

end Basic

section Lift

variable {adj' : V → V → Prop} (h : ∀ a b, adj a b → adj' a b)

@[simp] lemma zw_lift (y : V → V → ℤ) : ∀ {a b : V} (p : Walk adj a b), (p.lift h).zw y = p.zw y
  | _, _, nil _ => rfl
  | _, _, cons e p => by simp [lift, zw_lift y p]

@[simp] lemma len_lift : ∀ {a b : V} (p : Walk adj a b), (p.lift h).len = p.len
  | _, _, nil _ => rfl
  | _, _, cons e p => by simp [lift, len_lift p]

@[simp] lemma cnt_lift (P : V → V → Prop) : ∀ {a b : V} (p : Walk adj a b),
    (p.lift h).cnt P = p.cnt P
  | _, _, nil _ => rfl
  | _, _, cons e p => by
    show (cons (h _ _ e) (p.lift h)).cnt P = (cons e p).cnt P
    rw [cnt_cons, cnt_cons, cnt_lift P p]

@[simp] lemma support_lift : ∀ {a b : V} (p : Walk adj a b), (p.lift h).support = p.support
  | _, _, nil _ => rfl
  | _, _, cons e p => by simp [lift, support_lift p]

@[simp] lemma nwt_lift (x : V → V → ℕ) : ∀ {a b : V} (p : Walk adj a b),
    (p.lift h).nwt x = p.nwt x
  | _, _, nil _ => rfl
  | _, _, cons e p => by simp [lift, nwt_lift x p]

@[simp] lemma wt_lift (w : V → V → ℝ≥0∞) : ∀ {a b : V} (p : Walk adj a b),
    (p.lift h).wt w = p.wt w
  | _, _, nil _ => rfl
  | _, _, cons e p => by simp [lift, wt_lift w p]

end Lift

section Nodup

variable (y : V → V → ℤ)

/-- A walk cut at one of its vertices `a`: a walk to `a` and a walk from `a`. -/
lemma exists_cut {a b c : V} (q : Walk adj b c) (ha : a ∈ q.support) :
    ∃ (s : Walk adj b a) (r : Walk adj a c), r.support.Sublist q.support ∧
      s.zw y + r.zw y = q.zw y ∧ s.len + r.len = q.len := by
  induction q with
  | nil b =>
    obtain rfl : a = b := by simpa using ha
    exact ⟨nil _, nil _, List.Sublist.refl _, by simp, by simp⟩
  | @cons x z u e q ih =>
    by_cases hax : a = x
    · subst hax
      exact ⟨nil _, cons e q, List.Sublist.refl _, by simp, by simp⟩
    · obtain ⟨s, r, h₁, h₂, h₃⟩ := ih (by simpa [hax] using ha)
      refine ⟨cons e s, r, h₁.cons _, ?_, ?_⟩
      · rw [zw_cons, zw_cons, ← h₂, add_assoc]
      · rw [len_cons, len_cons, ← h₃]
        omega

/-- **Shortcuts.** If closed walks have nonnegative weight, every walk can be replaced by one without
repeated vertices that is not heavier and not longer. -/
lemma exists_nodup_le [DecidableEq V] (hC : ∀ a (C : Walk adj a a), 0 ≤ C.zw y) :
    ∀ {a b : V} (p : Walk adj a b), ∃ q : Walk adj a b, q.support.Nodup ∧ q.zw y ≤ p.zw y ∧
      q.len ≤ p.len
  | _, _, nil a => ⟨nil a, by simp, le_rfl, le_rfl⟩
  | a, _, cons e p => by
    obtain ⟨q, hq, hw, hl⟩ := exists_nodup_le hC p
    by_cases ha : a ∈ q.support
    · obtain ⟨s, r, h₁, h₂, h₃⟩ := exists_cut y q ha
      have hc := hC a (cons e s)
      rw [zw_cons] at hc
      refine ⟨r, h₁.nodup hq, ?_, ?_⟩
      · rw [zw_cons]
        omega
      · rw [len_cons]
        omega
    · refine ⟨cons e q, by simp [ha, hq], ?_, ?_⟩
      · rw [zw_cons, zw_cons]
        omega
      · rw [len_cons, len_cons]
        omega

/-- A walk without repeated vertices has fewer arcs than there are vertices. -/
lemma len_lt_card [Fintype V] {a b : V} (p : Walk adj a b) (h : p.support.Nodup) :
    p.len < Fintype.card V := by
  have := h.length_le_card
  rw [support_length] at this
  omega

end Nodup

end Walk

namespace Congest

section WalkZ

variable {V : Type}

/-- The arcs with a finite weight. -/
abbrev zArc (adj : V → V → Prop) (w : V → V → Option ℤ) (a b : V) : Prop :=
  adj a b ∧ (w a b).isSome

/-- The weights as integers, `0` where there is none. -/
def zWt (w : V → V → Option ℤ) (a b : V) : ℤ := (w a b).getD 0

theorem zWt_of_eq {w : V → V → Option ℤ} {a b : V} {x : ℤ} (h : w a b = some x) : zWt w a b = x := by
  simp [zWt, h]

/-- The walks of `Net.NegSpec` are the walks along the arcs of finite weight. -/
theorem walkZ_iff {adj : V → V → Prop} {w : V → V → Option ℤ} {a b : V} {y : ℤ} :
    WalkZ adj w a b y ↔ ∃ p : Walk (zArc adj w) a b, p.zw (zWt w) = y := by
  constructor
  · intro h
    induction h with
    | nil a => exact ⟨.nil a, rfl⟩
    | @cons a b c x y hab hw _ ih =>
      obtain ⟨p, hp⟩ := ih
      exact ⟨.cons (And.intro hab (by simp [hw])) p, by rw [Walk.zw_cons, zWt_of_eq hw, hp]⟩
  · rintro ⟨p, rfl⟩
    induction p with
    | nil a => exact WalkZ.nil a
    | @cons a b c e p ih =>
      obtain ⟨hab, hs⟩ := e
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hs
      rw [Walk.zw_cons, zWt_of_eq hx]
      exact WalkZ.cons hab hx ih

end WalkZ

section ZDist

variable {V : Type} [Finite V] (adj : V → V → Prop) (len : V → V → ℕ) (o : V → ℤ)

/-- `min_a (o a + d(a, v))`: the least value of the offset of a start plus the length of a walk from
it, for integer offsets and natural lengths. -/
noncomputable def zdist (v : V) : ℤ := sInf {z | ∃ a, ∃ p : Walk adj a v, z = o a + p.nwt len}

variable {adj len o}

theorem zdist_bdd (v : V) : BddBelow {z | ∃ a, ∃ p : Walk adj a v, z = o a + p.nwt len} := by
  have : Nonempty V := ⟨v⟩
  obtain ⟨a₀, ha₀⟩ := Finite.exists_min o
  refine ⟨o a₀, ?_⟩
  rintro z ⟨a, p, rfl⟩
  have := ha₀ a
  omega

theorem zdist_le {a v : V} (p : Walk adj a v) : zdist adj len o v ≤ o a + p.nwt len :=
  csInf_le (zdist_bdd v) ⟨a, p, rfl⟩

theorem zdist_spec (v : V) : ∃ a, ∃ p : Walk adj a v, zdist adj len o v = o a + p.nwt len :=
  Int.csInf_mem (s := {z | ∃ a, ∃ p : Walk adj a v, z = o a + p.nwt len}) ⟨_, v, .nil v, rfl⟩
    (zdist_bdd v)

theorem zdist_le_off (v : V) : zdist adj len o v ≤ o v := by
  simpa using zdist_le (adj := adj) (len := len) (o := o) (Walk.nil v)

theorem zdist_triangle {a b : V} (h : adj a b) :
    zdist adj len o b ≤ zdist adj len o a + len a b := by
  obtain ⟨c, p, hp⟩ := zdist_spec (adj := adj) (len := len) (o := o) a
  have := zdist_le (adj := adj) (len := len) (o := o) (p.append (.cons h (.nil b)))
  rw [Walk.nwt_append] at this
  simp only [Walk.nwt_cons, Walk.nwt_nil] at this
  omega

theorem le_zdist {m : ℤ} (h : ∀ a, m ≤ o a) (v : V) : m ≤ zdist adj len o v := by
  obtain ⟨a, p, hp⟩ := zdist_spec (adj := adj) (len := len) (o := o) v
  rw [hp]
  have := h a
  omega

/-- The oracle computes `ndsrc` on natural offsets; shifted by `c`, it is `zdist`. -/
theorem ndsrc_shift (c : ℕ) (hc : ∀ a, 0 ≤ o a + c) (v : V) :
    (ndsrc adj len (fun a => (o a + c).toNat) v : ℤ) = zdist adj len o v + c := by
  apply le_antisymm
  · obtain ⟨a, p, hp⟩ := zdist_spec (adj := adj) (len := len) (o := o) v
    have h₁ : (((o a + c).toNat : ℕ) : ℤ) = o a + c := Int.toNat_of_nonneg (hc a)
    have h₂ := ndsrc_le (adj := adj) (x := len) (y := fun a => (o a + c).toNat) p
    have h₃ : ((ndsrc adj len (fun a => (o a + c).toNat) v : ℕ) : ℤ) ≤
        ((o a + c).toNat : ℤ) + (p.nwt len : ℤ) := by exact_mod_cast h₂
    omega
  · obtain ⟨a, p, hp⟩ := ndsrc_spec adj len (fun a => (o a + c).toNat) v
    have h₁ : (((o a + c).toNat : ℕ) : ℤ) = o a + c := Int.toNat_of_nonneg (hc a)
    have h₂ := zdist_le (adj := adj) (len := len) (o := o) p
    have h₃ : ((ndsrc adj len (fun a => (o a + c).toNat) v : ℕ) : ℤ) =
        ((o a + c).toNat : ℤ) + (p.nwt len : ℤ) := by exact_mod_cast hp
    omega

end ZDist

section Restrict

open Classical

/-- The lengths `len` on the arcs of `E` and `⊤` elsewhere. -/
noncomputable def restrictLen {V : Type} (E : V → V → Prop) (len : V → V → ℕ) (a b : V) : ℕ∞ :=
  if E a b then (len a b : ℕ∞) else ⊤

variable {V : Type} {adj E : V → V → Prop} (hE : ∀ a b, E a b → adj a b) (len : V → V → ℕ)

theorem wt_restrict : ∀ {a b : V} (p : Walk E a b),
    (p.lift hE).wt (lenTop (restrictLen E len)) = (p.nwt len : ℝ≥0∞)
  | _, _, .nil _ => by simp [Walk.lift]
  | _, _, .cons e p => by
    rw [show (Walk.cons e p).lift hE = .cons (hE _ _ e) (p.lift hE) from rfl, Walk.wt_cons,
      wt_restrict p, Walk.nwt_cons]
    simp [lenTop, restrictLen, e]

theorem exists_of_wt_ne_top : ∀ {a b : V} (p : Walk adj a b),
    p.wt (lenTop (restrictLen E len)) ≠ ⊤ →
      ∃ q : Walk E a b, (q.nwt len : ℝ≥0∞) = p.wt (lenTop (restrictLen E len))
  | _, _, .nil a, _ => ⟨.nil a, by simp⟩
  | _, _, @Walk.cons _ _ a m _ e p, hne => by
    rw [Walk.wt_cons] at hne ⊢
    have h₁ : lenTop (restrictLen E len) a m ≠ ⊤ := fun h' => hne (by rw [h', top_add])
    have h₂ : p.wt (lenTop (restrictLen E len)) ≠ ⊤ := fun h' => hne (by rw [h', add_top])
    have hEm : E a m := by
      by_contra hn
      exact h₁ (by simp [lenTop, restrictLen, hn])
    obtain ⟨q, hq⟩ := exists_of_wt_ne_top p h₂
    refine ⟨.cons hEm q, ?_⟩
    rw [Walk.nwt_cons, ← hq]
    simp [lenTop, restrictLen, hEm]

include hE in
/-- **Lengths `⊤` outside `E`.** The distance from the virtual source with finite offsets is the
natural distance along `E`. -/
theorem dsrc_restrict (y : V → ℕ) (v : V) :
    dsrc adj (lenTop (restrictLen E len)) (offTop fun a => (y a : ℕ∞)) v =
      (ndsrc E len y v : ℝ≥0∞) := by
  apply le_antisymm
  · obtain ⟨a, p, hp⟩ := ndsrc_spec E len y v
    refine (dsrc_le_walk _ _ (p.lift hE)).trans_eq ?_
    rw [wt_restrict hE len p, hp]
    simp [offTop]
  · refine le_dsrc fun a p => ?_
    by_cases hp : p.wt (lenTop (restrictLen E len)) = ⊤
    · rw [hp, add_top]
      exact le_top
    · obtain ⟨q, hq⟩ := exists_of_wt_ne_top len p hp
      rw [← hq]
      have := ndsrc_le (adj := E) (x := len) (y := y) q
      have h' : (ndsrc E len y v : ℝ≥0∞) ≤ ((y a + q.nwt len : ℕ) : ℝ≥0∞) := by exact_mod_cast this
      simpa [offTop] using h'

/-- A distance of at most `d` with lengths `⊤` outside `E` is the length of a walk along `E`. -/
theorem exists_walk_le_of_dist {u v : V} {d : ℕ}
    (h : dist adj (lenTop (restrictLen E len)) Set.univ u v ≤ d) :
    ∃ q : Walk E u v, q.nwt len ≤ d := by
  by_contra hq
  push Not at hq
  have : ((d + 1 : ℕ) : ℝ≥0∞) ≤ dist adj (lenTop (restrictLen E len)) Set.univ u v := by
    refine le_iInf₂ fun p _ => ?_
    by_cases hp : p.wt (lenTop (restrictLen E len)) = ⊤
    · rw [hp]
      exact le_top
    · obtain ⟨q, hq'⟩ := exists_of_wt_ne_top len p hp
      rw [← hq']
      have := hq q
      exact_mod_cast (show d + 1 ≤ q.nwt len by omega)
  have h2 := this.trans h
  have h3 : d + 1 ≤ d := by exact_mod_cast h2
  omega

end Restrict

end Congest

end SsspFlow
