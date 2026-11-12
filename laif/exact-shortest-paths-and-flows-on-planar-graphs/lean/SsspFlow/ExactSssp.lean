import SsspFlow.Boost
import SsspFlow.LabelOracle

/-!
# Exact shortest paths in the message model

`exactSsspBound`: `LabelHypothesis`, `AggBox` and `SmoothingBox` give `ExactSsspBound`, the Exact SSSP
Theorem of the paper: distances from a virtual source and parents in a shortest-path forest, in
`Õ(D)` rounds, on planar networks with lengths and offsets of polynomial size.

The algorithm follows the paper with one change of units. A length is replaced by
`(n + 1) ℓ + 1` and an offset by `(n + 1) φ`, which makes shortest walks shortest for the old
lengths and gives a parent by a strict decrease. `⊤` is replaced by a large `M`. Then all lengths
are multiplied by `U`, and iteration `i` calls the smooth oracle on `Λ_i + 1`, with an answer `d`. With
`e = ⌈d / 4⌉`, the new lengths are `Λ_{i+1}(a, b) = Λ_i(a, b) + 1 + e(a) - e(b)`, also on the arcs from
the virtual source. These are natural numbers, since rounding up to multiples of `4` keeps the
smoothness. In units of `1 / U`, this is a run of `Boost.Run` with `α = 2` and `η = 1 / U`.

* `walk_scale`, `scale_top`, `scale_finite`: distances under the new lengths.
* `exactSpec_of_ndsrc`: exact distances under the new lengths give the output of the theorem.
* `boost_dist_le`, `le_boost_dist`: the distances of `Boost.dist` on the network with a virtual source.
* `it_main`: the iterations give the exact distance.
* `itRel_iter`: the data held by the nodes are the data of the iterations.
* `exactAlg_ok`: the algorithm is correct, given the contract of the oracle.
-/

set_option autoImplicit false

open scoped ENNReal
open Cslib.Congest

namespace SsspFlow.Congest

/-! ### New lengths -/

section Scale

variable {V : Type} {adj : V → V → Prop}

/-- A length scaled by `S` and raised by `1`, with `⊤` replaced by `M`. -/
def scaleLen (S M : ℕ) (x : ℕ∞) : ℕ := if x = ⊤ then M else S * x.toNat + 1

/-- An offset scaled by `S`, with `⊤` replaced by `M`. -/
def scaleOff (S M : ℕ) (x : ℕ∞) : ℕ := if x = ⊤ then M else S * x.toNat

@[simp] theorem scaleLen_top (S M : ℕ) : scaleLen S M ⊤ = M := by simp [scaleLen]

@[simp] theorem scaleLen_coe (S M m : ℕ) : scaleLen S M m = S * m + 1 := by simp [scaleLen]

@[simp] theorem scaleOff_top (S M : ℕ) : scaleOff S M ⊤ = M := by simp [scaleOff]

@[simp] theorem scaleOff_coe (S M m : ℕ) : scaleOff S M m = S * m := by simp [scaleOff]

/-- The new lengths. -/
def lenScale (S M : ℕ) (ℓ : V → V → ℕ∞) : V → V → ℕ := fun a b => scaleLen S M (ℓ a b)

/-- The new offsets. -/
def offScale (S M : ℕ) (φ : V → ℕ∞) : V → ℕ := fun v => scaleOff S M (φ v)

/-- A walk has an arc of length `⊤`, or its new length is determined by its length and its arcs. -/
theorem walk_scale (S M : ℕ) (ℓ : V → V → ℕ∞) : ∀ {a b : V} (p : Walk adj a b),
    (M ≤ p.nwt (lenScale S M ℓ) ∧ p.wt (lenTop ℓ) = ⊤) ∨
      ∃ k : ℕ, p.wt (lenTop ℓ) = k ∧ p.nwt (lenScale S M ℓ) + 1 = S * k + p.support.length
  | _, _, .nil a => .inr ⟨0, by simp, by simp⟩
  | _, _, @Walk.cons _ _ a m _ e p => by
    simp only [Walk.nwt_cons, Walk.wt_cons, Walk.support_cons, List.length_cons]
    by_cases hℓ : ℓ a m = ⊤
    · left
      have h1 : lenScale S M ℓ a m = M := by simp [lenScale, hℓ]
      have h2 : lenTop ℓ a m = ⊤ := by simp [lenTop, hℓ]
      exact ⟨by omega, by simp [h2]⟩
    · obtain ⟨m', hm'⟩ := ENat.ne_top_iff_exists.1 hℓ
      have h1 : lenScale S M ℓ a m = S * m' + 1 := by simp [lenScale, ← hm']
      have h2 : lenTop ℓ a m = (m' : ℝ≥0∞) := by simp [lenTop, ← hm']
      rcases walk_scale S M ℓ p with ⟨h3, h4⟩ | ⟨k, h3, h4⟩
      · left
        exact ⟨by omega, by simp [h4]⟩
      · right
        refine ⟨m' + k, by rw [h2, h3]; push_cast; rfl, ?_⟩
        rw [h1, Nat.mul_add]
        omega

/-- An unreachable node has a new distance of at least `M`. -/
theorem scale_top {S M : ℕ} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {v : V}
    (h : dsrc adj (lenTop ℓ) (offTop φ) v = ⊤) :
    M ≤ ndsrc adj (lenScale S M ℓ) (offScale S M φ) v := by
  obtain ⟨a, p, hp⟩ := ndsrc_spec adj (lenScale S M ℓ) (offScale S M φ) v
  rw [hp]
  by_cases hφ : φ a = ⊤
  · have : offScale S M φ a = M := by simp [offScale, hφ]
    omega
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hφ
    rcases walk_scale S M ℓ p with ⟨h3, -⟩ | ⟨k, h3, -⟩
    · omega
    · have h4 := dsrc_le_walk (lenTop ℓ) (offTop φ) p
      have h5 : offTop φ a = (m : ℝ≥0∞) := by simp [offTop, ← hm]
      rw [h, h3, h5] at h4
      exact absurd (top_le_iff.1 h4)
        (ENNReal.add_ne_top.2 ⟨ENNReal.natCast_ne_top _, ENNReal.natCast_ne_top _⟩)

/-- A node at distance `d` has a new distance between `S d` and `S d + |V| - 1`. -/
theorem scale_finite [Fintype V] [DecidableEq V] {S M d : ℕ} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} {v : V}
    (h : dsrc adj (lenTop ℓ) (offTop φ) v = d) (hM : S * d + Fintype.card V ≤ M) :
    S * d ≤ ndsrc adj (lenScale S M ℓ) (offScale S M φ) v ∧
      ndsrc adj (lenScale S M ℓ) (offScale S M φ) v + 1 ≤ S * d + Fintype.card V := by
  have hup : ndsrc adj (lenScale S M ℓ) (offScale S M φ) v + 1 ≤ S * d + Fintype.card V := by
    have hlt : dsrc adj (lenTop ℓ) (offTop φ) v < ((d + 1 : ℕ) : ℝ≥0∞) := by
      rw [h]
      exact_mod_cast Nat.lt_succ_self d
    obtain ⟨a, p, hp⟩ := dsrc_lt_iff.1 hlt
    obtain ⟨q, hq, hw⟩ := Walk.exists_nodup (lenTop ℓ) p
    have hq' : offTop φ a + q.wt (lenTop ℓ) < ((d + 1 : ℕ) : ℝ≥0∞) :=
      lt_of_le_of_lt (by gcongr) hp
    have hφ : φ a ≠ ⊤ := fun ht => by
      have h0 : offTop φ a = ⊤ := by simp [offTop, ht]
      rw [h0, top_add] at hq'
      exact absurd hq' (by simp)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hφ
    have h5 : offTop φ a = (m : ℝ≥0∞) := by simp [offTop, ← hm]
    rcases walk_scale S M ℓ q with ⟨-, h3⟩ | ⟨k, h3, h4⟩
    · rw [h3, add_top] at hq'
      exact absurd hq' (by simp)
    · rw [h5, h3, ← Nat.cast_add] at hq'
      have h6 : m + k < d + 1 := by exact_mod_cast hq'
      have h7 := ndsrc_le (x := lenScale S M ℓ) (y := offScale S M φ) q
      have h8 : offScale S M φ a = S * m := by simp [offScale, ← hm]
      have h9 : q.support.length ≤ Fintype.card V := hq.length_le_card
      have h10 : S * (m + k) ≤ S * d := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add] at h10
      omega
  refine ⟨?_, hup⟩
  obtain ⟨a', p', hp'⟩ := ndsrc_spec adj (lenScale S M ℓ) (offScale S M φ) v
  by_cases hφ : φ a' = ⊤
  · have : offScale S M φ a' = M := by simp [offScale, hφ]
    omega
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hφ
    have h8 : offScale S M φ a' = S * m := by simp [offScale, ← hm]
    rcases walk_scale S M ℓ p' with ⟨h3, -⟩ | ⟨k, h3, h4⟩
    · omega
    · have h5 := dsrc_le_walk (lenTop ℓ) (offTop φ) p'
      have h0 : offTop φ a' = (m : ℝ≥0∞) := by simp [offTop, ← hm]
      rw [h, h3, h0, ← Nat.cast_add] at h5
      have h6 : d ≤ m + k := by exact_mod_cast h5
      have h10 : S * d ≤ S * (m + k) := Nat.mul_le_mul_left _ h6
      rw [Nat.mul_add] at h10
      have h11 : 1 ≤ p'.support.length := List.length_pos_of_mem p'.start_mem
      omega

/-- A distance from the virtual source is `⊤` or a natural number. -/
theorem dsrc_top_or_nat (adj : V → V → Prop) (ℓ : V → V → ℕ∞) (φ : V → ℕ∞) (v : V) :
    dsrc adj (lenTop ℓ) (offTop φ) v = ⊤ ∨ ∃ d : ℕ, dsrc adj (lenTop ℓ) (offTop φ) v = d := by
  by_cases hT : dsrc adj (lenTop ℓ) (offTop φ) v = ⊤
  · exact .inl hT
  right
  have val : ∀ {a : V} (p : Walk adj a v), offTop φ a + p.wt (lenTop ℓ) = ⊤ ∨
      ∃ k : ℕ, offTop φ a + p.wt (lenTop ℓ) = k := by
    intro a p
    by_cases hφ : φ a = ⊤
    · left
      simp [offTop, hφ]
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hφ
      have h5 : offTop φ a = (m : ℝ≥0∞) := by simp [offTop, ← hm]
      rcases walk_scale 0 0 ℓ p with ⟨-, h3⟩ | ⟨k, h3, -⟩
      · left
        rw [h3, add_top]
      · right
        exact ⟨m + k, by rw [h5, h3]; push_cast; rfl⟩
  obtain ⟨a₀, p₀, hp₀⟩ := dsrc_lt_iff.1 (lt_top_iff_ne_top.2 hT)
  obtain ⟨k₀, hk₀⟩ := (val p₀).resolve_left hp₀.ne
  have hne : {k : ℕ | ∃ a, ∃ p : Walk adj a v, offTop φ a + p.wt (lenTop ℓ) = k}.Nonempty :=
    ⟨k₀, a₀, p₀, hk₀⟩
  obtain ⟨a₁, p₁, hp₁⟩ := Nat.sInf_mem hne
  refine ⟨_, le_antisymm ((dsrc_le_walk _ _ p₁).trans_eq hp₁) (le_dsrc fun a p => ?_)⟩
  rcases val p with h | ⟨k, hk⟩
  · rw [h]
    exact le_top
  · rw [hk]
    exact Nat.cast_le.2 (Nat.sInf_le ⟨a, p, hk⟩)

end Scale

/-! ### The output -/

/-- The output distance from a new distance. -/
def dOut (S M D : ℕ) : ℕ∞ := if M ≤ D then ⊤ else ((D / S : ℕ) : ℕ∞)

open Classical in
/-- The output parent from a new distance, the offset, the lengths of the arcs that enter the node and
the new distances of its neighbours. -/
noncomputable def pOut {V : Type} (M off : ℕ) (inLen : V → ℕ) (D : ℕ) (recv : V → Option ℕ) :
    Option V :=
  if M ≤ D ∨ D = off then none
  else if h : ∃ p x, recv p = some x ∧ x + inLen p = D then some h.choose else none

/-- Exact new distances give the distances and a shortest-path forest. -/
theorem exactSpec_of_ndsrc {V : Type} [Fintype V] [DecidableEq V] {N : Net V} {m W S M : ℕ}
    {ℓ : V → V → ℕ∞} {φ : V → ℕ∞} (hV : OracleValid N m W ℓ φ) (hS : S = Fintype.card V + 1)
    (hM : S * (Fintype.card V * W) + Fintype.card V ≤ M) (inL : V → V → ℕ)
    (hinL : ∀ v p, N.G.Adj p v → inL v p = lenScale S M ℓ p v) :
    N.ExactSpec ℓ φ (fun v =>
      (dOut S M (ndsrc N.G.Adj (lenScale S M ℓ) (offScale S M φ) v),
        pOut M (offScale S M φ v) (inL v) (ndsrc N.G.Adj (lenScale S M ℓ) (offScale S M φ) v)
          (fun p => if N.G.Adj p v then
            some (ndsrc N.G.Adj (lenScale S M ℓ) (offScale S M φ) p) else none))) := by
  set D := ndsrc N.G.Adj (lenScale S M ℓ) (offScale S M φ) with hD
  have hbound : ∀ v (d : ℕ), N.dsrcTop ℓ φ v = d → S * d + Fintype.card V ≤ M := by
    intro v d hd
    have h1 := dsrcTop_le hV (by rw [hd]; exact ENNReal.natCast_ne_top _)
    rw [hd] at h1
    have h2 : d ≤ Fintype.card V * W := by exact_mod_cast h1
    have h3 := Nat.mul_le_mul_left S h2
    omega
  have hreach : ∀ v, D v < M → ∃ d : ℕ, N.dsrcTop ℓ φ v = d ∧ S * d ≤ D v ∧
      D v + 1 ≤ S * d + Fintype.card V ∧ D v / S = d := by
    intro v hv
    rcases dsrc_top_or_nat N.G.Adj ℓ φ v with h | ⟨d, h⟩
    · exact absurd (scale_top (S := S) (M := M) h) (not_le.2 hv)
    · obtain ⟨h1, h2⟩ : S * d ≤ D v ∧ D v + 1 ≤ S * d + Fintype.card V :=
        scale_finite h (hbound v d h)
      refine ⟨d, h, h1, h2, Nat.div_eq_of_lt_le ?_ ?_⟩
      · rw [mul_comm]
        exact h1
      · have : (d + 1) * S = S * d + S := by ring
        omega
  have hfar : ∀ v, M ≤ D v → N.dsrcTop ℓ φ v = ⊤ := by
    intro v hv
    rcases dsrc_top_or_nat N.G.Adj ℓ φ v with h | ⟨d, h⟩
    · exact h
    · obtain ⟨-, h2⟩ : S * d ≤ D v ∧ D v + 1 ≤ S * d + Fintype.card V :=
        scale_finite h (hbound v d h)
      have := hbound v d h
      omega
  have hSpos : 0 < S := by omega
  refine ⟨fun v => ?_, D, fun v => ?_⟩
  · simp only [dOut]
    by_cases h1 : M ≤ D v
    · rw [ite_eq_left h1, hfar v h1]
      simp
    · obtain ⟨d, hd, -, -, hdiv⟩ := hreach v (not_le.1 h1)
      rw [ite_eq_right h1, hdiv, hd]
      simp
  · simp only
    by_cases h1 : M ≤ D v
    · right
      refine ⟨by simp [pOut, h1], .inl (by simp [dOut, h1])⟩
    by_cases h2 : D v = offScale S M φ v
    · right
      refine ⟨by simp [pOut, h2], .inr ?_⟩
      have hφ : φ v ≠ ⊤ := fun ht => h1 (by rw [h2]; simp [offScale, ht])
      obtain ⟨m', hm⟩ := ENat.ne_top_iff_exists.1 hφ
      have h3 : offScale S M φ v = S * m' := by simp [offScale, ← hm]
      simp only [dOut]
      rw [ite_eq_right h1, h2, h3, Nat.mul_div_cancel_left _ hSpos, ← hm]
    · left
      have hex : ∃ p x, (if N.G.Adj p v then some (D p) else none) = some x ∧
          x + inL v p = D v := by
        rcases ndsrc_bellman (adj := N.G.Adj) (x := lenScale S M ℓ) (y := offScale S M φ) v with
          h | ⟨u, hu, hE⟩
        · exact absurd h h2
        · exact ⟨u, D u, by simp [hu], by rw [hinL v u hu]; exact hE⟩
      have hp : pOut M (offScale S M φ v) (inL v) (D v)
          (fun p => if N.G.Adj p v then some (D p) else none) = some hex.choose := by
        unfold pOut
        rw [ite_eq_right (by tauto), dite_eq_left hex]
      obtain ⟨x, hx, hsum⟩ := hex.choose_spec
      generalize hex.choose = p₀ at hp hx hsum
      have hadj : N.G.Adj p₀ v := by
        by_contra hn
        simp [hn] at hx
      have hxD : x = D p₀ := by simpa [hadj] using hx.symm
      subst hxD
      rw [hinL v p₀ hadj] at hsum
      have hℓ : ℓ p₀ v ≠ ⊤ := fun ht => by
        have : lenScale S M ℓ p₀ v = M := by simp [lenScale, ht]
        omega
      obtain ⟨m', hm⟩ := ENat.ne_top_iff_exists.1 hℓ
      have hsc : lenScale S M ℓ p₀ v = S * m' + 1 := by simp [lenScale, ← hm]
      rw [hsc] at hsum
      have hp₀ : D p₀ < M := by omega
      obtain ⟨d₀, -, hd₁, hd₂, hdiv⟩ := hreach p₀ hp₀
      have hdv : D v / S = d₀ + m' := by
        refine Nat.div_eq_of_lt_le ?_ ?_
        · have : (d₀ + m') * S = S * d₀ + S * m' := by ring
          omega
        · have : (d₀ + m' + 1) * S = S * d₀ + S * m' + S := by ring
          omega
      refine ⟨p₀, hp, hadj, by simp [dOut, h1], ?_, by omega⟩
      simp only [dOut]
      rw [ite_eq_right h1, ite_eq_right (not_le.2 hp₀), hdiv, hdv, ← hm]
      push_cast
      rfl

/-! ### The network with a virtual source -/

section Virtual

variable {V : Type} {adj : V → V → Prop}

/-- The arcs of the network with the virtual source `none`. -/
inductive OArc (adj : V → V → Prop) : Option V → Option V → Type
  | src (v : V) : OArc adj none (some v)
  | edge {a b : V} (h : adj a b) : OArc adj (some a) (some b)

/-- The lengths of these arcs. -/
def oLen (x : V → V → ℕ) (y : V → ℕ) : ∀ a b, OArc adj a b → ℕ
  | _, _, .src v => y v
  | _, _, @OArc.edge _ _ a b _ => x a b

/-- A walk of the network in the network with the virtual source. -/
def toO : ∀ {a b : V}, Walk adj a b → FaceDisjoint.Walk (OArc adj) (some a) (some b)
  | _, _, .nil a => .nil (some a)
  | _, _, .cons e p => .cons (.edge e) (toO p)

theorem wt_toO (x : V → V → ℕ) (y : V → ℕ) (c : ℝ) : ∀ {a b : V} (p : Walk adj a b),
    (toO p).wt (fun a b e => (oLen x y a b e : ℝ) * c) = (p.nwt x : ℝ) * c
  | _, _, .nil a => by simp [toO]
  | _, _, @Walk.cons _ _ a m _ e p => by
    show (FaceDisjoint.Walk.cons (OArc.edge e) (toO p)).wt _ = _
    rw [FaceDisjoint.Walk.wt_cons, wt_toO x y c p, Walk.nwt_cons]
    simp only [oLen]
    push_cast
    ring

/-- The distance as a potential on the network with the virtual source. -/
noncomputable def oPot (adj : V → V → Prop) (x : V → V → ℕ) (y : V → ℕ) (c : ℝ) : Option V → ℝ
  | none => 0
  | some v => (ndsrc adj x y v : ℝ) * c

theorem oPot_wt {x : V → V → ℕ} {y : V → ℕ} {c : ℝ} (hc : 0 ≤ c) : ∀ {a b : Option V}
    (p : FaceDisjoint.Walk (OArc adj) a b),
    oPot adj x y c b ≤ oPot adj x y c a + p.wt (fun a b e => (oLen x y a b e : ℝ) * c)
  | _, _, .nil a => by simp
  | _, _, @FaceDisjoint.Walk.cons _ _ a m _ e p => by
    rw [FaceDisjoint.Walk.wt_cons]
    have ih := oPot_wt (x := x) (y := y) hc p
    have harc : oPot adj x y c m ≤ oPot adj x y c a + (oLen x y a m e : ℝ) * c := by
      cases e with
      | src v =>
        simp only [oPot, oLen, zero_add]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast ndsrc_le_off v) hc
      | edge h =>
        simp only [oPot, oLen]
        rw [← add_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast ndsrc_triangle h) hc
    linarith

theorem boost_dist_le (x : V → V → ℕ) (y : V → ℕ) {c : ℝ} (hc : 0 ≤ c) (v : V) :
    Boost.dist none (fun a b (e : OArc adj a b) => (oLen x y a b e : ℝ) * c) (some v) ≤
      (ndsrc adj x y v : ℝ) * c := by
  obtain ⟨a, p, hp⟩ := ndsrc_spec adj x y v
  have h := Boost.dist_le (fun a b (e : OArc adj a b) => (oLen x y a b e : ℝ) * c)
    (fun _ _ _ => mul_nonneg (Nat.cast_nonneg _) hc) (FaceDisjoint.Walk.cons (OArc.src a) (toO p))
  rw [FaceDisjoint.Walk.wt_cons, wt_toO] at h
  refine h.trans_eq ?_
  rw [hp]
  simp only [oLen]
  push_cast
  ring

theorem le_boost_dist (x : V → V → ℕ) (y : V → ℕ) {c : ℝ} (hc : 0 ≤ c) (v : V) :
    (ndsrc adj x y v : ℝ) * c ≤
      Boost.dist none (fun a b (e : OArc adj a b) => (oLen x y a b e : ℝ) * c) (some v) := by
  have : Nonempty (FaceDisjoint.Walk (OArc adj) none (some v)) :=
    ⟨.cons (.src v) (.nil _)⟩
  refine Boost.le_dist _ fun p => ?_
  have h := oPot_wt (x := x) (y := y) hc p
  simpa [oPot] using h

/-- The answers of an iteration as the estimates of `Boost.Run`. -/
def oDt (e : V → ℕ) (c : ℝ) : Option V → ℝ
  | none => 0
  | some v => ((2 * e v : ℕ) : ℝ) * c

end Virtual

/-! ### The iterations -/

section Iter

variable {V : Type} [Fintype V] [DecidableEq V] {σ : Type} {Bq B : ℕ}

/-- The lengths, offsets and sums of the estimates in one iteration. -/
structure ItGlobal (V : Type) where
  /-- The current length of an arc. -/
  lo : V → V → ℕ
  /-- The current length of the arc from the virtual source. -/
  off : V → ℕ
  /-- The sum of the estimates so far. -/
  sum : V → ℕ

/-- The lengths for the oracle. -/
def ItGlobal.len (g : ItGlobal V) : V → V → ℕ∞ := fun a b => ((g.lo a b + 1 : ℕ) : ℕ∞)

/-- The offsets for the oracle. -/
def ItGlobal.ofs (g : ItGlobal V) : V → ℕ∞ := fun v => ((g.off v + 1 : ℕ) : ℕ∞)

variable (N : Net V) (Q : Algorithm V (OracleIn V) σ Bq) (outQ : V → σ → ℕ) (TQ : ℕ)

/-- The estimate of an iteration, rounded up to a multiple of `4` and divided by `4`. -/
def itE (g : ItGlobal V) (v : V) : ℕ :=
  (outQ v (Q.run N.G (N.oracleIn g.len g.ofs) TQ v) + 3) / 4

/-- The next iteration. -/
def itNext (g : ItGlobal V) : ItGlobal V where
  lo a b := g.lo a b + 1 + itE N Q outQ TQ g a - itE N Q outQ TQ g b
  off v := g.off v + 1 - itE N Q outQ TQ g v
  sum v := g.sum v + itE N Q outQ TQ g v

/-- The iterations. -/
def itSeq (g₀ : ItGlobal V) : ℕ → ItGlobal V
  | 0 => g₀
  | i + 1 => itNext N Q outQ TQ (itSeq g₀ i)

/-- The contract of a smooth oracle on one network. -/
def SmoothOK (X : ℕ) : Prop :=
  ∀ (ℓ : V → V → ℕ∞) (φ : V → ℕ∞), OracleValid N 1 X ℓ φ → (∀ v, φ v ≠ ⊤) →
    let d := fun v => outQ v (Q.run N.G (N.oracleIn ℓ φ) TQ v)
    (∀ v, 2 * N.dsrcTop ℓ φ v ≤ (d v : ℝ≥0∞)) ∧
      (∀ a b, N.G.Adj a b → (d b : ℕ∞) ≤ d a + 4 * ℓ a b) ∧
      ∀ v, (d v : ℕ∞) ≤ 4 * φ v

/-- What an iteration needs from the estimates. -/
structure ItGood (g : ItGlobal V) (e : V → ℕ) : Prop where
  nc : ∀ v, ndsrc N.G.Adj (fun a b => g.lo a b + 1) (fun v => g.off v + 1) v ≤ 2 * e v
  smooth : ∀ a b, N.G.Adj a b → e b ≤ e a + (g.lo a b + 1)
  src : ∀ v, e v ≤ g.off v + 1

variable {N Q outQ TQ}

theorem dsrcTop_len (g : ItGlobal V) (v : V) :
    N.dsrcTop g.len g.ofs v =
      (ndsrc N.G.Adj (fun a b => g.lo a b + 1) (fun v => g.off v + 1) v : ℝ≥0∞) := by
  have h1 : lenTop g.len = lenOf fun a b => g.lo a b + 1 := by
    funext a b
    simp [lenTop, lenOf, ItGlobal.len]
  have h2 : offTop g.ofs = fun v => ((g.off v + 1 : ℕ) : ℝ≥0∞) := by
    funext v
    simp [offTop, ItGlobal.ofs]
  rw [← dsrc_nat, Net.dsrcTop, h1, h2]

theorem itGood_of_smooth {X : ℕ} (hQ : SmoothOK N Q outQ TQ X) {g : ItGlobal V}
    (h₁ : ∀ a b, N.G.Adj a b → g.lo a b + 1 ≤ X) (h₂ : ∀ v, g.off v + 1 ≤ X) :
    ItGood N g (itE N Q outQ TQ g) := by
  have hv : OracleValid N 1 X g.len g.ofs := by
    refine ⟨fun a b hab => .inr ⟨?_, ?_⟩, fun v => .inr ?_⟩
    · simp only [ItGlobal.len]
      exact_mod_cast Nat.le_add_left 1 _
    · simp only [ItGlobal.len]
      exact_mod_cast h₁ a b hab
    · simp only [ItGlobal.ofs]
      exact_mod_cast h₂ v
  obtain ⟨h3, h4, h5⟩ := hQ g.len g.ofs hv (fun v => by simp [ItGlobal.ofs])
  refine ⟨fun v => ?_, fun a b hab => ?_, fun v => ?_⟩
  · have h := h3 v
    rw [dsrcTop_len] at h
    have h' : 2 * ndsrc N.G.Adj (fun a b => g.lo a b + 1) (fun v => g.off v + 1) v ≤
        outQ v (Q.run N.G (N.oracleIn g.len g.ofs) TQ v) := by exact_mod_cast h
    simp only [itE]
    omega
  · have h := h4 a b hab
    simp only [ItGlobal.len] at h
    have h' : outQ b (Q.run N.G (N.oracleIn g.len g.ofs) TQ b) ≤
        outQ a (Q.run N.G (N.oracleIn g.len g.ofs) TQ a) + 4 * (g.lo a b + 1) := by
      exact_mod_cast h
    simp only [itE]
    omega
  · have h := h5 v
    simp only [ItGlobal.ofs] at h
    have h' : outQ v (Q.run N.G (N.oracleIn g.len g.ofs) TQ v) ≤ 4 * (g.off v + 1) := by
      exact_mod_cast h
    simp only [itE]
    omega

/-- Lengths and offsets stay polynomial. -/
theorem it_bounds {X R I : ℕ} (hQ : SmoothOK N Q outQ TQ X) {g₀ : ItGlobal V}
    (h₁ : ∀ a b, N.G.Adj a b → g₀.lo a b ≤ R) (h₂ : ∀ v, g₀.off v ≤ R)
    (hX : R + I * (R + I + 2) + 1 ≤ X) : ∀ i, i ≤ I →
      (∀ v, (itSeq N Q outQ TQ g₀ i).off v ≤ R + i) ∧
      ∀ a b, N.G.Adj a b → (itSeq N Q outQ TQ g₀ i).lo a b ≤ R + i * (R + i + 2) := by
  have hmono : ∀ i, i ≤ I → i * (R + i + 2) ≤ I * (R + I + 2) := fun i hi =>
    Nat.mul_le_mul hi (by omega)
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨fun v => by simpa [itSeq] using h₂ v, fun a b hab => by simpa [itSeq] using h₁ a b hab⟩
  | succ i ih =>
    intro hi
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    have hm := hmono i (by omega)
    have hg := itGood_of_smooth hQ (g := itSeq N Q outQ TQ g₀ i)
      (fun a b hab => by have := ih₂ a b hab; omega)
      (fun v => by
        have := ih₁ v
        have : i ≤ i * (R + i + 2) + I := by omega
        have : I ≤ I * (R + I + 2) := Nat.le_mul_of_pos_right _ (by omega)
        omega)
    refine ⟨fun v => ?_, fun a b hab => ?_⟩
    · show (itSeq N Q outQ TQ g₀ i).off v + 1 - _ ≤ _
      have := ih₁ v
      omega
    · show (itSeq N Q outQ TQ g₀ i).lo a b + 1 + _ - _ ≤ _
      have h3 := ih₂ a b hab
      have h4 := hg.src a
      have h5 := ih₁ a
      have h6 : (i + 1) * (R + (i + 1) + 2) = i * (R + i + 2) + (R + i + 2) + (i + 1) := by ring
      omega

/-- All iterations before `I` meet the contract. -/
theorem it_good {X R I : ℕ} (hQ : SmoothOK N Q outQ TQ X) {g₀ : ItGlobal V}
    (h₁ : ∀ a b, N.G.Adj a b → g₀.lo a b ≤ R) (h₂ : ∀ v, g₀.off v ≤ R)
    (hX : R + I * (R + I + 2) + 1 ≤ X) : ∀ i, i < I →
      ItGood N (itSeq N Q outQ TQ g₀ i) (itE N Q outQ TQ (itSeq N Q outQ TQ g₀ i)) := by
  intro i hi
  obtain ⟨h₃, h₄⟩ := it_bounds hQ h₁ h₂ hX i hi.le
  have hm : i * (R + i + 2) ≤ I * (R + I + 2) := Nat.mul_le_mul hi.le (by omega)
  have hI' : I ≤ I * (R + I + 2) := Nat.le_mul_of_pos_right _ (by omega)
  exact itGood_of_smooth hQ (fun a b hab => by have := h₄ a b hab; omega)
    (fun w => by have := h₃ w; omega)

/-- The iterations are a run of `Boost.Run`, and rounding gives the exact distance. -/
theorem it_main {X M U I : ℕ} (hQ : SmoothOK N Q outQ TQ X) {x₂ : V → V → ℕ} {y₂ : V → ℕ}
    (hU : 8 * (I + 1) * (Fintype.card V + 1) ≤ U) (hI : 4 * M < 2 ^ I)
    (hx : ∀ a b, N.G.Adj a b → x₂ a b ≤ M) (hy : ∀ v, y₂ v ≤ M)
    (hX : U * M + I * (U * M + I + 2) + 1 ≤ X) (v : V) :
    (round ((((itSeq N Q outQ TQ
      ⟨fun a b => U * x₂ a b, fun v => U * y₂ v, fun _ => 0⟩ I).sum v : ℕ) : ℝ) / U)) =
      (ndsrc N.G.Adj x₂ y₂ v : ℤ) := by
  have hUpos : 0 < U := lt_of_lt_of_le (by positivity) hU
  have hUr : (0 : ℝ) < U := by exact_mod_cast hUpos
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 / U := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  have hUc : (U : ℝ) * c = 1 := by rw [hcdef]; field_simp
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : ItGlobal V, g₀ = ⟨fun a b => U * x₂ a b, fun v => U * y₂ v, fun _ => 0⟩ :=
    ⟨_, rfl⟩
  rw [← hg₀]
  have hgood := it_good (R := U * M) (I := I) hQ (g₀ := g₀)
    (fun a b hab => by rw [hg₀]; exact Nat.mul_le_mul_left _ (hx a b hab))
    (fun v => by rw [hg₀]; exact Nat.mul_le_mul_left _ (hy v)) hX
  have R : Boost.Run (none : Option V) (oLen (adj := N.G.Adj) x₂ y₂)
      (fun i a b e => (oLen (itSeq N Q outQ TQ g₀ i).lo (itSeq N Q outQ TQ g₀ i).off a b e : ℝ) * c)
      (fun i => oDt (itE N Q outQ TQ (itSeq N Q outQ TQ g₀ i)) c) 2 c I := by
    refine ⟨by norm_num, hc.le, ?_, ?_, ?_, fun _ _ => rfl, ?_, ?_⟩
    · intro u
      cases u with
      | none => exact ⟨.nil _⟩
      | some w => exact ⟨.cons (.src w) (.nil _)⟩
    · intro a b e
      cases e with
      | src w =>
        simp only [oLen, itSeq, hg₀]
        push_cast
        rw [mul_right_comm, hUc, one_mul]
      | edge h =>
        simp only [oLen, itSeq, hg₀]
        push_cast
        rw [mul_right_comm, hUc, one_mul]
    · intro i hi a b e
      have hG := hgood i hi
      cases e with
      | @src w =>
        have h1 : (((itSeq N Q outQ TQ g₀ (i + 1)).off w : ℕ) : ℝ) =
            ((itSeq N Q outQ TQ g₀ i).off w : ℝ) + 1 -
              (itE N Q outQ TQ (itSeq N Q outQ TQ g₀ i) w : ℝ) := by
          rw [eq_sub_iff_add_eq]
          exact_mod_cast Nat.sub_add_cancel (hG.src w)
        simp only [oLen, oDt]
        rw [h1]
        push_cast
        ring
      | @edge a' b' h =>
        have h1 : (((itSeq N Q outQ TQ g₀ (i + 1)).lo a' b' : ℕ) : ℝ) =
            ((itSeq N Q outQ TQ g₀ i).lo a' b' : ℝ) + 1 +
              (itE N Q outQ TQ (itSeq N Q outQ TQ g₀ i) a' : ℝ) -
              (itE N Q outQ TQ (itSeq N Q outQ TQ g₀ i) b' : ℝ) := by
          rw [eq_sub_iff_add_eq]
          exact_mod_cast Nat.sub_add_cancel (by have := hG.smooth a' b' h; omega)
        simp only [oLen, oDt]
        rw [h1]
        push_cast
        ring
    · intro i hi u
      have hG := hgood i hi
      have hnn : ∀ a b (e : OArc N.G.Adj a b), 0 ≤
          (oLen (itSeq N Q outQ TQ g₀ i).lo (itSeq N Q outQ TQ g₀ i).off a b e : ℝ) * c + c :=
        fun _ _ _ => add_nonneg (mul_nonneg (Nat.cast_nonneg _) hc.le) hc.le
      cases u with
      | none => exact Boost.dist_le _ hnn (.nil _)
      | some w =>
        have heq : (fun a b (e : OArc N.G.Adj a b) =>
            (oLen (itSeq N Q outQ TQ g₀ i).lo (itSeq N Q outQ TQ g₀ i).off a b e : ℝ) * c + c) =
            fun a b e => (oLen (fun a b => (itSeq N Q outQ TQ g₀ i).lo a b + 1)
              (fun v => (itSeq N Q outQ TQ g₀ i).off v + 1) a b e : ℝ) * c := by
          funext a b e
          cases e <;> simp only [oLen] <;> push_cast <;> ring
        rw [heq]
        refine (boost_dist_le _ _ hc.le w).trans ?_
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hG.nc w) hc.le
    · intro i hi a b e
      have hG := hgood i hi
      cases e with
      | @src w =>
        simp only [oLen, oDt]
        have h1 : (itE N Q outQ TQ (itSeq N Q outQ TQ g₀ i) w : ℝ) ≤
            ((itSeq N Q outQ TQ g₀ i).off w : ℝ) + 1 := by exact_mod_cast hG.src w
        have h2 := mul_le_mul_of_nonneg_right h1 hc.le
        push_cast
        nlinarith
      | @edge a' b' h =>
        simp only [oLen, oDt]
        have h1 : (itE N Q outQ TQ (itSeq N Q outQ TQ g₀ i) b' : ℝ) ≤
            (itE N Q outQ TQ (itSeq N Q outQ TQ g₀ i) a' : ℝ) +
              (((itSeq N Q outQ TQ g₀ i).lo a' b' : ℝ) + 1) := by
          exact_mod_cast hG.smooth a' b' h
        have h2 := mul_le_mul_of_nonneg_right h1 hc.le
        push_cast
        nlinarith
  have hdist : Boost.dist (none : Option V) (fun a b (e : OArc N.G.Adj a b) =>
      (oLen (itSeq N Q outQ TQ g₀ 0).lo (itSeq N Q outQ TQ g₀ 0).off a b e : ℝ) * c) (some v) =
      (ndsrc N.G.Adj x₂ y₂ v : ℝ) := by
    have heq : (fun a b (e : OArc N.G.Adj a b) =>
        (oLen (itSeq N Q outQ TQ g₀ 0).lo (itSeq N Q outQ TQ g₀ 0).off a b e : ℝ) * c) =
        fun a b e => (oLen x₂ y₂ a b e : ℝ) * 1 := by
      funext a b e
      cases e with
      | src w =>
        simp only [oLen, itSeq, hg₀]
        push_cast
        rw [mul_right_comm, hUc]
        ring
      | edge h =>
        simp only [oLen, itSeq, hg₀]
        push_cast
        rw [mul_right_comm, hUc]
        ring
    rw [heq]
    have h1 := boost_dist_le (adj := N.G.Adj) x₂ y₂ (c := 1) zero_le_one v
    have h2 := le_boost_dist (adj := N.G.Adj) x₂ y₂ (c := 1) zero_le_one v
    rw [mul_one] at h1 h2
    exact le_antisymm h1 h2
  have hsum : ∀ J, ∑ i ∈ Finset.range J,
      oDt (itE N Q outQ TQ (itSeq N Q outQ TQ g₀ i)) c (some v) / 2 =
      (((itSeq N Q outQ TQ g₀ J).sum v : ℕ) : ℝ) * c := by
    intro J
    induction J with
    | zero =>
      simp [itSeq, hg₀]
    | succ J ih =>
      rw [Finset.sum_range_succ, ih]
      show _ = (((itSeq N Q outQ TQ g₀ J).sum v +
        itE N Q outQ TQ (itSeq N Q outQ TQ g₀ J) v : ℕ) : ℝ) * c
      simp only [oDt]
      push_cast
      ring
  have hcardr : ((Fintype.card (Option V) : ℕ) : ℝ) - 1 = (Fintype.card V : ℝ) := by
    rw [Fintype.card_option]
    push_cast
    ring
  have hU8 : (8 : ℝ) * ((I : ℝ) + 1) * ((Fintype.card V : ℝ) + 1) * c ≤ 1 := by
    have h1 : ((8 * (I + 1) * (Fintype.card V + 1) : ℕ) : ℝ) ≤ U := by exact_mod_cast hU
    push_cast at h1
    have h2 := mul_le_mul_of_nonneg_right h1 hc.le
    rwa [hUc] at h2
  have hnc : (Fintype.card V : ℝ) * c ≤ ((I : ℝ) + 1) * ((Fintype.card V : ℝ) + 1) * c := by
    refine mul_le_mul_of_nonneg_right ?_ hc.le
    have : (0 : ℝ) ≤ I := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    nlinarith
  have hinc : (I : ℝ) * (Fintype.card V : ℝ) * c ≤
      ((I : ℝ) + 1) * ((Fintype.card V : ℝ) + 1) * c := by
    refine mul_le_mul_of_nonneg_right ?_ hc.le
    have : (0 : ℝ) ≤ I := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    nlinarith
  have hDM : (ndsrc N.G.Adj x₂ y₂ v : ℝ) ≤ M := by
    exact_mod_cast (ndsrc_le_off v).trans (hy v)
  have hex := R.exact I le_rfl (some v) (by
      rw [hdist, hcardr, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div_pow]
      have h2I : (4 : ℝ) * M < 2 ^ I := by exact_mod_cast hI
      have hpos : (0 : ℝ) < 2 ^ I := by positivity
      have h3 : (1 : ℝ) / 2 ^ I * (ndsrc N.G.Adj x₂ y₂ v : ℝ) ≤ 1 / 2 ^ I * M :=
        mul_le_mul_of_nonneg_left hDM (by positivity)
      have h4 : (1 : ℝ) / 2 ^ I * M < 1 / 4 := by
        rw [one_div_mul_eq_div, div_lt_iff₀ hpos]
        linarith
      nlinarith) (by
      rw [hcardr]
      nlinarith)
  have h6 : (((itSeq N Q outQ TQ g₀ I).sum v : ℕ) : ℝ) * c = ((itSeq N Q outQ TQ g₀ I).sum v : ℝ) / U := by
    rw [hcdef]
    ring
  rw [hdist, hsum, h6] at hex
  exact_mod_cast hex

end Iter

/-! ### The algorithm -/

section Alg

variable {V : Type} [Fintype V] [DecidableEq V] {σ : Type} {Bq B : ℕ}

/-- The data of a node between two iterations. -/
structure ItData (V : Type) where
  /-- The neighbours in rotation order. -/
  nbrs : List V
  /-- The current lengths of the arcs to the neighbours. -/
  lo : V → ℕ
  /-- The current lengths of the arcs from the neighbours. -/
  li : V → ℕ
  /-- The current length of the arc from the virtual source. -/
  off : ℕ
  /-- The sum of the estimates so far. -/
  sum : ℕ

/-- The input of the oracle from the data of a node. -/
def itIn (j : ItData V) : OracleIn V where
  nbrs := j.nbrs
  lenOut u := if u ∈ j.nbrs then ((j.lo u + 1 : ℕ) : ℕ∞) else ⊤
  lenIn u := if u ∈ j.nbrs then ((j.li u + 1 : ℕ) : ℕ∞) else ⊤
  offset := ((j.off + 1 : ℕ) : ℕ∞)

/-- The new data of a node from its estimate and those of its neighbours. -/
def itUpd (j : ItData V) (x : ℕ) (recv : V → Option ℕ) : ItData V where
  nbrs := j.nbrs
  lo u := j.lo u + 1 + x - (recv u).getD 0
  li u := j.li u + 1 + (recv u).getD 0 - x
  off := j.off + 1 - x
  sum := j.sum + x

/-- The data of a node before the first iteration. -/
def itInit (S M U : ℕ) (i : OracleIn V) : ItData V where
  nbrs := i.nbrs
  lo u := U * scaleLen S M (i.lenOut u)
  li u := U * scaleLen S M (i.lenIn u)
  off := U * scaleOff S M i.offset
  sum := 0

/-- The states of one iteration. -/
abbrev BodyState (V σ : Type) : Type := (ℕ × σ) ⊕ (ℕ × (V → Option ℕ))

/-- The states of the whole algorithm. -/
abbrev ExactState (V σ : Type) : Type :=
  (ℕ × (OracleIn V × (ItData V × ℕ × BodyState V σ))) ⊕ ((OracleIn V × ℕ) × (ℕ × (V → Option ℕ)))

/-- One iteration: the oracle, then one round in which the nodes tell their neighbours the estimate. -/
noncomputable def itBody (Q : Algorithm V (OracleIn V) σ Bq) (outQ : V → σ → ℕ) (TQ : ℕ)
    (hB : Bq ≤ B) : Algorithm V (OracleIn V) (BodyState V σ) B :=
  (Q.widen hB).seq TQ (fun v s => (outQ v s + 3) / 4) (Algorithm.exch V B)

/-- The new data from the state after an iteration. -/
def itStep (j : ItData V) (s : BodyState V σ) : ItData V :=
  match s with
  | .inr p => itUpd j p.1 p.2
  | .inl _ => j

/-- The iterations. -/
noncomputable def itLoop (Q : Algorithm V (OracleIn V) σ Bq) (outQ : V → σ → ℕ) (TQ : ℕ)
    (hB : Bq ≤ B) : Algorithm V (ItData V) (ItData V × ℕ × BodyState V σ) B :=
  (itBody Q outQ TQ hB).iter (TQ + 1) (fun _ j => itIn j) (fun _ j s => itStep j s)

/-- The input and the new distance from the state after the iterations. -/
noncomputable def exactRound (U : ℕ) (s : OracleIn V × (ItData V × ℕ × BodyState V σ)) :
    OracleIn V × ℕ :=
  (s.1, (round ((s.2.1.sum : ℝ) / U)).toNat)

/-- The whole algorithm: the iterations, rounding, and one round in which the nodes tell their
neighbours the new distance. -/
noncomputable def exactAlg (Q : Algorithm V (OracleIn V) σ Bq) (outQ : V → σ → ℕ) (TQ : ℕ)
    (hB : Bq ≤ B) (I S M U : ℕ) : Algorithm V (OracleIn V) (ExactState V σ) B :=
  ((itLoop Q outQ TQ hB).keep fun _ i => itInit S M U i).seq (I * (TQ + 1))
    (fun _ s => exactRound U s) ((Algorithm.exch V B).keep fun _ p => p.2)

/-- The output of a node. -/
noncomputable def exactOut (S M : ℕ) (s : ℕ × ExactState V σ) : ℕ∞ × Option V :=
  match s.2 with
  | .inr (p, q) =>
    (dOut S M p.2,
      pOut M (scaleOff S M p.1.offset) (fun u => scaleLen S M (p.1.lenIn u)) p.2 q.2)
  | .inl _ => (⊤, none)

/-- The data of the nodes are their parts of an iteration. -/
structure ItRel (N : Net V) (g : ItGlobal V) (j : V → ItData V) : Prop where
  nbrs : ∀ v, (j v).nbrs = N.rotList v
  lo : ∀ v u, N.G.Adj v u → (j v).lo u = g.lo v u
  li : ∀ v u, N.G.Adj v u → (j v).li u = g.lo u v
  off : ∀ v, (j v).off = g.off v
  sum : ∀ v, (j v).sum = g.sum v

variable {N : Net V} {Q : Algorithm V (OracleIn V) σ Bq} {outQ : V → σ → ℕ} {TQ : ℕ}

theorem ItRel.itIn_eq {g : ItGlobal V} {j : V → ItData V} (h : ItRel N g j) :
    (fun v => itIn (j v)) = N.oracleIn g.len g.ofs := by
  funext v
  simp only [itIn, Net.oracleIn, ItGlobal.len, ItGlobal.ofs]
  rw [h.nbrs v, h.off v]
  congr 1
  · funext u
    by_cases hu : N.G.Adj v u
    · simp [(N.mem_rotList v u).2 hu, hu, h.lo v u hu]
    · have hm : u ∉ N.rotList v := fun hm => hu ((N.mem_rotList v u).1 hm)
      simp [hm, hu]
  · funext u
    by_cases hu : N.G.Adj v u
    · simp [(N.mem_rotList v u).2 hu, hu, h.li v u hu]
    · have hm : u ∉ N.rotList v := fun hm => hu ((N.mem_rotList v u).1 hm)
      simp [hm, hu]

omit [Fintype V] [DecidableEq V] in
theorem run_itBody (Q : Algorithm V (OracleIn V) σ Bq) (outQ : V → σ → ℕ) (TQ : ℕ) (hB : Bq ≤ B)
    (G : SimpleGraph V) [DecidableRel G.Adj] (inp : V → OracleIn V)
    (hlt : ∀ v, (outQ v (Q.run G inp TQ v) + 3) / 4 < 2 ^ B) (v : V) :
    (itBody Q outQ TQ hB).run G inp (TQ + 1) v =
      .inr ((outQ v (Q.run G inp TQ v) + 3) / 4, fun u =>
        if G.Adj u v then some ((outQ u (Q.run G inp TQ u) + 3) / 4) else none) := by
  have h1 := congrFun (Algorithm.run_seq (Q.widen hB) TQ (fun v s => (outQ v s + 3) / 4)
    (Algorithm.exch V B) G inp 1) v
  rw [Algorithm.run_widen] at h1
  rw [← Algorithm.run_exch G (fun v => (outQ v (Q.run G inp TQ v) + 3) / 4) hlt v]
  exact h1

/-- An iteration on the network is a step of `itSeq`. -/
theorem ItRel.next (hB : Bq ≤ B) {g : ItGlobal V} {j : V → ItData V} (h : ItRel N g j)
    (hlt : ∀ v, itE N Q outQ TQ g v < 2 ^ B) :
    ItRel N (itNext N Q outQ TQ g) (fun v =>
      itStep (j v) ((itBody Q outQ TQ hB).run N.G (fun v => itIn (j v)) (TQ + 1) v)) := by
  rw [h.itIn_eq]
  have hrun := run_itBody Q outQ TQ hB N.G (N.oracleIn g.len g.ofs) hlt
  refine ⟨fun v => ?_, fun v u hu => ?_, fun v u hu => ?_, fun v => ?_, fun v => ?_⟩
  · rw [hrun]
    exact h.nbrs v
  · rw [hrun]
    have hu' : N.G.Adj u v := hu.symm
    simp [itStep, itUpd, hu', h.lo v u hu, itNext, itE]
  · rw [hrun]
    have hu' : N.G.Adj u v := hu.symm
    simp [itStep, itUpd, hu', h.li v u hu, itNext, itE]
  · rw [hrun]
    simp [itStep, itUpd, h.off v, itNext, itE]
  · rw [hrun]
    simp [itStep, itUpd, h.sum v, itNext, itE]

theorem itRel_iter (hB : Bq ≤ B) {g₀ : ItGlobal V} {j₀ : V → ItData V} (h₀ : ItRel N g₀ j₀) {I : ℕ}
    (hlt : ∀ i, i < I → ∀ v, itE N Q outQ TQ (itSeq N Q outQ TQ g₀ i) v < 2 ^ B) :
    ∀ i, i ≤ I → ItRel N (itSeq N Q outQ TQ g₀ i)
      (Algorithm.iterData (itBody Q outQ TQ hB) (TQ + 1) (fun _ j => itIn j)
        (fun _ j s => itStep j s) N.G j₀ i)
  | 0, _ => h₀
  | i + 1, hi => (itRel_iter hB h₀ hlt i (by omega)).next hB (hlt i (by omega))

theorem itRel_init (N : Net V) (S M U : ℕ) (ℓ : V → V → ℕ∞) (φ : V → ℕ∞) :
    ItRel N ⟨fun a b => U * lenScale S M ℓ a b, fun v => U * offScale S M φ v, fun _ => 0⟩
      (fun v => itInit S M U (N.oracleIn ℓ φ v)) := by
  refine ⟨fun v => rfl, fun v u hu => ?_, fun v u hu => ?_, fun v => rfl, fun v => rfl⟩
  · simp [itInit, Net.oracleIn, lenScale, hu]
  · simp [itInit, Net.oracleIn, lenScale, hu]

theorem scale_le {S M W c : ℕ} {x : ℕ∞} (hc : 1 ≤ c) (hM : M = S * (c * W) + c + 1)
    (h : x = ⊤ ∨ x ≤ W) : scaleLen S M x ≤ M ∧ scaleOff S M x ≤ M := by
  rcases h with rfl | h
  · simp
  · have hne : x ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 hne
    have h1 : m ≤ W := by exact_mod_cast h
    have h2 : W ≤ c * W := Nat.le_mul_of_pos_left _ hc
    have h3 : S * m ≤ S * (c * W) := Nat.mul_le_mul_left _ (h1.trans h2)
    simp only [scaleLen_coe, scaleOff_coe]
    omega

theorem run_exactAlg (Q : Algorithm V (OracleIn V) σ Bq) (outQ : V → σ → ℕ) (TQ : ℕ) (hB : Bq ≤ B)
    (I S M U : ℕ) (N : Net V) (inp : V → OracleIn V) (D : V → ℕ)
    (hD : ∀ v, (round ((((Algorithm.iterData (itBody Q outQ TQ hB) (TQ + 1) (fun _ j => itIn j)
      (fun _ j s => itStep j s) N.G (fun v => itInit S M U (inp v)) I v).sum : ℕ) : ℝ) / U)).toNat =
        D v)
    (hDB : ∀ v, D v < 2 ^ B) (v : V) :
    (exactAlg Q outQ TQ hB I S M U).run N.G inp (I * (TQ + 1) + 1) v =
      .inr ((inp v, D v), (D v, fun u => if N.G.Adj u v then some (D u) else none)) := by
  have h3 : ∀ v, ((itLoop Q outQ TQ hB).run N.G (fun v => itInit S M U (inp v))
      (I * (TQ + 1)) v).1 =
      Algorithm.iterData (itBody Q outQ TQ hB) (TQ + 1) (fun _ j => itIn j)
        (fun _ j s => itStep j s) N.G (fun v => itInit S M U (inp v)) I v := fun v =>
    congrArg Prod.fst (congrFun (Algorithm.run_iter (itBody Q outQ TQ hB) _ _ N.G _
      (Nat.succ_pos TQ) I 0 (Nat.succ_pos TQ)) v)
  have h4 : (fun v => exactRound U (((itLoop Q outQ TQ hB).keep fun _ i => itInit S M U i).run
      N.G inp (I * (TQ + 1)) v)) = fun v => (inp v, D v) := by
    rw [Algorithm.run_keep]
    funext v
    simp only [exactRound, h3, hD]
  have h1 : (exactAlg Q outQ TQ hB I S M U).run N.G inp (I * (TQ + 1) + 1) v =
      .inr (((Algorithm.exch V B).keep fun _ p => p.2).run N.G
        (fun v => exactRound U (((itLoop Q outQ TQ hB).keep fun _ i => itInit S M U i).run
          N.G inp (I * (TQ + 1)) v)) 1 v) :=
    congrFun (Algorithm.run_seq _ _ _ _ N.G inp 1) v
  rw [h1, h4, Algorithm.run_keep]
  show Sum.inr ((inp v, D v), (Algorithm.exch V B).run N.G D 1 v) = _
  rw [Algorithm.run_exch N.G D hDB v]

/-- The algorithm is correct, given the contract of the oracle. -/
theorem exactAlg_ok (hB : Bq ≤ B) {I S M U W X t : ℕ} {ℓ : V → V → ℕ∞} {φ : V → ℕ∞}
    (hQ : SmoothOK N Q outQ TQ X) (hV : OracleValid N 0 W ℓ φ) (hS : S = Fintype.card V + 1)
    (hM : M = S * (Fintype.card V * W) + Fintype.card V + 1)
    (hU : 8 * (I + 1) * (Fintype.card V + 1) ≤ U) (hI : 4 * M < 2 ^ I)
    (hX : U * M + I * (U * M + I + 2) + 1 ≤ X) (hXB : X < 2 ^ B)
    (ht : I * (TQ + 1) + 1 ≤ t) :
    N.ExactSpec ℓ φ (fun v => exactOut S M
      (((exactAlg Q outQ TQ hB I S M U).stopAt (I * (TQ + 1) + 1)).run N.G
        (N.oracleIn ℓ φ) t v)) := by
  have hUpos : 0 < U := lt_of_lt_of_le (by positivity) hU
  have hMU : M ≤ U * M := Nat.le_mul_of_pos_left _ hUpos
  have hx : ∀ a b, N.G.Adj a b → lenScale S M ℓ a b ≤ M := fun a b hab =>
    (scale_le (Fintype.card_pos_iff.2 ⟨a⟩) hM ((hV.1 a b hab).imp_right And.right)).1
  have hy : ∀ v, offScale S M φ v ≤ M := fun v =>
    (scale_le (Fintype.card_pos_iff.2 ⟨v⟩) hM (hV.2 v)).2
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : ItGlobal V, g₀ = ⟨fun a b => U * lenScale S M ℓ a b,
      fun v => U * offScale S M φ v, fun _ => 0⟩ := ⟨_, rfl⟩
  have h₁ : ∀ a b, N.G.Adj a b → g₀.lo a b ≤ U * M := fun a b hab => by
    rw [hg₀]
    exact Nat.mul_le_mul_left _ (hx a b hab)
  have h₂ : ∀ v, g₀.off v ≤ U * M := fun v => by
    rw [hg₀]
    exact Nat.mul_le_mul_left _ (hy v)
  have hlt : ∀ i, i < I → ∀ v, itE N Q outQ TQ (itSeq N Q outQ TQ g₀ i) v < 2 ^ B := by
    intro i hi v
    have h₃ := (it_good hQ h₁ h₂ hX i hi).src v
    have h₄ := (it_bounds hQ h₁ h₂ hX i hi.le).1 v
    have h₅ : I ≤ I * (U * M + I + 2) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hrel := itRel_iter hB (hg₀ ▸ itRel_init N S M U ℓ φ) hlt I le_rfl
  have hD : ∀ v, (round ((((Algorithm.iterData (itBody Q outQ TQ hB) (TQ + 1) (fun _ j => itIn j)
      (fun _ j s => itStep j s) N.G (fun v => itInit S M U (N.oracleIn ℓ φ v)) I v).sum : ℕ) : ℝ) /
        U)).toNat = ndsrc N.G.Adj (lenScale S M ℓ) (offScale S M φ) v := by
    intro v
    have h := it_main hQ hU hI hx hy hX v
    rw [← hg₀] at h
    rw [hrel.sum v, h]
    simp
  have hDB : ∀ v, ndsrc N.G.Adj (lenScale S M ℓ) (offScale S M φ) v < 2 ^ B := fun v => by
    have h₃ : ndsrc N.G.Adj (lenScale S M ℓ) (offScale S M φ) v ≤ offScale S M φ v := ndsrc_le_off v
    have h₄ := hy v
    omega
  have hmin : min t (I * (TQ + 1) + 1) = I * (TQ + 1) + 1 := min_eq_right ht
  have hfun : (fun v => exactOut S M
      (((exactAlg Q outQ TQ hB I S M U).stopAt (I * (TQ + 1) + 1)).run N.G
        (N.oracleIn ℓ φ) t v)) = fun v =>
      (dOut S M (ndsrc N.G.Adj (lenScale S M ℓ) (offScale S M φ) v),
        pOut M (offScale S M φ v) (fun p => scaleLen S M ((N.oracleIn ℓ φ v).lenIn p))
          (ndsrc N.G.Adj (lenScale S M ℓ) (offScale S M φ) v)
          (fun p => if N.G.Adj p v then
            some (ndsrc N.G.Adj (lenScale S M ℓ) (offScale S M φ) p) else none)) := by
    funext v
    rw [Algorithm.run_stopAt]
    simp only [hmin]
    rw [run_exactAlg Q outQ TQ hB I S M U N _ _ hD hDB v]
    rfl
  rw [hfun]
  exact exactSpec_of_ndsrc hV hS (by omega)
    (fun v p => scaleLen S M ((N.oracleIn ℓ φ v).lenIn p))
    (fun v p hp => by simp [Net.oracleIn, lenScale, hp.symm])

end Alg

/-! ### The bound -/

/-- The replacement of `⊤`. -/
def exM (K n : ℕ) : ℕ := (n + 1) * (n * (n + 2) ^ K) + n + 1

/-- The number of iterations. -/
def exI (K n : ℕ) : ℕ := Nat.log 2 (4 * exM K n) + 1

/-- The unit of the lengths. -/
def exU (K n : ℕ) : ℕ := 8 * (exI K n + 1) * (n + 1)

/-- A bound on all lengths in the iterations. -/
def exX (K n : ℕ) : ℕ :=
  exU K n * exM K n + exI K n * (exU K n * exM K n + exI K n + 2) + 1

theorem polyN_exM (K : ℕ) : PolyN (exM K) :=
  (((polyN_id.add (PolyN.const 1)).mul (polyN_id.mul (polyN_pow K))).add polyN_id).add
    (PolyN.const 1)

theorem polyN_exI (K : ℕ) : PolyN (exI K) :=
  PolyN.mono (g := fun n => 4 * exM K n + 1)
    (fun _ => Nat.add_le_add_right (Nat.log_le_self _ _) 1)
    (((PolyN.const 4).mul (polyN_exM K)).add (PolyN.const 1))

theorem polyLog_exI (K : ℕ) : PolyLog (exI K) :=
  ((PolyN.const 4).mul (polyN_exM K)).log.add (PolyLog.const 1)

theorem polyN_exU (K : ℕ) : PolyN (exU K) :=
  ((PolyN.const 8).mul ((polyN_exI K).add (PolyN.const 1))).mul (polyN_id.add (PolyN.const 1))

theorem polyN_exX (K : ℕ) : PolyN (exX K) :=
  have a := (polyN_exU K).mul (polyN_exM K)
  (a.add ((polyN_exI K).mul ((a.add (polyN_exI K)).add (PolyN.const 2)))).add (PolyN.const 1)

theorem polyN_logN (C : ℕ) : PolyN fun n => C * logN n + 1 :=
  PolyN.mono (g := fun n => C * (n + 3) + 1)
    (fun n => Nat.add_le_add_right (Nat.mul_le_mul_left _ (by
      have := Nat.log_le_self 2 (n + 2)
      unfold logN
      omega)) 1)
    (((PolyN.const C).mul (polyN_id.add (PolyN.const 3))).add (PolyN.const 1))

theorem rounds_le {I a g₁ e T D : ℕ} (hD : 1 ≤ D) (hT : T ≤ g₁ * D * e) :
    I * (a * (T + D + 1) + 1) + 1 ≤ (I * (a * (g₁ * e + 2) + 1) + 1) * D := by
  have h1 : T + D + 1 ≤ (g₁ * e + 2) * D := by nlinarith
  have h2 : a * (T + D + 1) + 1 ≤ (a * (g₁ * e + 2) + 1) * D := by
    calc a * (T + D + 1) + 1 ≤ a * ((g₁ * e + 2) * D) + D := by gcongr
      _ = _ := by ring
  calc I * (a * (T + D + 1) + 1) + 1 ≤ I * ((a * (g₁ * e + 2) + 1) * D) + D := by gcongr
    _ = _ := by ring

/-- **Exact SSSP.** Labels, the aggregation and the smoothing give exact distances and a shortest-path
forest in `Õ(D)` rounds, with words of polylogarithmically many bits. -/
theorem exactSsspBound (hL : LabelHypothesis) (hA : AggBox) (hS : SmoothingBox) :
    ExactSsspBound := by
  intro K
  obtain ⟨K₁, hK₁⟩ := polyN_exX K
  obtain ⟨Cs, cs, hSK⟩ := hS K₁
  obtain ⟨k, hk⟩ := polyN_logN Cs
  obtain ⟨g, gB, hg, hgB, hOr⟩ := approxOracle hL hA (max k Cs)
  have hf : PolyLog fun n => gB n + Cs * logN n ^ cs + (logN n * K₁ + 1) +
      (exI K n * (Cs * logN n * (g n * (Cs * logN n + 1) + 2) + 1) + 1) :=
    ((hgB.add (polyLog_pow Cs cs)).add
      ((polyLog_logN.mul (PolyLog.const K₁)).add (PolyLog.const 1))).add
      (((polyLog_exI K).mul ((((PolyLog.const Cs).mul polyLog_logN).mul
        ((hg.mul (((PolyLog.const Cs).mul polyLog_logN).add (PolyLog.const 1))).add
          (PolyLog.const 2))).add (PolyLog.const 1))).add (PolyLog.const 1))
  obtain ⟨C, c, hCc⟩ := hf
  refine ⟨C, c, fun n D hD => ?_⟩
  have hX2 : 1 ≤ n + 2 := by omega
  obtain ⟨T, σ, A, out, hT, hAO⟩ := hOr n (Cs * logN n + 1) D (by omega)
    ((hk n).trans (Nat.pow_le_pow_right hX2 (le_max_left _ _))) hD
  have hAO' := hAO.mono (W := (n + 2) ^ Cs) (e := Cs * logN n)
    (Nat.pow_le_pow_right hX2 (le_max_right _ _)) (by omega)
  obtain ⟨σ', Q, out', hQ⟩ := hSK n D T (gB n) σ A out hAO'
  have hC : gB n + Cs * logN n ^ cs + (logN n * K₁ + 1) +
      (exI K n * (Cs * logN n * (g n * (Cs * logN n + 1) + 2) + 1) + 1) ≤ C * logN n ^ c := hCc n
  have hB : gB n + Cs * logN n ^ cs ≤ C * logN n ^ c := by omega
  have hXB : (n + 2) ^ K₁ < 2 ^ (C * logN n ^ c) :=
    (lt_two_pow_of_le le_rfl).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine ⟨_, (exactAlg Q out' (Cs * logN n * (T + D + 1)) hB (exI K n) (n + 1) (exM K n)
    (exU K n)).stopAt (exI K n * (Cs * logN n * (T + D + 1) + 1) + 1),
    fun _ s => exactOut (n + 1) (exM K n) s, fun N ℓ φ hP hDi hV => ?_⟩
  have hround := rounds_le (I := exI K n) (a := Cs * logN n) (g₁ := g n)
    (e := Cs * logN n + 1) hD hT
  refine exactAlg_ok hB (W := (n + 2) ^ K) (X := (n + 2) ^ K₁)
    (fun ℓ' φ' hV' hφ' => hQ N ℓ' φ' hP hDi hV' hφ') hV ?_ ?_ ?_ ?_ ?_ hXB ?_
  · rw [Fintype.card_fin]
  · rw [Fintype.card_fin]
    rfl
  · rw [Fintype.card_fin]
    exact le_rfl
  · exact Nat.lt_pow_succ_log_self (by norm_num) _
  · exact hK₁ n
  · exact hround.trans (Nat.mul_le_mul_right D (by omega))

end SsspFlow.Congest
