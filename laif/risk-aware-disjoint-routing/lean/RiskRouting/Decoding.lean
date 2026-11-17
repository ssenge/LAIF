import RiskRouting.Combined

/-!
# Decoding the reduced encoding

The reduced encoding of arXiv:2610.13621 replaces the link variables of one path by values of
three kinds: a variable or its complement (value 0 or 1), the dependent link `1 - Σ q` at a
terminal, and removed links (value 0). Each inner vertex is of one of three kinds: degree at most 1
(removed), degree 2 (its two links carry the same value), or degree at least 3, where the degree
equals `2ι` for an indicator `ι ∈ {0, 1}`, either by substitution or because the node penalty
`(deg - 2z)²` vanishes. The incidence of links and vertices is an arbitrary map `inc`.

Soundness (zero penalty decodes to valid link sets):
- `dep_value_01`, `term_sum_of_dep`, `onehot_sum`, `node_of_pen_zero`: the local steps.
- `decode_path`: with values 0 or 1, degree 1 at both terminals and the local conditions at inner
  vertices, every inner vertex has degree `2ι` with `ι ∈ {0, 1}`.
- `decode_disjoint`, `decode_pair`: a zero disjointness penalty over 0/1 indicators leaves no inner
  vertex with links of both paths.

Completeness (a valid link set has an assignment of penalty zero):
- `complete_terminal`: at a terminal of degree 1 the dependent link has the value `1 - Σ` of the
  others and their pair penalty is zero; `complete_onehot` for terminals without a dependent link.
- `complete_merge`, `complete_prune`: degree 0 or 2 forces equal values at a vertex of degree 2 and
  zero values at a vertex of degree at most 1.
-/

namespace RiskRouting.Decoding

open Finset RiskRouting.Combined

/-! ## Soundness -/

/-- A zero pair penalty makes the dependent link `1 - Σ q` equal to 0 or 1. -/
theorem dep_value_01 {ι : Type*} [DecidableEq ι] (S : Finset ι) (q : ι → ℕ)
    (hq : ∀ i ∈ S, q i ≤ 1) (h0 : ∑ T ∈ S.powersetCard 2, ∏ i ∈ T, q i = 0) :
    1 - ((∑ i ∈ S, q i : ℕ) : ℤ) = 0 ∨ 1 - ((∑ i ∈ S, q i : ℕ) : ℤ) = 1 := by
  have := dep_le_one_of_pairs_zero S q hq h0
  omega

/-- The dependent link makes the degree of its terminal equal to 1 for every assignment. -/
theorem term_sum_of_dep {E : Type*} [DecidableEq E] (I : Finset E) (d : E) (hd : d ∈ I)
    (x : E → ℤ) (hx : x d = 1 - ∑ e ∈ I.erase d, x e) : ∑ e ∈ I, x e = 1 := by
  rw [← Finset.add_sum_erase I x hd, hx]
  ring

/-- A terminal without a dependent link: the penalty `(Σ - 1)²` is zero iff the degree is 1. -/
theorem onehot_sum (d : ℤ) : (d - 1) ^ 2 = 0 ↔ d = 1 := by
  constructor
  · intro h
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    linarith
  · intro h; rw [h]; ring

/-- A zero node penalty `(d - 2z)²` gives `d = 2z`. -/
theorem node_of_pen_zero (d z : ℤ) (h : (d - 2 * z) ^ 2 = 0) : d = 2 * z := by
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  linarith

variable {V E : Type*} [DecidableEq E] (inc : V → Finset E)

/-- **Decoding of one path.** Let all link values be 0 or 1, let both terminals have degree 1, and
let each inner vertex be removed (all its links 0), of degree 2 (two distinct links with the same
value), or have degree `2ι` with `ι ∈ {0, 1}`. Then every inner vertex has degree `2ι` with
`ι ∈ {0, 1}`, so degree 0 or 2. -/
theorem decode_path (s t : V) (x : E → ℤ) (hval : ∀ e, x e = 0 ∨ x e = 1)
    (hin : ∀ v, v ≠ s → v ≠ t →
      (∀ e ∈ inc v, x e = 0) ∨
      (∃ e f, e ≠ f ∧ inc v = {e, f} ∧ x e = x f) ∨
      (∃ ι : ℤ, (ι = 0 ∨ ι = 1) ∧ ∑ e ∈ inc v, x e = 2 * ι)) :
    ∀ v, v ≠ s → v ≠ t → ∃ ι : ℤ, (ι = 0 ∨ ι = 1) ∧ ∑ e ∈ inc v, x e = 2 * ι := by
  intro v hs ht
  rcases hin v hs ht with h | ⟨e, f, hef, hI, hx⟩ | h
  · exact ⟨0, Or.inl rfl, by rw [Finset.sum_eq_zero h]; ring⟩
  · refine ⟨x e, hval e, ?_⟩
    rw [hI, Finset.sum_pair hef, ← hx]
    ring
  · exact h

/-- **Disjointness.** A zero disjointness penalty `Σ_v ι_x(v) ι_y(v)` over 0/1 indicators leaves
no vertex with both indicators 1. -/
theorem decode_disjoint {V : Type*} (T : Finset V) (ix iy : V → ℤ)
    (hx : ∀ v, ix v = 0 ∨ ix v = 1) (hy : ∀ v, iy v = 0 ∨ iy v = 1)
    (h0 : ∑ v ∈ T, ix v * iy v = 0) : ∀ v ∈ T, ix v = 0 ∨ iy v = 0 := by
  have hnn : ∀ v ∈ T, 0 ≤ ix v * iy v := fun v _ => by
    rcases hx v with h | h <;> rcases hy v with h' | h' <;> simp [h, h']
  intro v hv
  have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 v hv
  exact mul_eq_zero.mp this

omit [DecidableEq E] in
/-- **Decoding of a pair.** For two paths with the local conditions of `decode_path`, whose inner
vertices in `T` have degrees `2 ι_x(v)` and `2 ι_y(v)`, a zero disjointness penalty leaves no vertex
of `T` with links of both paths. -/
theorem decode_pair (inc₁ inc₂ : V → Finset E) (T : Finset V) (x y : E → ℤ) (ix iy : V → ℤ)
    (hx : ∀ v, ix v = 0 ∨ ix v = 1) (hy : ∀ v, iy v = 0 ∨ iy v = 1)
    (hdx : ∀ v ∈ T, ∑ e ∈ inc₁ v, x e = 2 * ix v) (hdy : ∀ v ∈ T, ∑ e ∈ inc₂ v, y e = 2 * iy v)
    (h0 : ∑ v ∈ T, ix v * iy v = 0) :
    ∀ v ∈ T, ∑ e ∈ inc₁ v, x e = 0 ∨ ∑ e ∈ inc₂ v, y e = 0 := by
  intro v hv
  rcases decode_disjoint T ix iy hx hy h0 v hv with h | h
  · left; rw [hdx v hv, h]; ring
  · right; rw [hdy v hv, h]; ring

/-! ## Completeness -/

/-- **Terminal.** For a 0/1 link set of degree 1 at a terminal with links `I` and a chosen link
`d ∈ I`, the value of `d` is `1 - Σ` of the others, and the pair penalty of the others is zero. -/
theorem complete_terminal (I : Finset E) (d : E) (hd : d ∈ I) (x : E → ℕ)
    (hx : ∀ e ∈ I, x e ≤ 1) (h1 : ∑ e ∈ I, x e = 1) :
    (x d : ℤ) = 1 - ((∑ e ∈ I.erase d, x e : ℕ) : ℤ) ∧
      ∑ T ∈ (I.erase d).powersetCard 2, ∏ e ∈ T, x e = 0 := by
  have hsplit := Finset.add_sum_erase I x hd
  have hle : ∑ e ∈ I.erase d, x e ≤ 1 := by omega
  refine ⟨by omega, ?_⟩
  have hx' : ∀ e ∈ I.erase d, x e ≤ 1 := fun e he => hx e (Finset.mem_of_mem_erase he)
  rw [sum_pairs_eq_choose _ x hx']
  rw [sum_eq_card_active _ x hx'] at hle
  exact Nat.choose_eq_zero_of_lt (by omega)

omit [DecidableEq E] in
/-- **Terminal without a dependent link.** Degree 1 makes `(Σ - 1)²` zero. -/
theorem complete_onehot (I : Finset E) (x : E → ℕ) (h1 : ∑ e ∈ I, x e = 1) :
    (((∑ e ∈ I, x e : ℕ) : ℤ) - 1) ^ 2 = 0 := by
  rw [h1]; norm_num

/-- **Vertex of degree 2.** Degree 0 or 2 with two distinct 0/1 links gives equal values, so the
merged variable is well defined. -/
theorem complete_merge (e f : E) (hef : e ≠ f) (x : E → ℕ) (he : x e ≤ 1) (hf : x f ≤ 1)
    (hd : ∑ g ∈ ({e, f} : Finset E), x g = 0 ∨ ∑ g ∈ ({e, f} : Finset E), x g = 2) :
    x e = x f := by
  rw [Finset.sum_pair hef] at hd
  omega

omit [DecidableEq E] in
/-- **Removed vertex.** A vertex with at most one link and degree 0 or 2 has all its links 0. -/
theorem complete_prune (I : Finset E) (hI : I.card ≤ 1) (x : E → ℕ) (hx : ∀ e ∈ I, x e ≤ 1)
    (hd : ∑ e ∈ I, x e = 0 ∨ ∑ e ∈ I, x e = 2) : ∀ e ∈ I, x e = 0 := by
  have hle : ∑ e ∈ I, x e ≤ I.card := by
    calc ∑ e ∈ I, x e ≤ ∑ _e ∈ I, 1 := Finset.sum_le_sum hx
      _ = I.card := by simp
  have h0 : ∑ e ∈ I, x e = 0 := by omega
  exact fun e he => (Finset.sum_eq_zero_iff.mp h0) e he

end RiskRouting.Decoding
