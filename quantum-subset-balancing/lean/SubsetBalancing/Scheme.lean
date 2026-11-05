import SubsetBalancing.Representations

/-!
# Instances: pair counts and the empty scheme

`good_cnt`: a pair of vectors with the alphabets of the lists is a representation for the layout of
its own pair counts, and the labeling is good for that layout. So goodness and representations are
satisfiable for every solution with a coordinate at the pinned value, in any admissible label system.

The empty scheme has the two labels `([0:2d], {d})` and `({d}, [0:2d])`. In each class there is one
pair, `(c + d, d)` and `(d, d - c)`, so `F` is empty and `K = 1`.
-/

open Finset

namespace SubsetBalancing

variable {ι Lab : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Lab]

/-- The layout with the given intervals and the pair counts of `(X, Y)`. -/
def pairLayout (iv : Lab → Label) (L : ι → Lab) (p : Pin ι) (X Y : ι → ℤ) : Layout Lab :=
  ⟨iv, fun l x y => #{i | i ≠ p.coord ∧ L i = l ∧ X i = x ∧ Y i = y}⟩

/-- **Every pair is a representation for its own counts.** If `X` and `Y` have the alphabets of the
lists and `X - Y = D`, then `L` is good for `D` and the layout of the pair counts, and `(X, Y)` is a
representation of `D`. -/
theorem good_cnt {iv : Lab → Label} {L : ι → Lab} {p : Pin ι} {X Y D : ι → ℤ}
    (hX : AlphaX (pairLayout iv L p X Y) L p X) (hY : AlphaY (pairLayout iv L p X Y) L p Y)
    (hD : X - Y = D) :
    Good L (pairLayout iv L p X Y) p D ∧ IsRep L (pairLayout iv L p X Y) p D X Y := by
  refine ⟨⟨?_, fun l e => ?_⟩, ⟨hX, hY, hD, fun l x _ y _ => rfl⟩⟩
  · rw [← hD]
    simp [hX.pin, hY.pin]
  · have hdi : ∀ i, D i = X i - Y i := fun i => by rw [← hD]; rfl
    have hmaps : ∀ i ∈ ({i | i ≠ p.coord ∧ L i = l ∧ D i = e} : Finset ι),
        X i ∈ (pairLayout iv L p X Y).cSyms l e := by
      intro i hi
      obtain ⟨h1, rfl, h3⟩ := (mem_filter.mp hi).2
      refine mem_filter.mpr ⟨hX.mem i h1, ?_⟩
      have h4 : X i - e = Y i := by
        rw [← h3, hdi]
        omega
      rw [h4]
      exact hY.mem i h1
    rw [card_eq_sum_card_fiberwise hmaps]
    refine sum_congr rfl fun x _ => ?_
    show _ = #{i | i ≠ p.coord ∧ L i = l ∧ X i = x ∧ Y i = x - e}
    congr 1
    ext i
    have := hdi i
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, h2, h4, by omega⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2, by omega⟩, h3⟩

/-- On a good labeling of a layout where `S` or `T` is a single point on each label, `K = 1`. -/
theorem K_eq_one [Fintype Lab] {L : ι → Lab} {ν : Layout Lab} {p : Pin ι} {D : ι → ℤ}
    (hD : Good L ν p D) (h : ∀ l, #(ν.iv l).S ≤ 1 ∨ #(ν.iv l).T ≤ 1) : ν.K = 1 := by
  have h1 := card_reps_le_one (free_eq_empty (L := L) (p := p) (D := D) h)
  rw [card_reps hD] at h1
  have h2 := ν.K_pos
  omega

namespace Label

/-- The label `([0:2d], {d})` of the empty scheme. -/
def emptyA (d : ℤ) : Label := ⟨0, 2 * d, d, d⟩

/-- The label `({d}, [0:2d])` of the empty scheme. -/
def emptyB (d : ℤ) : Label := ⟨d, d, 0, 2 * d⟩

theorem emptyA_inside (d : ℤ) : (emptyA d).Inside d := by
  intro x hx y hy
  have h1 := mem_S.mp hx
  have h2 := mem_T.mp hy
  simp only [emptyA] at h1 h2
  rw [abs_le]
  omega

theorem emptyB_inside (d : ℤ) : (emptyB d).Inside d := by
  intro x hx y hy
  have h1 := mem_S.mp hx
  have h2 := mem_T.mp hy
  simp only [emptyB] at h1 h2
  rw [abs_le]
  omega

theorem card_emptyA_T (d : ℤ) : #(emptyA d).T ≤ 1 := by
  simp [emptyA, T]

theorem card_emptyB_S (d : ℤ) : #(emptyB d).S ≤ 1 := by
  simp [emptyB, S]

/-- Every value `c ∈ [-d:d]` has the pair `(c + d, d)` in the first label. -/
theorem emptyA_pair {d c : ℤ} (hc : |c| ≤ d) : c + d ∈ (emptyA d).S ∧ d ∈ (emptyA d).T := by
  have := abs_le.mp hc
  simp only [mem_S, mem_T, emptyA]
  omega

/-- Every value `c ∈ [-d:d]` has the pair `(d, d - c)` in the second label. -/
theorem emptyB_pair {d c : ℤ} (hc : |c| ≤ d) : d ∈ (emptyB d).S ∧ d - c ∈ (emptyB d).T := by
  have := abs_le.mp hc
  simp only [mem_S, mem_T, emptyB]
  omega

end Label

omit [DecidableEq Lab] in
/-- **The empty scheme has no free coordinates.** -/
theorem free_empty_scheme {L : ι → Lab} {ν : Layout Lab} {p : Pin ι} {D : ι → ℤ} {d : ℤ}
    (h : ∀ l, ν.iv l = Label.emptyA d ∨ ν.iv l = Label.emptyB d) : free L ν p D = ∅ := by
  refine free_eq_empty fun l => ?_
  rcases h l with h1 | h1
  · rw [h1]
    exact Or.inr (Label.card_emptyA_T d)
  · rw [h1]
    exact Or.inl (Label.card_emptyB_S d)

end SubsetBalancing
