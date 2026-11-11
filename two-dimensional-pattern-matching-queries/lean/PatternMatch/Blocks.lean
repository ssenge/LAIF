import Mathlib

/-!
# Blocks of starts in pattern matching

Combinatorial lemmas behind the block procedures for one- and two-dimensional pattern matching:
periods and occurrences, the rotation argument for periodic segments, the existence of a
deterministic sample by halving, the exclusions implied by a passing start, the two extreme
passing starts of a block, the dominance order in two dimensions, and duels.
-/

namespace PatternMatch

/-! ## Periods -/

/-- `d` is a period of the word `p` of length `m`. -/
def IsPeriod {α : Type*} (p : ℕ → α) (m d : ℕ) : Prop :=
  ∀ y, y + d < m → p y = p (y + d)

/-- The word `p` of length `m` occurs in `S` at `x`. -/
def Occ {α : Type*} (S p : ℕ → α) (m x : ℕ) : Prop :=
  ∀ i, i < m → S (x + i) = p i

/-- Two occurrences at distance `d` make `d` a period. -/
theorem period_of_occ {α : Type*} {S p : ℕ → α} {m x d : ℕ}
    (h1 : Occ S p m x) (h2 : Occ S p m (x + d)) : IsPeriod p m d := by
  intro y hy
  have a := h1 (y + d) hy
  have b := h2 y (by omega)
  have e : x + (y + d) = x + d + y := by ring
  rw [e] at a
  exact b.symm.trans a

/-- Lemma 1(a): occurrences lie at least the smallest period `L` apart. -/
theorem occ_gap {α : Type*} {S p : ℕ → α} {m L x x' : ℕ}
    (hL : ∀ d, 0 < d → IsPeriod p m d → L ≤ d) (hLm : L ≤ m)
    (h1 : Occ S p m x) (h2 : Occ S p m x') (hlt : x < x') : L ≤ x' - x := by
  by_cases hd : x' - x < m
  · have e : x' = x + (x' - x) := by omega
    rw [e] at h2
    exact hL _ (by omega) (period_of_occ h1 h2)
  · omega

/-- An infinite word with periods `t` and `L` has the period `gcd t L`. -/
theorem gcd_period {α : Type*} (w : ℕ → α) {t L : ℕ} (hL : 0 < L)
    (ht : ∀ i, w (i + t) = w i) (hLp : ∀ i, w (i + L) = w i) :
    ∀ i, w (i + Nat.gcd t L) = w i := by
  have hmod : ∀ i, w i = w (i % L) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases h : i < L
      · rw [Nat.mod_eq_of_lt h]
      · have e : i = (i - L) + L := by omega
        rw [e, hLp, Nat.add_mod_right]
        exact ih _ (by omega)
  have htc : ∀ c i, w (i + t * c) = w i := by
    intro c
    induction c with
    | zero => intro i; simp
    | succ c ih =>
      intro i
      have e : i + t * (c + 1) = (i + t * c) + t := by ring
      rw [e, ht, ih]
  intro i
  by_cases hg : Nat.gcd t L < L
  · obtain ⟨c, -, hc⟩ := Nat.exists_mul_mod_eq_gcd hg
    rw [hmod (i + Nat.gcd t L), ← htc c i, hmod (i + t * c)]
    congr 1
    rw [← Nat.add_mod_mod i (t * c) L, hc]
  · have hgL : Nat.gcd t L = L := le_antisymm (Nat.gcd_le_right _ hL) (by omega)
    rw [hgL, hLp]

/-- Lemma 1(b): in an `L`-periodic word, two windows of length `L` that both equal the
first `L` letters of a word with smallest period `L` start in the same residue class modulo `L`.
Here `w` is the periodic word read from the left end of the segment, and `q` the letters of the
pattern extended with period `L`. -/
theorem residue_unique {α : Type*} {w q : ℕ → α} {L m t : ℕ} (hL : 0 < L) (hLm : L ≤ m)
    (hmin : ∀ d, 0 < d → IsPeriod q m d → L ≤ d)
    (hq : ∀ i, q (i + L) = q i) (hw : ∀ i, w (i + L) = w i)
    {x : ℕ} (hx : ∀ i, i < L → w (x + i) = q i) (hxt : ∀ i, i < L → w (x + t + i) = q i) :
    t % L = 0 := by
  have hmod : ∀ (v : ℕ → α), (∀ i, v (i + L) = v i) → ∀ i, v i = v (i % L) := by
    intro v hv i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases h : i < L
      · rw [Nat.mod_eq_of_lt h]
      · have e : i = (i - L) + L := by omega
        rw [e, hv, Nat.add_mod_right]
        exact ih _ (by omega)
  have hwq : ∀ i, w (x + i) = q i := by
    intro i
    have h1 : w (x + i) = w (x + i % L) := by
      rw [hmod w hw (x + i), hmod w hw (x + i % L)]
      congr 1
      rw [Nat.add_mod_mod]
    rw [h1, hx _ (Nat.mod_lt _ hL), ← hmod q hq]
  have hwq' : ∀ i, w (x + t + i) = q i := by
    intro i
    have h1 : w (x + t + i) = w (x + t + i % L) := by
      rw [hmod w hw (x + t + i), hmod w hw (x + t + i % L)]
      congr 1
      rw [Nat.add_mod_mod]
    rw [h1, hxt _ (Nat.mod_lt _ hL), ← hmod q hq]
  have hqt : ∀ i, q (i + t % L) = q i := by
    intro i
    have e1 : q (i + t) = q i := by
      rw [← hwq' i, ← hwq (i + t)]
      congr 1
      ring
    have e2 : q (i + t) = q (i + t % L) := by
      rw [hmod q hq (i + t), hmod q hq (i + t % L)]
      congr 1
      rw [Nat.add_mod_mod]
    rw [← e2, e1]
  by_contra hne
  have hpos : 0 < t % L := Nat.pos_of_ne_zero hne
  have hg := gcd_period q hL hqt hq
  have hgpos : 0 < Nat.gcd (t % L) L := Nat.gcd_pos_of_pos_left _ hpos
  have hgle : Nat.gcd (t % L) L ≤ t % L := Nat.gcd_le_left _ hpos
  have hlt : t % L < L := Nat.mod_lt _ hL
  have := hmin _ hgpos (fun y _ => (hg y).symm)
  omega

/-! ## Deterministic samples -/

/-- Lemma 5 (and the combinatorial core of Lemma 2): if the copies in `S` are pairwise distinct on
the cells `Z`, a list `D` of cells of `Z` with values and a survivor `f` exist such that `f` has the
listed values, every other copy differs from a listed value, and `2 ^ D.length ≤ S.card`. -/
theorem sample_exists {ι κ α : Type*} [DecidableEq ι] [DecidableEq α] (v : ι → κ → α) (Z : Set κ) :
    ∀ (S : Finset ι), S.Nonempty →
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∃ z ∈ Z, v i z ≠ v j z) →
      ∃ f ∈ S, ∃ D : List (κ × α), (∀ zc ∈ D, zc.1 ∈ Z) ∧ (∀ zc ∈ D, v f zc.1 = zc.2) ∧
        (∀ j ∈ S, j ≠ f → ∃ zc ∈ D, v j zc.1 ≠ zc.2) ∧ 2 ^ D.length ≤ S.card := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hne hdist
    by_cases h1 : S.card ≤ 1
    · obtain ⟨f, hf⟩ := hne
      refine ⟨f, hf, [], by simp, by simp, ?_, by simpa using Finset.card_pos.mpr ⟨f, hf⟩⟩
      intro j hj hjf
      exact absurd (Finset.card_le_one.mp h1 j hj f hf) hjf
    · obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
      obtain ⟨z, hz, hv⟩ := hdist i hi j hj hij
      set A := S.filter (fun k => v k z = v i z) with hA
      set B := S.filter (fun k => v k z = v j z) with hB
      have hdisj : Disjoint A B := by
        rw [Finset.disjoint_filter]
        intro k _ h1 h2
        exact hv (h1.symm.trans h2)
      have hsum : A.card + B.card ≤ S.card := by
        rw [← Finset.card_union_of_disjoint hdisj]
        exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _)
          (Finset.filter_subset _ _))
      have key : ∀ (T : Finset ι) (c : α), T = S.filter (fun k => v k z = c) → T.Nonempty →
          2 * T.card ≤ S.card →
          ∃ f ∈ S, ∃ D : List (κ × α), (∀ zc ∈ D, zc.1 ∈ Z) ∧ (∀ zc ∈ D, v f zc.1 = zc.2) ∧
            (∀ j ∈ S, j ≠ f → ∃ zc ∈ D, v j zc.1 ≠ zc.2) ∧ 2 ^ D.length ≤ S.card := by
        intro T c hT hTne hT2
        have hsub : T ⊂ S := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hT ▸ Finset.filter_subset _ _, ?_⟩
          intro he
          have := hTne.card_pos
          rw [he] at hT2
          omega
        have hTd : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → ∃ z ∈ Z, v a z ≠ v b z := fun a ha b hb hab =>
          hdist a (hsub.1 ha) b (hsub.1 hb) hab
        obtain ⟨f, hf, D, hDZ, hfD, hjD, hlen⟩ := ih T hsub hTne hTd
        have hfc : v f z = c := by
          rw [hT] at hf
          exact (Finset.mem_filter.mp hf).2
        refine ⟨f, hsub.1 hf, (z, c) :: D, ?_, ?_, ?_, ?_⟩
        · intro zc hzc
          rcases List.mem_cons.mp hzc with h | h
          · rw [h]; exact hz
          · exact hDZ zc h
        · intro zc hzc
          rcases List.mem_cons.mp hzc with h | h
          · rw [h]; exact hfc
          · exact hfD zc h
        · intro k hk hkf
          by_cases hkT : k ∈ T
          · obtain ⟨zc, hzc, hne'⟩ := hjD k hkT hkf
            exact ⟨zc, List.mem_cons_of_mem _ hzc, hne'⟩
          · refine ⟨(z, c), List.mem_cons_self .., ?_⟩
            intro heq
            apply hkT
            rw [hT]
            exact Finset.mem_filter.mpr ⟨hk, heq⟩
        · simp only [List.length_cons, pow_succ]
          calc 2 ^ D.length * 2 ≤ T.card * 2 := Nat.mul_le_mul_right _ hlen
            _ ≤ S.card := by omega
      have hAne : A.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
      have hBne : B.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, rfl⟩⟩
      by_cases hAB : A.card ≤ B.card
      · exact key A (v i z) hA hAne (by omega)
      · exact key B (v j z) hB hBne (by omega)

/-! ## Passing starts in one dimension -/

/-- A sample of the copies `0, …, L - 1` of a word `p` of length `m`: cells `z t` with values
`c t`, survivor `f`; every other copy is defined at some cell and differs there. -/
structure Sample1 {α : Type*} (p : ℤ → α) (m L f : ℤ) (k : ℕ) (z : Fin k → ℤ) (c : Fin k → α) :
    Prop where
  surv : 0 ≤ f ∧ f < L
  elim : ∀ j, 0 ≤ j → j < L → j ≠ f → ∃ t, j ≤ z t ∧ z t < j + m ∧ p (z t - j) ≠ c t

/-- Occurrence in a text indexed by the integers. -/
def OccZ {α : Type*} (S p : ℤ → α) (m x : ℤ) : Prop := ∀ i, 0 ≤ i → i < m → S (x + i) = p i

/-- A start passes if the text agrees with copy `f` placed at `x - f` on the sample. -/
def Passes {α : Type*} (S : ℤ → α) (f : ℤ) {k : ℕ} (z : Fin k → ℤ) (c : Fin k → α) (x : ℤ) :
    Prop := ∀ t, S (x - f + z t) = c t

/-- A passing start excludes every other start of `[x - f, x - f + L)`. -/
theorem pass_excludes {α : Type*} {S p : ℤ → α} {m L f : ℤ} {k : ℕ} {z : Fin k → ℤ}
    {c : Fin k → α} (hs : Sample1 p m L f k z c) {q : ℤ} (hq : Passes S f z c q) {y : ℤ}
    (hy1 : q - f ≤ y) (hy2 : y < q - f + L) (hyq : y ≠ q) : ¬ OccZ S p m y := by
  intro hocc
  obtain ⟨t, h1, h2, hne⟩ := hs.elim (y - q + f) (by omega) (by omega) (by omega)
  have a := hocc (z t - (y - q + f)) (by omega) (by omega)
  have e : y + (z t - (y - q + f)) = q - f + z t := by ring
  rw [e, hq t] at a
  exact hne a.symm

/-- Lemma 3, case `L ≤ 2f`: in an interval of at most `L` starts, every occurrence is the
rightmost passing start `x₁` or the rightmost passing start `x₂` below `x₁ - f`
(take `x₂ < lo` if there is none). -/
theorem two_right {occ pass : ℤ → Prop} {f L lo hi x₁ x₂ : ℤ}
    (hpass : ∀ x, occ x → pass x)
    (hkill : ∀ q, pass q → ∀ y, q - f ≤ y → y < q - f + L → y ≠ q → ¬ occ y)
    (hf : L ≤ 2 * f) (hfL : f < L) (hI : hi - lo ≤ L)
    (h1 : lo ≤ x₁ ∧ x₁ < hi ∧ pass x₁) (h1max : ∀ y, lo ≤ y → y < hi → pass y → y ≤ x₁)
    (h2max : ∀ y, lo ≤ y → y < x₁ - f → pass y → y ≤ x₂)
    (h2 : x₂ < lo ∨ (pass x₂ ∧ x₂ < x₁ - f)) :
    ∀ y, lo ≤ y → y < hi → occ y → y = x₁ ∨ y = x₂ := by
  intro y hy1 hy2 hy
  have hp := hpass y hy
  have hle := h1max y hy1 hy2 hp
  by_cases e1 : y = x₁
  · exact Or.inl e1
  by_cases hyf : x₁ - f ≤ y
  · exact absurd hy (hkill x₁ h1.2.2 y hyf (by omega) e1)
  have hle2 := h2max y hy1 (by omega) hp
  by_cases e2 : y = x₂
  · exact Or.inr e2
  rcases h2 with h2 | ⟨h2, h2lt⟩
  · omega
  by_cases hyf2 : x₂ - f ≤ y
  · exact absurd hy (hkill x₂ h2 y hyf2 (by omega) e2)
  · omega

/-- Lemma 3, case `2f < L`: every occurrence is the leftmost passing start `x₁` or the leftmost
passing start `x₂` from `x₁ - f + L` on (take `x₂ ≥ hi` if there is none). -/
theorem two_left {occ pass : ℤ → Prop} {f L lo hi x₁ x₂ : ℤ}
    (hpass : ∀ x, occ x → pass x)
    (hkill : ∀ q, pass q → ∀ y, q - f ≤ y → y < q - f + L → y ≠ q → ¬ occ y)
    (hf : 2 * f < L) (hf0 : 0 ≤ f) (hI : hi - lo ≤ L)
    (h1 : lo ≤ x₁ ∧ x₁ < hi ∧ pass x₁) (h1min : ∀ y, lo ≤ y → y < hi → pass y → x₁ ≤ y)
    (h2min : ∀ y, x₁ - f + L ≤ y → y < hi → pass y → x₂ ≤ y)
    (h2 : hi ≤ x₂ ∨ (pass x₂ ∧ x₁ - f + L ≤ x₂)) :
    ∀ y, lo ≤ y → y < hi → occ y → y = x₁ ∨ y = x₂ := by
  intro y hy1 hy2 hy
  have hp := hpass y hy
  have hge := h1min y hy1 hy2 hp
  by_cases e1 : y = x₁
  · exact Or.inl e1
  by_cases hyf : y < x₁ - f + L
  · exact absurd hy (hkill x₁ h1.2.2 y (by omega) hyf e1)
  have hge2 := h2min y (by omega) hy2 hp
  by_cases e2 : y = x₂
  · exact Or.inr e2
  rcases h2 with h2 | ⟨h2, h2ge⟩
  · omega
  by_cases hyf2 : y < x₂ - f + L
  · exact absurd hy (hkill x₂ h2 y (by omega) hyf2 e2)
  · omega

/-- Lemma 4: every start `x` of the block `[B, B + (m - L))` has `B + m - 1` in `[x + L, x + m)`. -/
theorem run_cell {B L m x : ℤ} (hx1 : B ≤ x) (hx2 : x < B + (m - L)) :
    x + L ≤ B + m - 1 ∧ B + m - 1 < x + m := by
  constructor <;> omega

/-! ## Two dimensions -/

/-- Occurrence of an `m × m` pattern at `x` in a text indexed by `ℤ × ℤ`. -/
def Occ2 {α : Type*} (T P : ℤ × ℤ → α) (m : ℤ) (x : ℤ × ℤ) : Prop :=
  ∀ u : ℤ × ℤ, 0 ≤ u.1 → u.1 < m → 0 ≤ u.2 → u.2 < m → T (x + u) = P u

/-- A sample of the copies with shifts in `[0, b)²`. -/
structure Sample2 {α : Type*} (P : ℤ × ℤ → α) (m b : ℤ) (f : ℤ × ℤ) (k : ℕ) (z : Fin k → ℤ × ℤ)
    (c : Fin k → α) : Prop where
  elim : ∀ j : ℤ × ℤ, 0 ≤ j.1 → j.1 < b → 0 ≤ j.2 → j.2 < b → j ≠ f →
    ∃ t, j.1 ≤ (z t).1 ∧ (z t).1 < j.1 + m ∧ j.2 ≤ (z t).2 ∧ (z t).2 < j.2 + m ∧ P (z t - j) ≠ c t

/-- A start passes the two-dimensional sample. -/
def Passes2 {α : Type*} (T : ℤ × ℤ → α) (f : ℤ × ℤ) {k : ℕ} (z : Fin k → ℤ × ℤ)
    (c : Fin k → α) (x : ℤ × ℤ) : Prop := ∀ t, T (x - f + z t) = c t

/-- A passing start `q` excludes every other start `x` with `x - q + f ∈ [0, b)²`. -/
theorem pass_excludes2 {α : Type*} {T P : ℤ × ℤ → α} {m b : ℤ} {f : ℤ × ℤ} {k : ℕ}
    {z : Fin k → ℤ × ℤ} {c : Fin k → α} (hs : Sample2 P m b f k z c) {q x : ℤ × ℤ}
    (hq : Passes2 T f z c q) (h1 : 0 ≤ (x - q + f).1) (h2 : (x - q + f).1 < b)
    (h3 : 0 ≤ (x - q + f).2) (h4 : (x - q + f).2 < b) (hxq : x ≠ q) : ¬ Occ2 T P m x := by
  intro hocc
  have hj : x - q + f ≠ f := by
    intro h
    apply hxq
    have := congrArg (· - f) h
    simpa [sub_eq_zero] using this
  obtain ⟨t, a1, a2, a3, a4, hne⟩ := hs.elim _ h1 h2 h3 h4 hj
  have a := hocc (z t - (x - q + f)) (by simp only [Prod.fst_sub]; omega)
    (by simp only [Prod.fst_sub]; omega) (by simp only [Prod.snd_sub]; omega)
    (by simp only [Prod.snd_sub]; omega)
  have e : x + (z t - (x - q + f)) = q - f + z t := by abel
  rw [e, hq t] at a
  exact hne a.symm

/-- Lemma 6, one coordinate: with the side `σ` of the survivor coordinate `f` and blocks of
`b' = ⌊b/2⌋`, a passing start `p` within distance `b'` on the side `σ` covers `x`. -/
theorem side_cover {b f p x : ℤ} (hf0 : 0 ≤ f) (hfb : f < b) (hd : |p - x| < b / 2) :
    (b - 1 - f ≤ f → 0 ≤ p - x → 0 ≤ x - p + f ∧ x - p + f < b) ∧
    (f < b - 1 - f → p - x ≤ 0 → 0 ≤ x - p + f ∧ x - p + f < b) := by
  have h := abs_lt.mp hd
  have h2 : 2 * (b / 2) ≤ b := Int.mul_ediv_self_le (by norm_num)
  constructor
  · intro hs hpx; constructor <;> omega
  · intro hs hpx; constructor <;> omega

/-- Lemma 6: an occurrence `x` is not dominated, in the order given by the sides, by any other
passing start of its block. -/
theorem occ_undominated {α : Type*} {T P : ℤ × ℤ → α} {m b : ℤ} {f : ℤ × ℤ} {k : ℕ}
    {z : Fin k → ℤ × ℤ} {c : Fin k → α} (hs : Sample2 P m b f k z c)
    (hf : 0 ≤ f.1 ∧ f.1 < b ∧ 0 ≤ f.2 ∧ f.2 < b) {p x : ℤ × ℤ} (hp : Passes2 T f z c p)
    (hpx : p ≠ x) (hd1 : |p.1 - x.1| < b / 2) (hd2 : |p.2 - x.2| < b / 2)
    (hσ1 : (b - 1 - f.1 ≤ f.1 ∧ 0 ≤ p.1 - x.1) ∨ (f.1 < b - 1 - f.1 ∧ p.1 - x.1 ≤ 0))
    (hσ2 : (b - 1 - f.2 ≤ f.2 ∧ 0 ≤ p.2 - x.2) ∨ (f.2 < b - 1 - f.2 ∧ p.2 - x.2 ≤ 0)) :
    ¬ Occ2 T P m x := by
  obtain ⟨c1a, c1b⟩ := side_cover (p := p.1) (x := x.1) hf.1 hf.2.1 hd1
  obtain ⟨c2a, c2b⟩ := side_cover (p := p.2) (x := x.2) hf.2.2.1 hf.2.2.2 hd2
  have r1 : 0 ≤ x.1 - p.1 + f.1 ∧ x.1 - p.1 + f.1 < b := by
    rcases hσ1 with ⟨a, b'⟩ | ⟨a, b'⟩
    · exact c1a a b'
    · exact c1b a b'
  have r2 : 0 ≤ x.2 - p.2 + f.2 ∧ x.2 - p.2 + f.2 < b := by
    rcases hσ2 with ⟨a, b'⟩ | ⟨a, b'⟩
    · exact c2a a b'
    · exact c2b a b'
  exact pass_excludes2 hs hp (by simpa using r1.1) (by simpa using r1.2) (by simpa using r2.1)
    (by simpa using r2.2) (Ne.symm hpx)

/-- A duel: if the copies at `x` and `y` differ at a cell inside both, one query there rules out
one of them. -/
theorem duel {α : Type*} {T P : ℤ × ℤ → α} {m : ℤ} {x y u : ℤ × ℤ}
    (hu : 0 ≤ u.1 ∧ u.1 < m ∧ 0 ≤ u.2 ∧ u.2 < m)
    (hv : 0 ≤ (u - (y - x)).1 ∧ (u - (y - x)).1 < m ∧ 0 ≤ (u - (y - x)).2 ∧ (u - (y - x)).2 < m)
    (hw : P u ≠ P (u - (y - x))) :
    (T (x + u) = P u → ¬ Occ2 T P m y) ∧ (T (x + u) ≠ P u → ¬ Occ2 T P m x) := by
  constructor
  · intro h hy
    have a := hy (u - (y - x)) hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
    have e : y + (u - (y - x)) = x + u := by abel
    rw [e, h] at a
    exact hw a
  · intro h hx
    exact h (hx u hu.1 hu.2.1 hu.2.2.1 hu.2.2.2)

end PatternMatch
