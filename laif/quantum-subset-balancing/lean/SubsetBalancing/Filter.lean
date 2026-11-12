import SubsetBalancing.Prob
import SubsetBalancing.Representations
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Int

/-!
# Lemma 3: the filter

The deterministic core: the Cauchy step on classes, and the step over the prime as a Markov
argument on a uniform choice from a finite set `Ps` of moduli. The only arithmetic fact it uses is
`PrimeHit Ps B δ`, that a nonzero integer of size at most `B` is divisible by at most a fraction `δ`
of `Ps`. For primes above `P₀`, the bound on the number of prime divisors is proved in
`primeHit_of_card`, and only the number of primes in `Ps` is left as an input.

Items are the values of representations, distinct integers as Lemma 2 shows, and classes are their
residues. So `Z` counts pairs `v < w` of values with `v ≡ w` modulo `P`.
-/

open Finset

namespace SubsetBalancing

/-! ## The Cauchy step -/

section Cauchy

variable {κ γ : Type*} [LinearOrder κ] [DecidableEq γ]

/-- The colliding pairs of `K` under the class map `c`, each unordered pair once. -/
def collisions (K : Finset κ) (c : κ → γ) : Finset (κ × κ) :=
  (K ×ˢ K).filter fun p => p.1 < p.2 ∧ c p.1 = c p.2

/-- The sum of squares of the class sizes counts the diagonal once and each colliding pair twice. -/
theorem sum_sq_classes (K : Finset κ) (c : κ → γ) :
    ∑ b ∈ K.image c, #{a ∈ K | c a = b} ^ 2 = #K + 2 * #(collisions K c) := by
  set Q := (K ×ˢ K).filter fun p => c p.1 = c p.2 with hQ
  have h1 : ∑ b ∈ K.image c, #{a ∈ K | c a = b} ^ 2 = #Q := by
    have hi : Q.image (fun p => c p.1) = K.image c := by
      ext b
      simp only [hQ, mem_image, mem_filter, mem_product, Prod.exists]
      constructor
      · rintro ⟨a, a', ⟨⟨ha, -⟩, -⟩, rfl⟩
        exact ⟨a, ha, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨a, a, ⟨⟨ha, ha⟩, rfl⟩, rfl⟩
    rw [card_eq_sum_card_image (fun p : κ × κ => c p.1) Q, hi]
    refine sum_congr rfl fun b _ => ?_
    rw [sq, ← card_product]
    congr 1
    ext ⟨a, a'⟩
    simp only [hQ, mem_filter, mem_product]
    constructor
    · rintro ⟨⟨ha, rfl⟩, ha', h⟩
      exact ⟨⟨⟨ha, ha'⟩, h.symm⟩, rfl⟩
    · rintro ⟨⟨⟨ha, ha'⟩, h⟩, h2⟩
      exact ⟨⟨ha, h2⟩, ha', h ▸ h2⟩
  have hdiag : #(Q.filter fun p => p.1 = p.2) = #K := by
    symm
    refine card_nbij (fun a => (a, a)) ?_ ?_ ?_
    · intro a ha
      simpa [hQ] using ha
    · intro a _ b _ h
      exact congrArg Prod.fst h
    · rintro ⟨a, a'⟩ h
      simp only [hQ, mem_coe, mem_filter, mem_product] at h
      obtain ⟨⟨⟨ha, -⟩, -⟩, h2⟩ := h
      exact ⟨a, ha, by simp [← h2]⟩
  have hlt : Q.filter (fun p => p.1 < p.2) = collisions K c := by
    ext p
    simp only [hQ, collisions, mem_filter]
    tauto
  have hgt : #(Q.filter fun p => p.2 < p.1) = #(collisions K c) := by
    rw [← hlt]
    refine card_nbij (fun p => (p.2, p.1)) ?_ ?_ ?_
    · rintro ⟨a, b⟩ h
      simp only [hQ, mem_coe, mem_filter, mem_product] at h ⊢
      exact ⟨⟨⟨h.1.1.2, h.1.1.1⟩, h.1.2.symm⟩, h.2⟩
    · rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ h
      simp only [Prod.mk.injEq] at h
      simp [h.1, h.2]
    · rintro ⟨a, b⟩ h
      simp only [hQ, mem_coe, mem_filter, mem_product] at h
      refine ⟨(b, a), ?_, rfl⟩
      simp only [hQ, mem_coe, mem_filter, mem_product]
      exact ⟨⟨⟨h.1.1.2, h.1.1.1⟩, h.1.2.symm⟩, h.2⟩
  have hsplit : #Q = #(Q.filter fun p => p.1 = p.2) + #(Q.filter fun p => p.1 < p.2)
      + #(Q.filter fun p => p.2 < p.1) := by
    have h3 := card_filter_add_card_filter_not (s := Q) (fun p => p.1 = p.2)
    have h4 := card_filter_add_card_filter_not (s := Q.filter fun p => ¬ p.1 = p.2)
      (fun p => p.1 < p.2)
    have h5 : ((Q.filter fun p => ¬ p.1 = p.2).filter fun p => p.1 < p.2)
        = Q.filter fun p => p.1 < p.2 := by
      ext p
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨h, -⟩, h'⟩
        exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩
        exact ⟨⟨h, h'.ne⟩, h'⟩
    have h6 : ((Q.filter fun p => ¬ p.1 = p.2).filter fun p => ¬ p.1 < p.2)
        = Q.filter fun p => p.2 < p.1 := by
      ext p
      simp only [mem_filter, not_lt]
      constructor
      · rintro ⟨⟨h, h1⟩, h2⟩
        exact ⟨h, lt_of_le_of_ne h2 (Ne.symm h1)⟩
      · rintro ⟨h, h'⟩
        exact ⟨⟨h, h'.ne'⟩, h'.le⟩
    rw [h5, h6] at h4
    omega
  rw [h1, hsplit, hdiag, hlt, hgt]
  ring

/-- **Cauchy step.** `K'` items in `M` classes with `Z` colliding pairs satisfy
`K'² ≤ M (K' + 2 Z)`. -/
theorem cauchy_classes (K : Finset κ) (c : κ → γ) :
    #K ^ 2 ≤ #(K.image c) * (#K + 2 * #(collisions K c)) := by
  have h := sq_sum_le_card_mul_sum_sq (s := K.image c) (f := fun b => #{a ∈ K | c a = b})
    (α := ℕ)
  rw [← card_eq_sum_card_image c K, sum_sq_classes K c] at h
  exact_mod_cast h

theorem collisions_mono {K K' : Finset κ} (h : K' ⊆ K) (c : κ → γ) :
    #(collisions K' c) ≤ #(collisions K c) := by
  apply card_le_card
  intro p hp
  simp only [collisions, mem_filter, mem_product] at hp ⊢
  exact ⟨⟨h hp.1.1, h hp.1.2⟩, hp.2⟩

/-- **The lower bound on the number of classes.** If `K'` is at least half of `K` and `K` has at
most `8 |K| b` colliding pairs, then `K'` occupies at least `|K| / (2 + 64 b)` classes. -/
theorem classes_lower_bound {K K' : Finset κ} (hsub : K' ⊆ K) (hhalf : #K ≤ 2 * #K') (c : κ → γ)
    {b : ℝ} (hb : 0 ≤ b) (hZ : (#(collisions K c) : ℝ) ≤ 8 * #K * b) :
    (#K : ℝ) ≤ #(K'.image c) * (2 + 64 * b) := by
  have hC : ((#K' : ℝ)) ^ 2 ≤ #(K'.image c) * (#K' + 2 * #(collisions K' c)) := by
    exact_mod_cast cauchy_classes K' c
  have hZ' : (#(collisions K' c) : ℝ) ≤ #(collisions K c) := by
    exact_mod_cast collisions_mono hsub c
  have hhalf' : (#K : ℝ) ≤ 2 * #K' := by exact_mod_cast hhalf
  have hM : (0 : ℝ) ≤ #(K'.image c) := by positivity
  rcases Nat.eq_zero_or_pos #K' with h0 | hpos
  · have h1 : (#K : ℝ) ≤ 0 := by simpa [h0] using hhalf'
    have h2 : (0 : ℝ) ≤ #(K'.image c) * (2 + 64 * b) := by positivity
    linarith
  · have hK'pos : (0 : ℝ) < #K' := by exact_mod_cast hpos
    have h3 : (#K' : ℝ) + 2 * #(collisions K' c) ≤ #K' * (1 + 32 * b) := by
      have : (8 : ℝ) * #K * b ≤ 16 * #K' * b := by nlinarith
      nlinarith
    have h4 : (#K' : ℝ) * #K' ≤ #K' * (#(K'.image c) * (1 + 32 * b)) := by
      calc (#K' : ℝ) * #K' = (#K' : ℝ) ^ 2 := by ring
        _ ≤ #(K'.image c) * (#K' + 2 * #(collisions K' c)) := hC
        _ ≤ #(K'.image c) * (#K' * (1 + 32 * b)) := mul_le_mul_of_nonneg_left h3 hM
        _ = #K' * (#(K'.image c) * (1 + 32 * b)) := by ring
    have h5 : (#K' : ℝ) ≤ #(K'.image c) * (1 + 32 * b) := le_of_mul_le_mul_left h4 hK'pos
    nlinarith

end Cauchy

/-! ## Divisors and the uniform choice of the modulus -/

/-- A nonzero integer of absolute value at most `B` is divisible by at most a fraction `δ` of the
moduli in `Ps`. -/
def PrimeHit (Ps : Finset ℕ) (B : ℤ) (δ : ℝ) : Prop :=
  ∀ d : ℤ, d ≠ 0 → |d| ≤ B → (#(Ps.filter fun P : ℕ => (P : ℤ) ∣ d) : ℝ) ≤ δ * #Ps

/-- A nonzero integer below `P₀ ^ (r + 1)` has at most `r` prime divisors at or above `P₀`. -/
theorem card_prime_divisors_le {Ps : Finset ℕ} (hprime : ∀ P ∈ Ps, P.Prime) {P₀ r : ℕ}
    (hlarge : ∀ P ∈ Ps, P₀ ≤ P) (hP₀ : 1 ≤ P₀) {d : ℤ} (hd : d ≠ 0)
    (hB : |d| < (P₀ : ℤ) ^ (r + 1)) : #(Ps.filter fun P : ℕ => (P : ℤ) ∣ d) ≤ r := by
  set Q := Ps.filter (fun P : ℕ => (P : ℤ) ∣ d) with hQ
  have hdvd : ∏ P ∈ Q, P ∣ d.natAbs := by
    apply Finset.prod_primes_dvd
    · intro P hP
      exact (hprime P (mem_filter.mp hP).1).prime
    · intro P hP
      exact Int.natCast_dvd.mp (mem_filter.mp hP).2
  have hle : ∏ P ∈ Q, P ≤ d.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hd) hdvd
  have hpow : P₀ ^ #Q ≤ ∏ P ∈ Q, P := by
    have := Finset.pow_card_le_prod Q (fun P => P) P₀ fun P hP => hlarge P (mem_filter.mp hP).1
    simpa using this
  have hlt : d.natAbs < P₀ ^ (r + 1) := by
    have h1 : (d.natAbs : ℤ) < (P₀ : ℤ) ^ (r + 1) := by rwa [Int.natCast_natAbs]
    exact_mod_cast h1
  have hfin : P₀ ^ #Q < P₀ ^ (r + 1) := lt_of_le_of_lt (hpow.trans hle) hlt
  have hP₀' : 1 < P₀ ∨ P₀ = 1 := by omega
  rcases hP₀' with h1 | h1
  · have := (Nat.pow_lt_pow_iff_right h1).mp hfin
    omega
  · subst h1
    simp at hfin

/-- With the bound on prime divisors proved, `PrimeHit` needs only a lower bound `N` on the number
of primes in `Ps`: then `δ = r / N` works. -/
theorem primeHit_of_card {Ps : Finset ℕ} (hprime : ∀ P ∈ Ps, P.Prime) {P₀ r N : ℕ}
    (hlarge : ∀ P ∈ Ps, P₀ ≤ P) (hP₀ : 1 ≤ P₀) (hN : 0 < N) (hcard : N ≤ #Ps) {B : ℤ}
    (hB : B < (P₀ : ℤ) ^ (r + 1)) : PrimeHit Ps B ((r : ℝ) / N) := by
  intro d hd hdB
  have h := card_prime_divisors_le hprime hlarge hP₀ hd (lt_of_le_of_lt hdB hB)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) ≤ #Ps := by exact_mod_cast hcard
  have h2 : (#(Ps.filter fun P : ℕ => (P : ℤ) ∣ d) : ℝ) ≤ r := by exact_mod_cast h
  have h3 : (1 : ℝ) ≤ (#Ps : ℝ) / N := by rwa [le_div_iff₀ hN', one_mul]
  calc (#(Ps.filter fun P : ℕ => (P : ℤ) ∣ d) : ℝ) ≤ r := h2
    _ = (r : ℝ) * 1 := (mul_one _).symm
    _ ≤ (r : ℝ) * ((#Ps : ℝ) / N) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (r : ℝ) / N * #Ps := by ring

/-- The elements of `S` whose `d` is nonzero and divisible by `P`. -/
def hits {α : Type*} (S : Finset α) (d : α → ℤ) (P : ℕ) : ℕ :=
  #{x ∈ S | d x ≠ 0 ∧ (P : ℤ) ∣ d x}

/-- Double counting: the mean over `P` of the hits of `S` is at most `|S| δ`. -/
theorem sum_hits_le {α : Type*} (Ps : Finset ℕ) (S : Finset α) (d : α → ℤ) {B : ℤ} {δ : ℝ}
    (hit : PrimeHit Ps B δ) (hδ : 0 ≤ δ) (hd : ∀ x ∈ S, |d x| ≤ B) :
    ∑ P ∈ Ps, (hits S d P : ℝ) ≤ #S * (δ * #Ps) := by
  have h : ∑ P ∈ Ps, hits S d P = ∑ x ∈ S, #(Ps.filter fun P : ℕ => d x ≠ 0 ∧ (P : ℤ) ∣ d x) := by
    simp only [hits, card_filter]
    rw [sum_comm]
  have h2 : ∀ x ∈ S, (#(Ps.filter fun P : ℕ => d x ≠ 0 ∧ (P : ℤ) ∣ d x) : ℝ) ≤ δ * #Ps := by
    intro x hx
    by_cases h0 : d x = 0
    · have : (Ps.filter fun P : ℕ => d x ≠ 0 ∧ (P : ℤ) ∣ d x) = ∅ := by
        simp [h0]
      rw [this]
      simp only [card_empty, Nat.cast_zero]
      positivity
    · have : (Ps.filter fun P : ℕ => d x ≠ 0 ∧ (P : ℤ) ∣ d x)
          = Ps.filter fun P : ℕ => (P : ℤ) ∣ d x := by
        simp [h0]
      rw [this]
      exact hit (d x) h0 (hd x hx)
  have h3 : ∑ x ∈ S, (#(Ps.filter fun P : ℕ => d x ≠ 0 ∧ (P : ℤ) ∣ d x) : ℝ) ≤ ∑ _x ∈ S, δ * #Ps :=
    sum_le_sum h2
  rw [sum_const, nsmul_eq_mul] at h3
  calc ∑ P ∈ Ps, (hits S d P : ℝ) = ((∑ P ∈ Ps, hits S d P : ℕ) : ℝ) := by push_cast; rfl
    _ = ((∑ x ∈ S, #(Ps.filter fun P : ℕ => d x ≠ 0 ∧ (P : ℤ) ∣ d x) : ℕ) : ℝ) := by rw [h]
    _ = ∑ x ∈ S, (#(Ps.filter fun P : ℕ => d x ≠ 0 ∧ (P : ℤ) ∣ d x) : ℝ) := by push_cast; rfl
    _ ≤ #S * (δ * #Ps) := h3

/-! ## The step over the prime -/

section Main

variable {α β : Type*}

/-- The residue class of an integer modulo `P`. -/
def res (P : ℕ) (v : ℤ) : ℤ := v % (P : ℤ)

theorem dvd_of_res_eq {P : ℕ} {a b : ℤ} (h : res P a = res P b) : (P : ℤ) ∣ a - b :=
  (Int.modEq_iff_dvd.mp (show b % (P : ℤ) = a % (P : ℤ) from h.symm))

/-- A prime is good for the values `V` and the lists `Sx`, `Sy` if there is a set `R` of residues,
of size at least `|V| / (2 + 64 b)`, such that each residue in `R` is the residue of a value `v` for
which at most `T/2` elements of the two lists in that residue have an exact sum other than `v`. -/
def GoodPrime (V : Finset ℤ) (Sx : Finset α) (sx : α → ℤ) (Sy : Finset β) (sy : β → ℤ)
    (T b : ℝ) (P : ℕ) : Prop :=
  ∃ R : Finset ℤ, (#V : ℝ) ≤ #R * (2 + 64 * b) ∧
    ∀ ρ ∈ R, ∃ v ∈ V, res P v = ρ ∧
      ((#{x ∈ Sx | res P (sx x) = ρ ∧ sx x ≠ v} + #{y ∈ Sy | res P (sy y) = ρ ∧ sy y ≠ v} : ℕ) : ℝ)
        ≤ T / 2

/-- **Lemma 3.** Let `V` be the `K` distinct values of the representations, and let the prime be a
uniform element of `Ps`, such that a nonzero difference of size at most `B` is divisible by at most a
fraction `δ` of `Ps`. Let both lists have at most `U` elements, `64 U δ ≤ T` and `K δ ≤ b`. Then
with probability at least `3/4` the prime is good. In the application `δ = O(n) / P₀`, `P₀ = K s`
with `s ≥ 1` and `T = c n U / P₀`, so `b = O(n)`. -/
theorem filter_lemma (Ps : Finset ℕ) (hPs : Ps.Nonempty) (V : Finset ℤ) (Sx : Finset α) (sx : α → ℤ)
    (Sy : Finset β) (sy : β → ℤ) {B : ℤ} {U δ T b : ℝ} (hit : PrimeHit Ps B δ) (hδ : 0 ≤ δ)
    (hUx : (#Sx : ℝ) ≤ U) (hUy : (#Sy : ℝ) ≤ U)
    (hVV : ∀ p ∈ V ×ˢ V, |p.2 - p.1| ≤ B)
    (hXV : ∀ v ∈ V, ∀ x ∈ Sx, |sx x - v| ≤ B) (hYV : ∀ v ∈ V, ∀ y ∈ Sy, |sy y - v| ≤ B)
    (hT : 64 * U * δ ≤ T) (hb : (#V : ℝ) * δ ≤ b) :
    (3 : ℝ) / 4 ≤ prob Ps (GoodPrime V Sx sx Sy sy T b) := by
  classical
  have hP0 : (0 : ℝ) < #Ps := by exact_mod_cast card_pos.mpr hPs
  have hU0 : 0 ≤ U := le_trans (by positivity) hUx
  set K : ℝ := (#V : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  -- the excess of a value at a prime
  set e : ℕ → ℤ → ℝ := fun P v =>
    (hits Sx (fun x => sx x - v) P : ℝ) + (hits Sy (fun y => sy y - v) P : ℝ) with he
  have he0 : ∀ P v, 0 ≤ e P v := fun P v => by simp only [he]; positivity
  set g : ℕ → ℝ := fun P => ∑ v ∈ V, e P v with hg
  have hg0 : ∀ P ∈ Ps, 0 ≤ g P := fun P _ => sum_nonneg fun v _ => he0 P v
  have hgmean : ∑ P ∈ Ps, g P ≤ #Ps * (K * (2 * U * δ)) := by
    have h1 : ∑ P ∈ Ps, g P = ∑ v ∈ V, ∑ P ∈ Ps, e P v := sum_comm
    have h2 : ∀ v ∈ V, ∑ P ∈ Ps, e P v ≤ 2 * U * δ * #Ps := by
      intro v hv
      have h3 := sum_hits_le Ps Sx (fun x => sx x - v) hit hδ (hXV v hv)
      have h4 := sum_hits_le Ps Sy (fun y => sy y - v) hit hδ (hYV v hv)
      have h5 : ∑ P ∈ Ps, e P v = ∑ P ∈ Ps, (hits Sx (fun x => sx x - v) P : ℝ)
          + ∑ P ∈ Ps, (hits Sy (fun y => sy y - v) P : ℝ) := sum_add_distrib
      have h6 : (0 : ℝ) ≤ δ * #Ps := by positivity
      have h7 : (#Sx : ℝ) * (δ * #Ps) ≤ U * (δ * #Ps) := mul_le_mul_of_nonneg_right hUx h6
      have h8 : (#Sy : ℝ) * (δ * #Ps) ≤ U * (δ * #Ps) := mul_le_mul_of_nonneg_right hUy h6
      rw [h5]
      linarith
    have h3 : ∑ v ∈ V, ∑ P ∈ Ps, e P v ≤ ∑ _v ∈ V, 2 * U * δ * #Ps := sum_le_sum h2
    rw [sum_const, nsmul_eq_mul] at h3
    rw [h1]
    calc ∑ v ∈ V, ∑ P ∈ Ps, e P v ≤ (#V : ℝ) * (2 * U * δ * #Ps) := h3
      _ = #Ps * (K * (2 * U * δ)) := by rw [hK]; ring
  -- colliding pairs of values at a prime
  set z : ℕ → ℝ := fun P => (#(collisions V (res P)) : ℝ) with hz
  have hz0 : ∀ P ∈ Ps, 0 ≤ z P := fun P _ => by simp only [hz]; positivity
  have hzmean : ∑ P ∈ Ps, z P ≤ #Ps * (K * K * δ) := by
    have h1 := sum_hits_le Ps (V ×ˢ V) (fun p => p.2 - p.1) hit hδ hVV
    have h2 : ∀ P ∈ Ps, z P ≤ (hits (V ×ˢ V) (fun p => p.2 - p.1) P : ℝ) := by
      intro P _
      simp only [hz, hits]
      have : #(collisions V (res P)) ≤ #{x ∈ V ×ˢ V | x.2 - x.1 ≠ 0 ∧ (P : ℤ) ∣ x.2 - x.1} := by
        apply card_le_card
        rintro ⟨v, w⟩ hp
        simp only [collisions, mem_filter] at hp ⊢
        refine ⟨hp.1, ?_, dvd_of_res_eq hp.2.2.symm⟩
        have := hp.2.1
        exact sub_ne_zero.mpr this.ne'
      exact_mod_cast this
    have h3 := sum_le_sum h2
    rw [card_product] at h1
    push_cast at h1
    calc ∑ P ∈ Ps, z P ≤ ∑ P ∈ Ps, (hits (V ×ˢ V) (fun p => p.2 - p.1) P : ℝ) := h3
      _ ≤ (#V : ℝ) * #V * (δ * #Ps) := h1
      _ = #Ps * (K * K * δ) := by rw [hK]; ring
  -- Markov, twice
  have hbad1 := count_above Ps g hg0 hgmean (m := 8) (by norm_num)
  have hbad2 := count_above Ps z hz0 hzmean (m := 8) (by norm_num)
  set G := Ps.filter fun P => g P ≤ 8 * (K * (2 * U * δ)) ∧ z P ≤ 8 * (K * K * δ) with hG
  have hcover : #Ps ≤ #G + #(Ps.filter fun P : ℕ => 8 * (K * (2 * U * δ)) < g P)
      + #(Ps.filter fun P : ℕ => 8 * (K * K * δ) < z P) := by
    have hsub : Ps ⊆ G ∪ (Ps.filter fun P => 8 * (K * (2 * U * δ)) < g P)
        ∪ (Ps.filter fun P => 8 * (K * K * δ) < z P) := by
      intro P hP
      simp only [hG, mem_union, mem_filter]
      by_cases h1 : 8 * (K * (2 * U * δ)) < g P
      · exact Or.inl (Or.inr ⟨hP, h1⟩)
      · by_cases h2 : 8 * (K * K * δ) < z P
        · exact Or.inr ⟨hP, h2⟩
        · exact Or.inl (Or.inl ⟨hP, not_lt.mp h1, not_lt.mp h2⟩)
    calc #Ps ≤ _ := card_le_card hsub
      _ ≤ _ := (card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)
  have hGcard : (3 : ℝ) / 4 * #Ps ≤ #G := by
    have : (#Ps : ℝ) ≤ #G + #(Ps.filter fun P : ℕ => 8 * (K * (2 * U * δ)) < g P)
        + #(Ps.filter fun P : ℕ => 8 * (K * K * δ) < z P) := by exact_mod_cast hcover
    linarith
  -- each prime of `G` is good
  have hGgood : ∀ P ∈ G, GoodPrime V Sx sx Sy sy T b P := by
    intro P hP
    obtain ⟨-, hgP, hzP⟩ := mem_filter.mp hP
    set V' := V.filter fun v => e P v ≤ 2 * (8 * (2 * U * δ)) with hV'
    have hhalf : #V ≤ 2 * #V' := by
      apply averaging V (e P) (fun v _ => he0 P v) (A := 8 * (2 * U * δ))
      calc ∑ v ∈ V, e P v = g P := rfl
        _ ≤ 8 * (K * (2 * U * δ)) := hgP
        _ = #V * (8 * (2 * U * δ)) := by rw [hK]; ring
    have hbd : (0 : ℝ) ≤ K * δ := by positivity
    have hZ : (#(collisions V (res P)) : ℝ) ≤ 8 * #V * (K * δ) := by
      calc (#(collisions V (res P)) : ℝ) = z P := rfl
        _ ≤ 8 * (K * K * δ) := hzP
        _ = 8 * #V * (K * δ) := by rw [hK]; ring
    have hclasses := classes_lower_bound (filter_subset _ V) hhalf (res P) hbd hZ
    refine ⟨V'.image (res P), ?_, ?_⟩
    · have hle : (2 : ℝ) + 64 * (K * δ) ≤ 2 + 64 * b := by linarith
      exact hclasses.trans (mul_le_mul_of_nonneg_left hle (by positivity))
    · intro ρ hρ
      obtain ⟨v, hv, hvρ⟩ := mem_image.mp hρ
      obtain ⟨hvV, hve⟩ := mem_filter.mp hv
      refine ⟨v, hvV, hvρ, ?_⟩
      have hc1 : #{x ∈ Sx | res P (sx x) = ρ ∧ sx x ≠ v} ≤ hits Sx (fun x => sx x - v) P := by
        apply card_le_card
        intro x hx
        obtain ⟨hxS, hxρ, hxv⟩ := mem_filter.mp hx
        refine mem_filter.mpr ⟨hxS, sub_ne_zero.mpr hxv, dvd_of_res_eq (hxρ.trans hvρ.symm)⟩
      have hc2 : #{y ∈ Sy | res P (sy y) = ρ ∧ sy y ≠ v} ≤ hits Sy (fun y => sy y - v) P := by
        apply card_le_card
        intro y hy
        obtain ⟨hyS, hyρ, hyv⟩ := mem_filter.mp hy
        refine mem_filter.mpr ⟨hyS, sub_ne_zero.mpr hyv, dvd_of_res_eq (hyρ.trans hvρ.symm)⟩
      have hc1' : (#{x ∈ Sx | res P (sx x) = ρ ∧ sx x ≠ v} : ℝ)
          ≤ hits Sx (fun x => sx x - v) P := by exact_mod_cast hc1
      have hc2' : (#{y ∈ Sy | res P (sy y) = ρ ∧ sy y ≠ v} : ℝ)
          ≤ hits Sy (fun y => sy y - v) P := by exact_mod_cast hc2
      have hee : e P v = (hits Sx (fun x => sx x - v) P : ℝ)
          + (hits Sy (fun y => sy y - v) P : ℝ) := rfl
      push_cast
      linarith
  rw [prob_eq, le_div_iff₀ hP0]
  have hsubG : G ⊆ Ps.filter (GoodPrime V Sx sx Sy sy T b) := fun P hP =>
    mem_filter.mpr ⟨(mem_filter.mp hP).1, hGgood P hP⟩
  have : (#G : ℝ) ≤ #(Ps.filter (GoodPrime V Sx sx Sy sy T b)) := by
    exact_mod_cast card_le_card hsubG
  linarith

end Main

/-! ## The filter for the lists of the label scheme -/

section Lists

variable {ι Lab : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq Lab] [Fintype Lab]
  {L : ι → Lab} {ν : Layout Lab} {p : Pin ι} {D y : ι → ℤ}

/-- All symbols of the layout and the pinned value have absolute value at most `A`. -/
structure EntryBound (ν : Layout Lab) (p : Pin ι) (A : ℤ) : Prop where
  nonneg : 0 ≤ A
  val : |p.val| ≤ A
  onS : ∀ l, ∀ v ∈ (ν.iv l).S, |v| ≤ A
  onT : ∀ l, ∀ v ∈ (ν.iv l).T, |v| ≤ A

omit [DecidableEq ι] in
/-- The size bound on the sums over either list. -/
theorem abs_dot_le {A : ℤ} {X : ι → ℤ} (hX : ∀ i, |X i| ≤ A) :
    |dot X y| ≤ A * ∑ i, |y i| := by
  unfold dot
  calc |∑ i, X i * y i| ≤ ∑ i, |X i * y i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, A * |y i| := by
      refine sum_le_sum fun i _ => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hX i) (abs_nonneg _)
    _ = A * ∑ i, |y i| := by rw [mul_sum]

omit [Fintype ι] [DecidableEq ι] [DecidableEq Lab] [Fintype Lab] in
theorem EntryBound.alphaX {A : ℤ} (h : EntryBound ν p A) {X : ι → ℤ} (hX : AlphaX ν L p X) (i : ι) :
    |X i| ≤ A := by
  classical
  by_cases hi : i = p.coord
  · rw [hi, hX.pin]
    exact h.val
  · exact h.onS _ _ (hX.mem i hi)

omit [Fintype ι] [DecidableEq ι] [DecidableEq Lab] [Fintype Lab] in
theorem EntryBound.alphaY {A : ℤ} (h : EntryBound ν p A) {Y : ι → ℤ} (hY : AlphaY ν L p Y) (i : ι) :
    |Y i| ≤ A := by
  classical
  by_cases hi : i = p.coord
  · rw [hi, hY.pin, abs_zero]
    exact h.nonneg
  · exact h.onT _ _ (hY.mem i hi)

/-- The values of the representations. -/
noncomputable def repValues (L : ι → Lab) (ν : Layout Lab) (p : Pin ι) (D y : ι → ℤ) : Finset ℤ :=
  (reps L ν p D).image fun q => dot q.1 y

/-- If the values of the representations are distinct there are `K` of them. Distinctness holds under
minimality (`value_injOn`) and without free coordinates (`value_injOn_of_free_empty`). -/
theorem card_repValues (hD : Good L ν p D)
    (hinj : Set.InjOn (fun q : (ι → ℤ) × (ι → ℤ) => dot q.1 y) (reps L ν p D)) :
    #(repValues L ν p D y) = ν.K := by
  rw [repValues, card_image_of_injOn hinj, card_reps hD]

/-- A prime is good for the lists `𝒳` and `𝒴`. Each residue of `R` has a representation
`(X⋆, Y⋆)` in that residue, of value `v`, for which at most `T/2` elements of `𝒳_ρ` and `𝒴_ρ`
together have an exact sum other than `v`. -/
def GoodPrimeLists (L : ι → Lab) (ν : Layout Lab) (p : Pin ι) (D y : ι → ℤ) (T b : ℝ) (P : ℕ) : Prop :=
  ∃ R : Finset ℤ, (ν.K : ℝ) ≤ #R * (2 + 64 * b) ∧
    ∀ ρ ∈ R, ∃ q ∈ reps L ν p D, res P (dot q.1 y) = ρ ∧ res P (dot q.2 y) = ρ ∧
      ((#{X ∈ listX ν L p | res P (dot X y) = ρ ∧ dot X y ≠ dot q.1 y}
        + #{Y ∈ listY ν L p | res P (dot Y y) = ρ ∧ dot Y y ≠ dot q.1 y} : ℕ) : ℝ) ≤ T / 2

/-- **Lemma 3, for the lists.** Fix a good partition and a solution `D` of `y` whose representations
have distinct values, and let the symbols be bounded by `A`. If `2 A Σ |y_i| ≤ B`, then with
probability at least `3/4` over a uniform element of `Ps`, the prime is good for `𝒳` and `𝒴`. -/
theorem filter_lists (hD : Good L ν p D) (hy : dot D y = 0)
    (hinj : Set.InjOn (fun q : (ι → ℤ) × (ι → ℤ) => dot q.1 y) (reps L ν p D))
    {A : ℤ} (hA : EntryBound ν p A)
    (Ps : Finset ℕ) (hPs : Ps.Nonempty) {B : ℤ} {U δ T b : ℝ} (hit : PrimeHit Ps B δ) (hδ : 0 ≤ δ)
    (hB : 2 * (A * ∑ i, |y i|) ≤ B)
    (hUx : (#(listX ν L p) : ℝ) ≤ U) (hUy : (#(listY ν L p) : ℝ) ≤ U)
    (hT : 64 * U * δ ≤ T) (hb : (ν.K : ℝ) * δ ≤ b) :
    (3 : ℝ) / 4 ≤ prob Ps (GoodPrimeLists L ν p D y T b) := by
  classical
  have hcard := card_repValues hD hinj
  have hbX : ∀ X ∈ listX ν L p, |dot X y| ≤ A * ∑ i, |y i| := fun X hX =>
    abs_dot_le (hA.alphaX (mem_listX.mp hX).toAlphaX)
  have hbY : ∀ Y ∈ listY ν L p, |dot Y y| ≤ A * ∑ i, |y i| := fun Y hY =>
    abs_dot_le (hA.alphaY (mem_listY.mp hY).toAlphaY)
  have hbV : ∀ v ∈ repValues L ν p D y, |v| ≤ A * ∑ i, |y i| := by
    intro v hv
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hv
    exact hbX q.1 (mem_listX.mpr (mem_reps.mp hq).isX)
  have hdiff : ∀ a b : ℤ, |a| ≤ A * ∑ i, |y i| → |b| ≤ A * ∑ i, |y i| → |a - b| ≤ B := by
    intro a b ha hb
    have := abs_sub a b
    linarith
  have h := filter_lemma Ps hPs (repValues L ν p D y) (listX ν L p) (fun X => dot X y) (listY ν L p)
    (fun Y => dot Y y) hit hδ hUx hUy
    (fun q hq => hdiff _ _ (hbV _ (mem_product.mp hq).2) (hbV _ (mem_product.mp hq).1))
    (fun v hv x hx => hdiff _ _ (hbX x hx) (hbV v hv))
    (fun v hv x hx => hdiff _ _ (hbY x hx) (hbV v hv))
    hT (by rw [hcard]; exact hb) (T := T) (b := b)
  refine h.trans ?_
  rw [prob_eq, prob_eq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsub : Ps.filter (GoodPrime (repValues L ν p D y) (listX ν L p) (fun X => dot X y) (listY ν L p)
      (fun Y => dot Y y) T b) ⊆ Ps.filter (GoodPrimeLists L ν p D y T b) := by
    intro P hP
    obtain ⟨hPPs, R, hR, hρ⟩ := mem_filter.mp hP
    refine mem_filter.mpr ⟨hPPs, R, ?_, ?_⟩
    · rwa [hcard] at hR
    · intro ρ hρR
      obtain ⟨v, hv, hvρ, hcount⟩ := hρ ρ hρR
      obtain ⟨q, hq, rfl⟩ := mem_image.mp hv
      refine ⟨q, hq, hvρ, ?_, hcount⟩
      rw [← value_eq hq hy]
      exact hvρ
  exact_mod_cast card_le_card hsub

end Lists

end SubsetBalancing
