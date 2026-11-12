import Mathlib

/-!
# Z-free Pauli strings in a coset of a subgroup

A Pauli string on `t` qubits up to phase is a vector in `(F₂²)^t`, here `Fin t → ZMod 2 × ZMod 2`,
and the single-qubit `Z` is `(0, 1)`. A string is Z-free if no coordinate equals `Z`.

* `zfree_count_le`: for a subgroup `H` with `2 ^ D` elements and any `x`, the coset `x + H` contains
  at most `2 ^ D` Z-free strings, and if `t ≤ D`, their number `c` satisfies
  `c * 2 ^ D * 3 ^ t ≤ 3 ^ D * 4 ^ t`, that is `c ≤ 3 ^ (D - t) * 2 ^ (2 t - D)`.
* `zfree_tcount`: if a subgroup `V` with `2 ^ D` elements, `D ≤ n + t`, has a coset with at least
  `4 ^ n` Z-free strings, then `4 ^ n * 2 ^ n ≤ 3 ^ n * 2 ^ t`, so `t ≥ (3 - log₂ 3) n`.
-/

namespace ZFreeCount

abbrev K := ZMod 2 × ZMod 2

/-- The single-qubit Pauli `Z`. -/
def zv : K := (0, 1)

/-- No coordinate equals `Z`. -/
def ZFree {t : ℕ} (v : Fin t → K) : Prop := ∀ i, v i ≠ zv

instance {t : ℕ} : DecidablePred (@ZFree t) := fun v => by unfold ZFree; infer_instance

open Classical in
/-- The number of Z-free strings in the coset `x + H`. -/
noncomputable def cnt {t : ℕ} (H : AddSubgroup (Fin t → K)) (x : Fin t → K) : ℕ :=
  (Finset.univ.filter (fun v => v - x ∈ H ∧ ZFree v)).card

lemma cnt_eq {t : ℕ} (H : AddSubgroup (Fin t → K)) (x : Fin t → K) (T : Finset (Fin t → K))
    (hT : ∀ v, v ∈ T ↔ v - x ∈ H ∧ ZFree v) : cnt H x = T.card := by
  unfold cnt
  congr 1
  ext v
  simp [hT]

/-- A finset described as a coset of a subgroup has the size of the subgroup. -/
lemma coset_card {α : Type*} [AddCommGroup α] [Fintype α] (G : AddSubgroup α) (y : α)
    (T : Finset α) (hT : ∀ v, v ∈ T ↔ v - y ∈ G) : T.card = Nat.card G := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr
    { toFun := fun v => ⟨v.1 - y, (hT _).1 v.2⟩
      invFun := fun g => ⟨g.1 + y, (hT _).2 (by rw [add_sub_cancel_right]; exact g.2)⟩
      left_inv := fun v => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun g => Subtype.ext (add_sub_cancel_right _ _) }

/-- Prepending a zero coordinate, as an additive map. -/
def consZero (t : ℕ) : (Fin t → K) →+ (Fin (t + 1) → K) where
  toFun w := Fin.cons 0 w
  map_zero' := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_add' a b := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma consZero_apply {t : ℕ} (w : Fin t → K) : consZero t w = Fin.cons 0 w := rfl

lemma sub_eq_consZero {t : ℕ} {u u' : Fin (t + 1) → K} (h : u 0 = u' 0) :
    u - u' = consZero t (Fin.tail u - Fin.tail u') := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [consZero_apply, h]
  · simp [consZero_apply, Fin.tail]

lemma zfree_cons {t : ℕ} (v : Fin (t + 1) → K) : ZFree v ↔ v 0 ≠ zv ∧ ZFree (Fin.tail v) := by
  constructor
  · intro h; exact ⟨h 0, fun j => h j.succ⟩
  · rintro ⟨h0, ht⟩ i
    exact Fin.cases h0 (fun j => ht j) i

/-- The fibre of a coset over a value `a` of the first coordinate is in bijection with a coset of
the subgroup of strings with first coordinate zero. -/
lemma fibre_card {t : ℕ} (H : AddSubgroup (Fin (t + 1) → K)) (x : Fin (t + 1) → K) (a : K)
    (v₀ : Fin (t + 1) → K) (hv₀ : v₀ - x ∈ H) (ha : v₀ 0 = a) (R : (Fin t → K) → Prop)
    (S : Finset (Fin (t + 1) → K)) (T : Finset (Fin t → K))
    (hS : ∀ v, v ∈ S ↔ v - x ∈ H ∧ v 0 = a ∧ R (Fin.tail v))
    (hT : ∀ w, w ∈ T ↔ w - Fin.tail v₀ ∈ H.comap (consZero t) ∧ R w) : S.card = T.card := by
  apply Finset.card_nbij' Fin.tail (Fin.cons a)
  · intro v hv
    rw [Finset.mem_coe, hS] at hv
    rw [Finset.mem_coe, hT, AddSubgroup.mem_comap]
    refine ⟨?_, hv.2.2⟩
    rw [← sub_eq_consZero (hv.2.1.trans ha.symm)]
    have := H.sub_mem hv.1 hv₀
    simpa using this
  · intro w hw
    rw [Finset.mem_coe, hT, AddSubgroup.mem_comap] at hw
    rw [Finset.mem_coe, hS]
    refine ⟨?_, by simp, by simpa using hw.2⟩
    have e : (Fin.cons a w : Fin (t + 1) → K) - v₀ = consZero t (w - Fin.tail v₀) := by
      rw [sub_eq_consZero (by simp [ha])]
      simp
    have := H.add_mem hw.1 hv₀
    rw [← e] at this
    simpa using this
  · intro v hv
    rw [Finset.mem_coe, hS] at hv
    rw [← hv.2.1]
    exact Fin.cons_self_tail v
  · intro w _
    exact Fin.tail_cons _ _

/-- The first coordinates of the coset `x + H`, as a coset of the image subgroup. -/
lemma first_mem {t : ℕ} (H : AddSubgroup (Fin (t + 1) → K)) (x v : Fin (t + 1) → K)
    (hv : v - x ∈ H) : v 0 - x 0 ∈ H.map (Pi.evalAddMonoidHom (fun _ => K) 0) :=
  AddSubgroup.mem_map.mpr ⟨v - x, hv, by simp⟩

lemma first_witness {t : ℕ} (H : AddSubgroup (Fin (t + 1) → K)) (x : Fin (t + 1) → K) (a : K)
    (ha : a - x 0 ∈ H.map (Pi.evalAddMonoidHom (fun _ => K) 0)) :
    ∃ v₀ : Fin (t + 1) → K, v₀ - x ∈ H ∧ v₀ 0 = a := by
  obtain ⟨h, hh, hp⟩ := AddSubgroup.mem_map.mp ha
  have hp' : h 0 = a - x 0 := hp
  refine ⟨x + h, by simpa using hh, ?_⟩
  show x 0 + h 0 = a
  rw [hp']
  abel

/-- The size of a subgroup is the size of its image under the first coordinate times the size of
the subgroup of strings with first coordinate zero. -/
lemma card_split {t : ℕ} (H : AddSubgroup (Fin (t + 1) → K)) :
    Nat.card H = Nat.card (H.map (Pi.evalAddMonoidHom (fun _ => K) 0)) *
      Nat.card (H.comap (consZero t)) := by
  classical
  set P := H.map (Pi.evalAddMonoidHom (fun _ => K) 0)
  set S : Finset (Fin (t + 1) → K) := Finset.univ.filter (fun v => v - 0 ∈ H)
  set T1 : Finset K := Finset.univ.filter (fun a => a - (0 : Fin (t + 1) → K) 0 ∈ P)
  have hSc : S.card = Nat.card H := coset_card H 0 S (fun v => by simp [S])
  have hT1 : T1.card = Nat.card P := coset_card P 0 T1 (fun a => by simp [T1])
  have hmaps : Set.MapsTo (fun v : Fin (t + 1) → K => v 0) (S : Set _) (T1 : Set _) := by
    intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, S] at hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, T1]
    exact first_mem H 0 v hv
  rw [← hSc, Finset.card_eq_sum_card_fiberwise hmaps, ← hT1, Finset.card_eq_sum_ones T1,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [one_mul]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, T1] at ha
  obtain ⟨v₀, hv₀, hva⟩ := first_witness H 0 a ha
  rw [fibre_card H 0 a v₀ hv₀ hva (fun _ => True) _
    (Finset.univ.filter (fun w => w - Fin.tail v₀ ∈ H.comap (consZero t)))
    (fun v => by simp [S]) (fun w => by simp)]
  exact coset_card _ (Fin.tail v₀) _ (fun w => by simp)

open Classical in
/-- The fibre bound: the count in a coset is at most the number of admissible first values times
a bound on the counts in the cosets of the subgroup of strings with first coordinate zero. -/
lemma key {t : ℕ} (H : AddSubgroup (Fin (t + 1) → K)) (x : Fin (t + 1) → K) (M L : ℕ)
    (hB : ∀ w₀, cnt (H.comap (consZero t)) w₀ * M ≤ L) :
    cnt H x * M ≤ (Finset.univ.filter (fun a : K =>
      a - x 0 ∈ H.map (Pi.evalAddMonoidHom (fun _ => K) 0) ∧ a ≠ zv)).card * L := by
  classical
  set P := H.map (Pi.evalAddMonoidHom (fun _ => K) 0)
  set S : Finset (Fin (t + 1) → K) := Finset.univ.filter (fun v => v - x ∈ H ∧ ZFree v)
  set T1 : Finset K := Finset.univ.filter (fun a => a - x 0 ∈ P)
  have hS : cnt H x = S.card := cnt_eq H x S (fun v => by simp [S])
  have hmaps : Set.MapsTo (fun v : Fin (t + 1) → K => v 0) (S : Set _) (T1 : Set _) := by
    intro v hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, S] at hv
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, T1]
    exact first_mem H x v hv.1
  have hT1 : (Finset.univ.filter (fun a : K => a - x 0 ∈ P ∧ a ≠ zv)) =
      T1.filter (fun a => a ≠ zv) := by
    ext a; simp [T1]
  rw [hS, Finset.card_eq_sum_card_fiberwise hmaps, hT1, Finset.sum_mul]
  rw [← Finset.sum_filter_of_ne (p := fun a => a ≠ zv)]
  · rw [Finset.card_eq_sum_ones (T1.filter _), Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, T1] at ha
    obtain ⟨v₀, hv₀, hva⟩ := first_witness H x a ha.1
    rw [one_mul, fibre_card H x a v₀ hv₀ hva ZFree _
      (Finset.univ.filter (fun w => w - Fin.tail v₀ ∈ H.comap (consZero t) ∧ ZFree w))
      (fun v => ?_) (fun w => by simp), ← cnt_eq (H.comap (consZero t)) (Fin.tail v₀) _ (fun w => by simp)]
    · exact hB _
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, S, zfree_cons]
      constructor
      · rintro ⟨⟨h1, _, h3⟩, h4⟩
        exact ⟨h1, h4, h3⟩
      · rintro ⟨h1, h4, h3⟩
        exact ⟨⟨h1, by rw [h4]; exact ha.2, h3⟩, h4⟩
  · intro a _ hne heq
    apply hne
    rw [Nat.mul_eq_zero]
    left
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro v hv hva
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, S] at hv
    exact hv.2 0 (hva.trans heq)

open Classical in
lemma first_count_le {t : ℕ} (H : AddSubgroup (Fin (t + 1) → K)) (x : Fin (t + 1) → K) :
    (Finset.univ.filter (fun a : K =>
      a - x 0 ∈ H.map (Pi.evalAddMonoidHom (fun _ => K) 0) ∧ a ≠ zv)).card
        ≤ Nat.card (H.map (Pi.evalAddMonoidHom (fun _ => K) 0)) ∧
    (Finset.univ.filter (fun a : K =>
      a - x 0 ∈ H.map (Pi.evalAddMonoidHom (fun _ => K) 0) ∧ a ≠ zv)).card ≤ 3 := by
  classical
  constructor
  · rw [← coset_card _ (x 0) (Finset.univ.filter (fun a : K =>
      a - x 0 ∈ H.map (Pi.evalAddMonoidHom (fun _ => K) 0))) (fun a => by simp)]
    exact Finset.card_le_card (fun a ha => by simp at ha ⊢; exact ha.1)
  · calc _ ≤ (Finset.univ.filter (fun a : K => a ≠ zv)).card :=
          Finset.card_le_card (fun a ha => by simp at ha ⊢; exact ha.2)
      _ = 3 := by decide

open Classical in
/-- The counting lemma. -/
theorem zfree_count_le (t : ℕ) :
    ∀ (H : AddSubgroup (Fin t → K)) (x : Fin t → K) (D : ℕ), Nat.card H = 2 ^ D →
      cnt H x ≤ 2 ^ D ∧ (t ≤ D → cnt H x * 2 ^ D * 3 ^ t ≤ 3 ^ D * 4 ^ t) := by
  induction t with
  | zero =>
    intro H x D _
    have h1 : cnt H x ≤ 1 := by
      unfold cnt
      exact Finset.card_le_one.mpr (fun a _ b _ => Subsingleton.elim a b)
    have h2 : 2 ^ D ≤ 3 ^ D := Nat.pow_le_pow_left (by norm_num) D
    refine ⟨le_trans h1 Nat.one_le_two_pow, fun _ => ?_⟩
    simp only [pow_zero, mul_one]
    calc cnt H x * 2 ^ D ≤ 1 * 2 ^ D := Nat.mul_le_mul_right _ h1
      _ ≤ 3 ^ D := by rw [one_mul]; exact h2
  | succ t ih =>
    intro H x D hD
    obtain ⟨cP, c3⟩ := first_count_le H x
    have hk := key H x
    set c := (Finset.univ.filter (fun a : K =>
      a - x 0 ∈ H.map (Pi.evalAddMonoidHom (fun _ => K) 0) ∧ a ≠ zv)).card
    set H₀ := H.comap (consZero t)
    set P := H.map (Pi.evalAddMonoidHom (fun _ => K) 0)
    have hsplit : Nat.card H = Nat.card P * Nat.card H₀ := card_split H
    have hK : Nat.card K = 2 ^ 2 := by rw [Nat.card_prod, Nat.card_zmod]; norm_num
    have hP4 : Nat.card P ∣ 2 ^ 2 := hK ▸ AddSubgroup.card_addSubgroup_dvd_card P
    obtain ⟨r, hr2, hPr⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hP4
    have h0dvd : Nat.card H₀ ∣ 2 ^ D := by rw [← hD, hsplit]; exact dvd_mul_left _ _
    obtain ⟨D', -, hD'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h0dvd
    have hDsum : D = D' + r := by
      have : 2 ^ D = 2 ^ (D' + r) := by rw [← hD, hsplit, hD', hPr, pow_add, mul_comm]
      exact Nat.pow_right_injective (le_refl 2) this
    subst hDsum
    have hplain : cnt H x ≤ c * 2 ^ D' := by
      have := hk 1 (2 ^ D') (fun w₀ => by rw [mul_one]; exact (ih H₀ w₀ D' hD').1)
      simpa using this
    have hprod : t ≤ D' → cnt H x * (2 ^ D' * 3 ^ t) ≤ c * (3 ^ D' * 4 ^ t) := fun htD =>
      hk _ _ (fun w₀ => by rw [← mul_assoc]; exact (ih H₀ w₀ D' hD').2 htD)
    rw [hPr] at cP
    refine ⟨?_, fun htD => ?_⟩
    · calc cnt H x ≤ c * 2 ^ D' := hplain
        _ ≤ 2 ^ r * 2 ^ D' := Nat.mul_le_mul_right _ cP
        _ = 2 ^ (D' + r) := by rw [pow_add, mul_comm]
    · rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
      · have h := hprod (by omega)
        have hc : c ≤ 1 := by simpa using cP
        calc cnt H x * 2 ^ (D' + 0) * 3 ^ (t + 1) = 3 * (cnt H x * (2 ^ D' * 3 ^ t)) := by ring
          _ ≤ 3 * (c * (3 ^ D' * 4 ^ t)) := Nat.mul_le_mul_left _ h
          _ ≤ 3 * (1 * (3 ^ D' * 4 ^ t)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc)
          _ ≤ 4 * (3 ^ D' * 4 ^ t) := by rw [one_mul]; exact Nat.mul_le_mul_right _ (by norm_num)
          _ = 3 ^ (D' + 0) * 4 ^ (t + 1) := by ring
      · have h := hprod (by omega)
        have hc : c ≤ 2 := by simpa using cP
        calc cnt H x * 2 ^ (D' + 1) * 3 ^ (t + 1) = 6 * (cnt H x * (2 ^ D' * 3 ^ t)) := by ring
          _ ≤ 6 * (c * (3 ^ D' * 4 ^ t)) := Nat.mul_le_mul_left _ h
          _ ≤ 6 * (2 * (3 ^ D' * 4 ^ t)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc)
          _ = 3 ^ (D' + 1) * 4 ^ (t + 1) := by ring
      · by_cases htD' : t ≤ D'
        · have h := hprod htD'
          calc cnt H x * 2 ^ (D' + 2) * 3 ^ (t + 1)
              = 12 * (cnt H x * (2 ^ D' * 3 ^ t)) := by ring
            _ ≤ 12 * (c * (3 ^ D' * 4 ^ t)) := Nat.mul_le_mul_left _ h
            _ ≤ 12 * (3 * (3 ^ D' * 4 ^ t)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ c3)
            _ = 3 ^ (D' + 2) * 4 ^ (t + 1) := by ring
        · obtain rfl : t = D' + 1 := by omega
          have h' : cnt H x ≤ 3 * 2 ^ D' := le_trans hplain (Nat.mul_le_mul_right _ c3)
          have e : 3 ^ (D' + 2) * 4 ^ (D' + 1 + 1) = 16 * (2 ^ D' * 2 ^ D') * 3 ^ (D' + 2) := by
            rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]; ring
          calc cnt H x * 2 ^ (D' + 2) * 3 ^ (D' + 1 + 1)
              ≤ (3 * 2 ^ D') * 2 ^ (D' + 2) * 3 ^ (D' + 1 + 1) :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h')
            _ = 12 * (2 ^ D' * 2 ^ D') * 3 ^ (D' + 2) := by ring
            _ ≤ 16 * (2 ^ D' * 2 ^ D') * 3 ^ (D' + 2) :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
            _ = 3 ^ (D' + 2) * 4 ^ (D' + 1 + 1) := e.symm

/-- The T-count bound: if a subgroup `V` with `2 ^ D` elements, `D ≤ n + t`, has a coset with at
least `4 ^ n` Z-free strings, then `4 ^ n * 2 ^ n ≤ 3 ^ n * 2 ^ t`. -/
theorem zfree_tcount (n t D : ℕ) (V : AddSubgroup (Fin t → K)) (x : Fin t → K)
    (hV : Nat.card V = 2 ^ D) (hD : D ≤ n + t) (hcov : 4 ^ n ≤ cnt V x) :
    4 ^ n * 2 ^ n ≤ 3 ^ n * 2 ^ t := by
  obtain ⟨hA, hB⟩ := zfree_count_le t V x D hV
  by_cases htD : t ≤ D
  · obtain ⟨e, rfl⟩ : ∃ e, D = t + e := ⟨D - t, by omega⟩
    have h2 : 4 ^ n * 2 ^ (t + e) * 3 ^ t ≤ 3 ^ (t + e) * 4 ^ t :=
      le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcov)) (hB htD)
    have h3 : 4 ^ n * 2 ^ e ≤ 3 ^ e * 2 ^ t := by
      have e1 : 4 ^ n * 2 ^ (t + e) * 3 ^ t = (4 ^ n * 2 ^ e) * (3 ^ t * 2 ^ t) := by ring
      have e2 : 3 ^ (t + e) * 4 ^ t = (3 ^ e * 2 ^ t) * (3 ^ t * 2 ^ t) := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]; ring
      rw [e1, e2] at h2
      exact Nat.le_of_mul_le_mul_right h2 (by positivity)
    obtain ⟨f, rfl⟩ : ∃ f, n = e + f := ⟨n - e, by omega⟩
    calc 4 ^ (e + f) * 2 ^ (e + f) = (4 ^ (e + f) * 2 ^ e) * 2 ^ f := by ring
      _ ≤ (3 ^ e * 2 ^ t) * 2 ^ f := Nat.mul_le_mul_right _ h3
      _ ≤ (3 ^ e * 2 ^ t) * 3 ^ f := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by norm_num) f)
      _ = 3 ^ (e + f) * 2 ^ t := by ring
  · have h4 : 4 ^ n ≤ 2 ^ t :=
      le_trans hcov (le_trans hA (Nat.pow_le_pow_right (by norm_num) (by omega)))
    calc 4 ^ n * 2 ^ n ≤ 2 ^ t * 3 ^ n := Nat.mul_le_mul h4 (Nat.pow_le_pow_left (by norm_num) n)
      _ = 3 ^ n * 2 ^ t := mul_comm _ _

end ZFreeCount
