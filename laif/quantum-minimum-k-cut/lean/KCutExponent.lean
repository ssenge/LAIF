import Mathlib

/-!
# Level costs and the padding identity for quantum minimum k-cut

Level `ℓ` of the recursion contracts a graph on `x = n_ℓ` vertices to `y = n_{ℓ+1}` vertices at gate cost
`x²` (up to polylogarithmic factors), and amplitude amplification repeats it `(n / y)^(k/2)` times in total.

* `schedule_hyp`: if `y ≥ x^(4/k)`, then `x² ≤ y^(k/2)`.
* `level_cost_le`: if `x² ≤ y^(k/2)`, then `(n / y)^(k/2) · x² ≤ n^(k/2)`, so every level costs at most `n^(k/2)`.
* `level_cost_eq`, `level_cost_can_fail`: the bound is attained when `x² = y^(k/2)`, and it fails for
  `k = 4`, `n = x = 2`, `y = 1`, where the hypothesis fails.
* `small_k_exponent`: for `0 ≤ k ≤ 4`, `a ≤ 1` and `ε ≥ 0`, the exponent `k/2 + a(2 - k/2 + kε/2)` of a level
  with `n_ℓ = n^a` and `n_{ℓ+1} = n_ℓ^(1-ε)` is at most `2 + kε/2`.
* `cost`: the weight of the pairs `(u, v)` that a map `f` into `Fin k` separates, counted as ordered pairs.
* `pad_ge`, `pad_le`: after adding `k - 2` vertices of weight zero, every partition into `k` nonempty parts costs
  at least some partition of the old vertices into `2` nonempty parts, and every such `2`-partition extends to a
  `k`-partition of the same cost. So the minimum `k`-cut of the padded graph is the minimum cut.
* `cost_example`: on two vertices joined by an edge of weight one, the identity map costs `2`.
-/

namespace KCutExponent

open Real

theorem schedule_hyp {x y k : ℝ} (hx : 0 ≤ x) (hk : 0 < k) (hxy : x ^ (4 / k) ≤ y) :
    x ^ (2 : ℝ) ≤ y ^ (k / 2) := by
  have h : (x ^ (4 / k)) ^ (k / 2) = x ^ (2 : ℝ) := by
    rw [← rpow_mul hx]
    congr 1
    field_simp
    ring
  rw [← h]
  exact rpow_le_rpow (rpow_nonneg hx _) hxy (by positivity)

theorem level_cost_le {n x y k : ℝ} (hn : 0 ≤ n) (hy : 0 < y)
    (hxy : x ^ (2 : ℝ) ≤ y ^ (k / 2)) :
    (n / y) ^ (k / 2) * x ^ (2 : ℝ) ≤ n ^ (k / 2) := by
  rw [div_rpow hn hy.le]
  have hyk : 0 < y ^ (k / 2) := rpow_pos_of_pos hy _
  rw [div_mul_eq_mul_div, div_le_iff₀ hyk]
  exact mul_le_mul_of_nonneg_left hxy (rpow_nonneg hn _)

theorem level_cost_eq {n x y k : ℝ} (hn : 0 ≤ n) (hy : 0 < y)
    (hxy : x ^ (2 : ℝ) = y ^ (k / 2)) :
    (n / y) ^ (k / 2) * x ^ (2 : ℝ) = n ^ (k / 2) := by
  rw [div_rpow hn hy.le, hxy]
  have hyk : 0 < y ^ (k / 2) := rpow_pos_of_pos hy _
  field_simp

theorem level_cost_can_fail :
    ¬ ((2 : ℝ) ^ (2 : ℝ) ≤ (1 : ℝ) ^ ((4 : ℝ) / 2)) ∧
      (2 : ℝ) ^ ((4 : ℝ) / 2) < ((2 : ℝ) / 1) ^ ((4 : ℝ) / 2) * (2 : ℝ) ^ (2 : ℝ) := by
  rw [show (4 : ℝ) / 2 = 2 by norm_num, rpow_two, rpow_two, rpow_two]
  constructor <;> norm_num

theorem small_k_exponent {k a ε : ℝ} (hk : k ≤ 4) (hk0 : 0 ≤ k) (ha1 : a ≤ 1)
    (hε : 0 ≤ ε) :
    k / 2 + a * (2 - k / 2 + k * ε / 2) ≤ 2 + k * ε / 2 := by
  have h1 : 0 ≤ k * ε := mul_nonneg hk0 hε
  have h2 : 0 ≤ (1 - a) * (2 - k / 2 + k * ε / 2) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The weight of the ordered pairs that `f` separates. -/
def cost {α : Type*} [Fintype α] (w : α → α → ℕ) {k : ℕ} (f : α → Fin k) : ℕ :=
  ∑ u, ∑ v, if f u ≠ f v then w u v else 0

/-- The weights after adding `m` vertices of weight zero. -/
def wPad {V : Type*} (w : V → V → ℕ) (m : ℕ) : V ⊕ Fin m → V ⊕ Fin m → ℕ
  | Sum.inl u, Sum.inl v => w u v
  | _, _ => 0

variable {V : Type*} [Fintype V]

theorem cost_pad (w : V → V → ℕ) {m k : ℕ} (f : V ⊕ Fin m → Fin k) :
    cost (wPad w m) f = ∑ u, ∑ v, if f (Sum.inl u) ≠ f (Sum.inl v) then w u v else 0 := by
  simp [cost, Fintype.sum_sum_type, wPad]

theorem pad_ge (w : V → V → ℕ) {k : ℕ} (hk : 2 ≤ k) (f : V ⊕ Fin (k - 2) → Fin k)
    (hf : Function.Surjective f) :
    ∃ g : V → Fin 2, Function.Surjective g ∧ cost w g ≤ cost (wPad w (k - 2)) f := by
  have hsplit : ∃ u₀ u₁ : V, f (Sum.inl u₀) ≠ f (Sum.inl u₁) := by
    by_contra hc
    simp only [not_exists, ne_eq, not_not] at hc
    have hA : (Finset.univ.image (fun u : V => f (Sum.inl u))).card ≤ 1 :=
      Finset.card_le_one.2 (by
        intro a ha b hb
        obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 ha
        obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hb
        exact hc u v)
    have hB : (Finset.univ.image (fun j : Fin (k - 2) => f (Sum.inr j))).card ≤ k - 2 := by
      simpa using (Finset.card_image_le (s := (Finset.univ : Finset (Fin (k - 2))))
        (f := fun j : Fin (k - 2) => f (Sum.inr j)))
    have hsub : (Finset.univ : Finset (Fin k)) ⊆
        Finset.univ.image (fun u : V => f (Sum.inl u)) ∪
          Finset.univ.image (fun j : Fin (k - 2) => f (Sum.inr j)) := by
      intro i _
      obtain ⟨x, rfl⟩ := hf i
      rcases x with u | j
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ u))
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    simp only [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  obtain ⟨u₀, u₁, h01⟩ := hsplit
  refine ⟨fun v => if f (Sum.inl v) = f (Sum.inl u₀) then 0 else 1, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨u₀, by simp⟩
    · exact ⟨u₁, by simp [Ne.symm h01]⟩
  · rw [cost_pad, cost]
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    by_cases h : f (Sum.inl u) = f (Sum.inl v)
    · simp [h]
    · split_ifs <;> omega

theorem pad_le (w : V → V → ℕ) {k : ℕ} (hk : 2 ≤ k) (g : V → Fin 2) (hg : Function.Surjective g) :
    ∃ f : V ⊕ Fin (k - 2) → Fin k, Function.Surjective f ∧ cost (wPad w (k - 2)) f = cost w g := by
  let f : V ⊕ Fin (k - 2) → Fin k
    | Sum.inl v => ⟨(g v).val, by omega⟩
    | Sum.inr j => ⟨j.val + 2, by omega⟩
  refine ⟨f, ?_, ?_⟩
  · intro i
    by_cases hi : i.val < 2
    · obtain ⟨v, hv⟩ := hg ⟨i.val, hi⟩
      exact ⟨Sum.inl v, Fin.ext (by simp [f, hv])⟩
    · exact ⟨Sum.inr ⟨i.val - 2, by omega⟩, Fin.ext (by simp [f]; omega)⟩
  · rw [cost_pad, cost]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    have : (f (Sum.inl u) ≠ f (Sum.inl v)) ↔ (g u ≠ g v) := by
      simp only [f, ne_eq, Fin.mk.injEq]
      exact not_congr Fin.val_inj
    simp only [this]

theorem cost_example :
    cost (fun u v : Fin 2 => if u ≠ v then 1 else 0) (id : Fin 2 → Fin 2) = 2 := by
  decide

end KCutExponent
