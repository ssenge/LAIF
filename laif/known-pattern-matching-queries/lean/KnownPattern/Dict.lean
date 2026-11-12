import KnownPattern.Basic

/-!
# Occurrences from anchored parts

`occ_of_parts` (Lemma 1 of dictionary matching, converse direction): if the text has period `q` on `[a, c)`, the
pattern `y` has period `q` on `[l, r)`, the copy of `y` at `t` agrees with the text on a window of length at least `q`
inside `[l, r)`, `[t + l, t + r) ⊆ [a, c)`, and the parts `[0, l)` and `[r, m)` agree, then `y` occurs at `t`.
-/

namespace KnownPattern

variable {α : Type*}

/-- **Occurrence from anchored parts.** -/
theorem occ_of_parts {x y : ℕ → α} {t a c l r m q δ L : ℕ} (hq0 : 0 < q)
    (hx : HasPeriod x a c q) (hy : HasPeriod y l r q)
    (hw : ∀ k < L, x (t + (δ + k)) = y (δ + k)) (hlδ : l ≤ δ) (hδr : δ + L ≤ r) (hqL : q ≤ L)
    (ha : a ≤ t + l) (hc : t + r ≤ c)
    (hleft : ∀ k < l, x (t + k) = y k) (hright : ∀ k, r ≤ k → k < m → x (t + k) = y k) :
    ∀ k < m, x (t + k) = y k := by
  -- the run [l, r): shift it to [0, r - l) and use `periodic_occ`
  have hx' : HasPeriod x (t + l) (t + l + (r - l)) q := hx.mono ha (by omega)
  have hy' : HasPeriod (fun j => y (l + j)) 0 (r - l) q := by
    intro k _ h2
    have := hy (l + k) (by omega) (by omega)
    simpa [add_assoc] using this
  have hw' : ∀ k < L, x (t + l + ((δ - l) + k)) = (fun j => y (l + j)) ((δ - l) + k) := by
    intro k hk
    have e := hw k hk
    have h1 : t + l + (δ - l + k) = t + (δ + k) := by omega
    have h2 : l + (δ - l + k) = δ + k := by omega
    simp only [h1, h2]
    exact e
  have run := periodic_occ hq0 hx' hy' hw' hqL (by omega)
  intro k hk
  by_cases h1 : k < l
  · exact hleft k h1
  by_cases h2 : k < r
  · have e := run (k - l) (by omega)
    have h3 : t + l + (k - l) = t + k := by omega
    have h4 : l + (k - l) = k := by omega
    simp only [h3, h4] at e
    exact e
  · exact hright k (by omega) hk

end KnownPattern
