import Histogram.Basic

/-!
# Weak records

A weak left record of `p` is a position `j ≤ p` whose height is at most every height in `(j, p]`.

* `isRecL_weak`: every left record is a weak left record.
* `weakL_mono`: the heights of weak left records do not increase going away from `p`, so the list of weak left
  records, in order of distance, can be searched by bisection.
* `first_below_weak`: the first position left of `p` with height below `v ≤ h p` is a weak left record, and every
  weak left record between it and `p` has height at least `v`.
-/

namespace Histogram

/-- `j` is a weak left record of `p`. -/
def IsWeakL (h : ℤ → ℝ) (p j : ℤ) : Prop := j ≤ p ∧ ∀ i, j < i → i ≤ p → h j ≤ h i

theorem isRecL_weak {h : ℤ → ℝ} {p j : ℤ} (hj : IsRecL h p j) : IsWeakL h p j :=
  ⟨hj.1, fun i h1 h2 => (hj.2 i h1 h2).le⟩

theorem weakL_mono {h : ℤ → ℝ} {p j j' : ℤ} (hj : IsWeakL h p j) (hj' : IsWeakL h p j') (e : j < j') :
    h j ≤ h j' :=
  hj.2 j' e hj'.1

theorem first_below_weak (h : ℤ → ℝ) {p q : ℤ} {v : ℝ} (hqp : q < p) (hq : h q < v)
    (hrun : ∀ i, q < i → i ≤ p → v ≤ h i) :
    IsWeakL h p q ∧ ∀ j, q < j → IsWeakL h p j → v ≤ h j :=
  ⟨isRecL_weak (first_below_isRecL h hqp hq hrun), fun j hj hw => hrun j hj hw.1⟩

end Histogram
