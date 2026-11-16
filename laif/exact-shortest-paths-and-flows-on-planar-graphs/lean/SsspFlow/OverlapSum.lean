import SsspFlow.SideCorners

/-!
# The lengths of an overlap through any visited corner

A shortest walk of a live annulus at an index `i` that visits a corner `c` of the side of `κ0(x_a)`
gives, for every index `μ` from `max x_a y_a` to `i`, `λ_μ` as the distance from `κ0(μ)` to `c` plus the
distance from `c` to `κ1(μ)`; the same holds on the side of `κ0(x_b)`. Any visited corner of the side
does, not only the one that a run chooses.

* `CutPath.Live.ov_sum_a`, `CutPath.Live.ov_sum_b`: the two sums.
-/

set_option autoImplicit false

namespace SsspFlow

open FourColor
open scoped ENNReal

namespace RotSystem

universe u

variable {D : Type u} [Fintype D] [DecidableEq D] {R : RotSystem D}

namespace CutPath

variable {C : R.CutPath} {g : D → ℝ≥0∞} {Γ : Finset (D × Bool)} (L : C.Live g Γ)
  (hR : R.Planar) (hC : R.Connected) (hg : ∀ x, g (R.rev x) = g x)

namespace Live

include hR hC hg

/-- **The overlap on the side of `κ0(x_a)`.** -/
theorem ov_sum_a {i μ : ℕ} {q : List (D × Bool)} (hq : L.Shortest i q) {c : D × Bool} (hc : L.CornerA c)
    (hv : L.Visits i q c) (hxμ : L.xa ≤ μ) (hyμ : L.ya ≤ μ) (hμi : μ ≤ i) (hix : i ≤ L.xb)
    (hiy : i ≤ L.yb) :
    (R.double.split Γ).walkDist (g ∘ Prod.fst) ((R.double.split Γ).tail (L.κ0 μ))
        ((R.double.split Γ).tail c) +
      (R.double.split Γ).walkDist (g ∘ Prod.fst) ((R.double.split Γ).tail c)
        ((R.double.split Γ).tail (L.κ1 μ)) = C.lamD g μ := by
  obtain ⟨P₁, P₂, s, hs, e1, e2, rfl, -⟩ := hq.1.split_first
    (fun w => w = (R.double.split Γ).tail c) (hv.imp Eq.symm id)
  subst hs
  rw [(L.faceDrawn hR hC).overlap_a (g ∘ Prod.fst) (fun z => hg z.1) hxμ hyμ hμi hix hiy hc e1 e2
    hq.2.2 hq.2.1]
  exact L.dist μ hxμ hyμ (hμi.trans hix) (hμi.trans hiy)

/-- **The overlap on the side of `κ0(x_b)`.** -/
theorem ov_sum_b {i μ : ℕ} {q : List (D × Bool)} (hq : L.Shortest i q) {c : D × Bool} (hc : L.CornerB c)
    (hv : L.Visits i q c) (hxi : L.xa ≤ i) (hyi : L.ya ≤ i) (hiμ : i ≤ μ) (hμx : μ ≤ L.xb)
    (hμy : μ ≤ L.yb) :
    (R.double.split Γ).walkDist (g ∘ Prod.fst) ((R.double.split Γ).tail (L.κ0 μ))
        ((R.double.split Γ).tail c) +
      (R.double.split Γ).walkDist (g ∘ Prod.fst) ((R.double.split Γ).tail c)
        ((R.double.split Γ).tail (L.κ1 μ)) = C.lamD g μ := by
  obtain ⟨P₁, P₂, s, hs, e1, e2, rfl, -⟩ := hq.1.split_first
    (fun w => w = (R.double.split Γ).tail c) (hv.imp Eq.symm id)
  subst hs
  rw [(L.faceDrawn hR hC).overlap_b (g ∘ Prod.fst) (fun z => hg z.1) hxi hyi hiμ hμx hμy hc e1 e2
    hq.2.2 hq.2.1]
  exact L.dist μ (hxi.trans hiμ) (hyi.trans hiμ) hμx hμy

end Live

end CutPath

end RotSystem

end SsspFlow
