import SsspFlow.AggProof
import SsspFlow.NegFinal

/-!
# The end results without the aggregation primitive as a hypothesis

`aggBox` proves `AggBox` in the message model, so the end results of `LabelFinal` and `NegFinal`
hold without it.
-/

set_option autoImplicit false

namespace SsspFlow.Congest

/-- **The Label Hypothesis** from the realization of metrics in a disk, distance labels of planar
graphs and the names of the faces. -/
theorem labelHypothesis_of_cited {Cr Cl cl : ℕ} (hC : RealizationBox Cr) (hL : DistanceLabelBox Cl cl)
    (hF : FaceIdBox) : LabelHypothesis :=
  labelHypothesis_of_boxes hC hL hF aggBox

/-- **Exact shortest paths** in `Õ(D)` rounds, from the same results and the smoothing. -/
theorem exactSssp_of_cited {Cr Cl cl : ℕ} (hC : RealizationBox Cr) (hL : DistanceLabelBox Cl cl)
    (hF : FaceIdBox) (hS : SmoothingBox) : ExactSsspBound :=
  exactSssp_of_boxes hC hL hF aggBox hS

/-- **Negative weights and maximum flow** with the factor `(log n)^c`, from the same results and a
reduction with this factor. -/
theorem negFlow_polylog_of_cited (c : ℕ) {Cr Cl cl : ℕ} (hC : RealizationBox Cr)
    (hL : DistanceLabelBox Cl cl) (hF : FaceIdBox) (hS : SmoothingBox)
    (hR : NegReduction (tauPolylog c)) :
    NegSsspBound (tauPolylog c) ∧ MaxFlowBound (tauPolylog c) :=
  negFlow_polylog_of_boxes c hC hL hF aggBox hS hR

/-- **Negative weights and maximum flow** with the factor `(log n)^(C √log n)`, from the same
results and a reduction with this factor. -/
theorem negFlow_subpoly_of_cited (C : ℕ) {Cr Cl cl : ℕ} (hC : RealizationBox Cr)
    (hL : DistanceLabelBox Cl cl) (hF : FaceIdBox) (hS : SmoothingBox)
    (hR : NegReduction (tauSubpoly C)) :
    NegSsspBound (tauSubpoly C) ∧ MaxFlowBound (tauSubpoly (12 * C)) :=
  negFlow_subpoly_of_boxes C hC hL hF aggBox hS hR

/-- **Negative weights and maximum flow** with the factor `logᶜ n`, from the realization of
metrics, distance labels, the names of the faces, the smoothing and the decomposition. -/
theorem negFlow_of_cited {Cr Cl cl : ℕ} (hC : RealizationBox Cr) (hL : DistanceLabelBox Cl cl)
    (hF : FaceIdBox) (hS : SmoothingBox) (hD : LDDBox) :
    ∃ c, NegSsspBound (tauPolylog c) ∧ MaxFlowBound (tauPolylog c) :=
  negFlow_of_ldd hC hL hF aggBox hS hD

end SsspFlow.Congest
