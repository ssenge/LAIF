import SsspFlow.AggProof
import SsspFlow.NegFinal

/-!
# The Label Hypothesis without the aggregation primitive as a hypothesis

`aggBox` proves `AggBox` in the message model, so the Label Hypothesis of `LabelFinal` holds
without it. The end results without the smoothing as a hypothesis are in `SmoothRun`.
-/

set_option autoImplicit false

namespace SsspFlow.Congest

/-- **The Label Hypothesis** from the realization of metrics in a disk, distance labels of planar
graphs and the names of the faces. -/
theorem labelHypothesis_of_cited {Cr Cl cl : ℕ} (hC : RealizationBox Cr) (hL : DistanceLabelBox Cl cl)
    (hF : FaceIdBox) : LabelHypothesis :=
  labelHypothesis_of_boxes hC hL hF aggBox

end SsspFlow.Congest
