module

import StratonovichHAMSecondMoment.DiagramBridge

set_option autoImplicit false
set_option pp.all true

#check @StratonovichHAMSecondMoment.DiagramBridge.incrOfPos
#print axioms StratonovichHAMSecondMoment.DiagramBridge.incrOfPos
#check @StratonovichHAMSecondMoment.DiagramBridge.pred_eq_some_val
#print axioms StratonovichHAMSecondMoment.DiagramBridge.pred_eq_some_val
#check @StratonovichHAMSecondMoment.DiagramBridge.pos_eq_add_predVal
#print axioms StratonovichHAMSecondMoment.DiagramBridge.pos_eq_add_predVal
#check @StratonovichHAMSecondMoment.DiagramBridge.incrOfPos_pos
#print axioms StratonovichHAMSecondMoment.DiagramBridge.incrOfPos_pos
#check @StratonovichHAMSecondMoment.DiagramBridge.pos_incrOfPos
#print axioms StratonovichHAMSecondMoment.DiagramBridge.pos_incrOfPos
#check @StratonovichHAMSecondMoment.DiagramBridge.measurable_incrOfPos
#print axioms StratonovichHAMSecondMoment.DiagramBridge.measurable_incrOfPos
#check @StratonovichHAMSecondMoment.DiagramBridge.posEquiv
#print axioms StratonovichHAMSecondMoment.DiagramBridge.posEquiv
#check @StratonovichHAMSecondMoment.DiagramBridge.e1
#print axioms StratonovichHAMSecondMoment.DiagramBridge.e1
#check @StratonovichHAMSecondMoment.DiagramBridge.measurePreserving_e1
#print axioms StratonovichHAMSecondMoment.DiagramBridge.measurePreserving_e1
#check @StratonovichHAMSecondMoment.DiagramBridge.e1_sub
#print axioms StratonovichHAMSecondMoment.DiagramBridge.e1_sub
#check @StratonovichHAMSecondMoment.DiagramBridge.e1_zero
#print axioms StratonovichHAMSecondMoment.DiagramBridge.e1_zero
#check @StratonovichHAMSecondMoment.DiagramBridge.eN
#print axioms StratonovichHAMSecondMoment.DiagramBridge.eN
#check @StratonovichHAMSecondMoment.DiagramBridge.measurePreserving_eN
#print axioms StratonovichHAMSecondMoment.DiagramBridge.measurePreserving_eN
#check @StratonovichHAMSecondMoment.DiagramBridge.incrMatrix
#print axioms StratonovichHAMSecondMoment.DiagramBridge.incrMatrix
#check @StratonovichHAMSecondMoment.DiagramBridge.det_incrMatrix
#print axioms StratonovichHAMSecondMoment.DiagramBridge.det_incrMatrix
#check @StratonovichHAMSecondMoment.DiagramBridge.incrVec
#print axioms StratonovichHAMSecondMoment.DiagramBridge.incrVec
#check @StratonovichHAMSecondMoment.DiagramBridge.incrMatrix_mulVec
#print axioms StratonovichHAMSecondMoment.DiagramBridge.incrMatrix_mulVec
#check @StratonovichHAMSecondMoment.DiagramBridge.measurePreserving_incrMatrix
#print axioms StratonovichHAMSecondMoment.DiagramBridge.measurePreserving_incrMatrix
#check @StratonovichHAMSecondMoment.DiagramBridge.incrOfPos_eq_conj
#print axioms StratonovichHAMSecondMoment.DiagramBridge.incrOfPos_eq_conj
#check @StratonovichHAMSecondMoment.DiagramBridge.measurePreserving_incrOfPos
#print axioms StratonovichHAMSecondMoment.DiagramBridge.measurePreserving_incrOfPos
#check @StratonovichHAMSecondMoment.DiagramBridge.pi_waveGreen_one
#print axioms StratonovichHAMSecondMoment.DiagramBridge.pi_waveGreen_one
#check @StratonovichHAMSecondMoment.DiagramBridge.prod_green1
#print axioms StratonovichHAMSecondMoment.DiagramBridge.prod_green1
#check @StratonovichHAMSecondMoment.DiagramBridge.lintegral_pi_waveGreen_one
#print axioms StratonovichHAMSecondMoment.DiagramBridge.lintegral_pi_waveGreen_one
#check @StratonovichHAMSecondMoment.DiagramBridge.spatial_waveGreen_one_eq_spatialPos
#print axioms StratonovichHAMSecondMoment.DiagramBridge.spatial_waveGreen_one_eq_spatialPos
#check @StratonovichHAMSecondMoment.DiagramBridge.diagram_waveGreen_one_eq_diagramPos
#print axioms StratonovichHAMSecondMoment.DiagramBridge.diagram_waveGreen_one_eq_diagramPos
#check @StratonovichHAMSecondMoment.DiagramBridge.spatial_bridge_paper
#print axioms StratonovichHAMSecondMoment.DiagramBridge.spatial_bridge_paper
#check @StratonovichHAMSecondMoment.DiagramBridge.diagram_bridge_paper
#print axioms StratonovichHAMSecondMoment.DiagramBridge.diagram_bridge_paper

namespace StratonovichHAMSecondMoment.Audit.DiagramBridge

open MeasureTheory StratonovichHAMSecondMoment DiagramModel DiagramBridge
open scoped ENNReal

/-- Consumer: in `d = 1` the total-order coefficient `A_k(t)` of the model
(increments form) is the sum of the literal positions-form diagrams of
`E:mixed-diagram`. -/
theorem audit_consumer (γ : HomogHypothesis.Rd 1 → ℝ≥0∞) (α₀ : ℝ) (k : ℕ) (t : ℝ) :
    coeffA (WaveGreen.waveGreen 1) γ α₀ k t =
      ∑ m ∈ Finset.range (2 * k + 1), ∑ D ∈ Pi2 m (2 * k - m),
        diagramPos green1 γ α₀ m (2 * k - m) D t := by
  unfold coeffA
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun D hD => ?_
  exact diagram_bridge_paper γ α₀ m (2 * k - m) D hD t

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.DiagramBridge
