-- Printed type replaced by the source's statement in its scope (the printed one elaborates another instance path for the measurable space of `Rd 1`, so CheckFidelity's Expr equality fails).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimitsHomog
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
open HomogHypothesis (Rd HomogCovariance)
open HigherRieszTwo (riesz)
open WaveGreen (coordOne)
/-- For all c, alpha: the measure c|y|^(-alpha) dy on R is invariant under x -> -x. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszDiagramLimitsHomog.withDensity_rieszR_even (c α : ℝ) :
    (volume.withDensity (rieszR c α)).map (fun x : ℝ => -x) = volume.withDensity (rieszR c α) := by
  apply _root_.StratonovichHAMSecondMoment.RieszDiagramLimitsHomog.withDensity_rieszR_even <;> assumption
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimitsHomog
