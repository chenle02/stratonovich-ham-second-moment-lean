-- Printed type replaced by the source's statement in its scope (the printed one elaborates another instance path for the measurable space of `Rd 1`, so CheckFidelity's Expr equality fails).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimitsHomog
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal Pointwise
open HomogHypothesis (Rd HomogCovariance)
open HigherRieszTwo (riesz)
open WaveGreen (coordOne)
/-- For all c, alpha: the pushforward by coordOne of c|y|^(-alpha) dy on R^1 is c|y|^(-alpha) dy on R. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszDiagramLimitsHomog.map_withDensity_riesz (c α : ℝ) :
    (volume.withDensity (riesz c α) : Measure (Rd 1)).map coordOne =
      volume.withDensity (rieszR c α) := by
  apply _root_.StratonovichHAMSecondMoment.RieszDiagramLimitsHomog.map_withDensity_riesz <;> assumption
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimitsHomog
