-- Printed type replaced by the source's statement in its scope (the printed one elaborates another instance path or universe order, so CheckFidelity's Expr equality fails).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceIsonormal
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal Matrix
open FiniteWick (CenteredGaussianField)
open SourceInterface (IsonormalTarget)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
omit [IsProbabilityMeasure P] in
/-- For any measure P and f in L^2(P): omega -> exp(i f(omega)) is measurable (canonical representative). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceIsonormal.measurable_cexp_L2 (f : Lp ℝ 2 P) : Measurable fun ω => exp ((f ω : ℂ) * I) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceIsonormal.measurable_cexp_L2)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceIsonormal
