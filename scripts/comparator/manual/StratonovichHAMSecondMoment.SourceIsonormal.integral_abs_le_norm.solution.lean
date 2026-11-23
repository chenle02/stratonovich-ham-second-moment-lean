-- Printed type replaced by the source's statement in its scope (the printed one elaborates another instance path or universe order, so CheckFidelity's Expr equality fails).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceIsonormal
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal Matrix
open FiniteWick (CenteredGaussianField)
open SourceInterface (IsonormalTarget)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
/-- For a probability measure P and f in L^2(P): int abs(f) dP <= the L^2 norm of f (the L^1 norm is at most the L^2 norm). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceIsonormal.integral_abs_le_norm (f : Lp ℝ 2 P) : ∫ ω, |f ω| ∂P ≤ ‖f‖ := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceIsonormal.integral_abs_le_norm)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceIsonormal
