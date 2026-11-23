-- Printed type replaced by the source's statement in its scope (the printed one elaborates another instance path or universe order, so CheckFidelity's Expr equality fails).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceIsonormal
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped ENNReal Matrix
open FiniteWick (CenteredGaussianField)
open SourceInterface (IsonormalTarget)
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
/-- For a probability measure P and f in L^2(P): omega -> exp(i f(omega)) is P-integrable (bounded by 1). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceIsonormal.integrable_cexp_L2 (f : Lp ℝ 2 P) : Integrable (fun ω => exp ((f ω : ℂ) * I)) P := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceIsonormal
