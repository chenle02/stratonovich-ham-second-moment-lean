-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CleanupWrappers
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open LowAlphaConvolution (specV)
open SourceInterface
open HomogeneousEnvelope (BK)
open LowAlphaUpper (C1 C2 Kgen kappa)
open TwoSimplexTime (Zc)
open D1Spatial (Ksp)
open MildInterface
/-- D1UpperRieszTarget, nothing supplied: P:d1-upper, Riesz case, for every source field under the manuscript's hypotheses only, 0 < alpha0 < 1, c > 0, 0 < alpha < 1, t > 0 (TeX 5454-5466, 5319); hR discharged. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CleanupWrappers.d1_upper_paper_closed_l20 : D1UpperRieszTarget.{u} := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CleanupWrappers
