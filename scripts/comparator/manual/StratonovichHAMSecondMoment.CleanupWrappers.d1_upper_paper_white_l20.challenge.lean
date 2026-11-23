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
/-- D1UpperWhiteTarget, nothing supplied: d = 1, Gamma = c delta_0, 0 < alpha0 < 1, c > 0, t > 0, every source field: both inequalities of E:d1-coefficient (coeffA, chaos sums) and E u^2 <= exp(2 (2 Z c)^(1/2) t^((3-alpha0)/2)) (TeX 5454-5466, 5320). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CleanupWrappers.d1_upper_paper_white_l20 : D1UpperWhiteTarget.{u} := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CleanupWrappers
