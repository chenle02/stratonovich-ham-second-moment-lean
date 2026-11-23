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
/-- Given hR: RieszSmallTarget: c > 0, 0 < alpha < 1, 0 < alpha0 < 1, t > 0, every source field with Gamma = c|y|^(-alpha) dy: E X_2, E X_1^2 as in E:riesz-two and their total E X_1^2 + 2 E X_2 (TeX 5125-5172, 5129-5142), without hH. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CleanupWrappers.riesz_small_paper_l20 (hR : RieszInstanceTarget) : RieszSmallTarget.{u} := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.CleanupWrappers.riesz_small_paper_l20)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CleanupWrappers
