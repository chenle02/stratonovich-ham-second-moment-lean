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
/-- Given hR : RieszInstanceTarget: D1UpperRieszTarget: d = 1, Gamma = c|y|^(-alpha) dy, 0 < alpha0 < 1, c > 0, 0 < alpha < 1, t > 0, every source field: the conclusions of SourceFinal.d1_upper_paper_l19 without its hH (TeX 5454-5466, 5319). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CleanupWrappers.d1_upper_paper_l20 (hR : RieszInstanceTarget) : D1UpperRieszTarget.{u} := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.CleanupWrappers.d1_upper_paper_l20)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CleanupWrappers
