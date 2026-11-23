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
/-- FirstCalibrationRateWhiteTarget, nothing supplied: c > 0, 0 < alpha0 < 1, every source field with Gamma = c delta_0: a first-moment lower rate L gives 2L <= 2 C1 < C2 with alpha = 1, K = c (TeX 5839-5841, 5320). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CleanupWrappers.first_calibration_rate_white_l20 : FirstCalibrationRateWhiteTarget.{u} := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.CleanupWrappers.first_calibration_rate_white_l20)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CleanupWrappers
