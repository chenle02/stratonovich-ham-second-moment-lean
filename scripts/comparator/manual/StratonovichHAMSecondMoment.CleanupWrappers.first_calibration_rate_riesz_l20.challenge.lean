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
/-- Given hR: FirstCalibrationRateRieszTarget: c > 0, 0 < alpha < 1, 0 < alpha0 < 1, every source field with Gamma = c|y|^(-alpha) dy: a first-moment lower rate L gives 2L <= 2 C1 < C2, K = Ksp c alpha (TeX 5839-5841). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CleanupWrappers.first_calibration_rate_riesz_l20 (hR : RieszInstanceTarget) :
    FirstCalibrationRateRieszTarget.{u} := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CleanupWrappers
