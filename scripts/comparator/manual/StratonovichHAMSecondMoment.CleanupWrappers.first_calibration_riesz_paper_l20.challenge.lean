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
/-- Given hR: FirstCalibrationRieszTarget: c > 0, 0 < alpha < 1, 0 < alpha0 < 1, t > 0, every source field with Gamma = c|y|^(-alpha) dy: the E X_(2k) bounds, E u <= exp(C1 t^kappa), C1 = C2/2^((4-alpha)/(3-alpha)), 2 C1 < C2 (TeX 5830-5842), without hH. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.CleanupWrappers.first_calibration_riesz_paper_l20 (hR : RieszInstanceTarget) :
    FirstCalibrationRieszTarget.{u} := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.CleanupWrappers
