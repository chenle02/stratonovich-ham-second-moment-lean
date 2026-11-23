-- Printed type replaced by the source's statement in its scope (CheckFidelity: the printed type's instance path differs from the claimed type's, e.g. Lp._proof_4 or the PiLp measurable space).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszInstanceOne
set_option autoImplicit false
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal FourierTransform
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure HomogCovariance)
open HigherRieszTwo (riesz)
open RieszPositiveDefinite (gauss mixOne)
/-- For 0 < alpha0 < 1, c > 0, 0 < alpha < 1: exists mu with HomogCovariance 1 alpha alpha0 (volume.withDensity (riesz c alpha)) mu (TeX 5317-5322 with 384-401); exactly RieszInstanceTarget, the item R target. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszInstanceOne.riesz_homogCovariance_one {c α α₀ : ℝ} (hα₀0 : 0 < α₀) (hα₀1 : α₀ < 1) (hc : 0 < c)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ μ : Measure (Rd 1), HomogCovariance 1 α α₀ (volume.withDensity (riesz c α)) μ := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.RieszInstanceOne.riesz_homogCovariance_one)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszInstanceOne
