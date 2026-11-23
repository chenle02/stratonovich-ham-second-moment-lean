-- Printed type replaced by the source's statement in its scope (CheckFidelity: the printed type's instance path differs from the claimed type's, e.g. Lp._proof_4 or the PiLp measurable space).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszInstanceOne
set_option autoImplicit false
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal FourierTransform
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure HomogCovariance)
open HigherRieszTwo (riesz)
open RieszPositiveDefinite (gauss mixOne)
/-- For c >= 0, 0 < alpha < 1: rieszSpectral c alpha is a spectral measure of Gamma = volume.withDensity (riesz c alpha) on Rd 1 in the convention of H:homog (TeX 384-401): int phi dGamma = int (int phi e^(i xi x) dx) dmu for Schwartz phi. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszInstanceOne.isSpectralMeasure_riesz {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) :
    IsSpectralMeasure ((volume : Measure (Rd 1)).withDensity (riesz c α)) (rieszSpectral c α) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.RieszInstanceOne.isSpectralMeasure_riesz)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszInstanceOne
