-- Printed type replaced by the source's statement in its scope (CheckFidelity: the printed type's instance path differs from the claimed type's, e.g. Lp._proof_4 or the PiLp measurable space).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszInstanceOne
set_option autoImplicit false
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal FourierTransform
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure HomogCovariance)
open HigherRieszTwo (riesz)
open RieszPositiveDefinite (gauss mixOne)
/-- For c >= 0, e > 0 and Gamma = volume.withDensity (riesz c e) tempered (ht): Gamma is positive definite on Rd 1 (IsPosDefDistr), by posdef_of_mixture with the identity isometry; the field Gamma_posdef of H:homog. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszInstanceOne.riesz_posdef_one {c e : ℝ} (hc : 0 ≤ c) (he0 : 0 < e)
    (ht : IsTempered ((volume : Measure (Rd 1)).withDensity (riesz c e))) :
    IsPosDefDistr ((volume : Measure (Rd 1)).withDensity (riesz c e)) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.RieszInstanceOne.riesz_posdef_one)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszInstanceOne
