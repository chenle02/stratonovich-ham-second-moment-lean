-- Printed type replaced by the source's statement in its scope (the printed type failed lean-pkg's round-trip check: the universe of the .{u} targets is dropped or the printed instance path differs).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszInstanceOne
set_option autoImplicit false
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal FourierTransform
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure HomogCovariance)
open HigherRieszTwo (riesz)
open RieszPositiveDefinite (gauss mixOne)
/-- For all c, alpha: the lintegral of spectralDensity c alpha * wt equals the mixR c alpha integral of the lintegral of ofReal (gaussK s xi) * wt xi (Tonelli). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszInstanceOne.lintegral_spectralDensity_wt (c α : ℝ) :
    ∫⁻ ξ, spectralDensity c α ξ * wt ξ =
      ∫⁻ s, (∫⁻ ξ : Rd 1, ENNReal.ofReal (gaussK s ξ) * wt ξ) ∂mixR c α := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.RieszInstanceOne.lintegral_spectralDensity_wt)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszInstanceOne
