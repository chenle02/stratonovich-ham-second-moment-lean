-- Printed type replaced by the source's statement in its scope (the printed type failed lean-pkg's round-trip check: the universe of the .{u} targets is dropped or the printed instance path differs).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszInstanceOne
set_option autoImplicit false
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal FourierTransform
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure HomogCovariance)
open HigherRieszTwo (riesz)
open RieszPositiveDefinite (gauss mixOne)
/-- For 0 < alpha < 1 (any c): the mixture integral over mixR c alpha of the lintegral of ofReal (gaussK s xi) * wt xi is finite (split at s = 1; alpha < 1 used at infinity). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszInstanceOne.lintegral_mix_wt_lt_top {c α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∫⁻ s, (∫⁻ ξ : Rd 1, ENNReal.ofReal (gaussK s ξ) * wt ξ) ∂mixR c α < ∞ := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszInstanceOne
