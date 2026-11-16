namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WhiteModel
open MeasureTheory Set Metric
open scoped ENNReal Pointwise FourierTransform
open HomogHypothesis
-- Statement copied from the source (the printed type writes `l • A` for a set `A`, which needs the source's `open scoped Pointwise`; the round trip fails without it).
/-- For every real c, measurable A in Rd 1 and l > 0: whiteCov c (l • A) = ofReal (l^(1 - 1)) * whiteCov c A, i.e. Gamma(lA) = l^(d - alpha) Gamma(A) with d = alpha = 1. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.WhiteModel.whiteCov_scaling (c : ℝ) (A : Set (Rd 1)) (hA : MeasurableSet A) (l : ℝ) (hl : 0 < l) :
    whiteCov c (l • A) = ENNReal.ofReal (l ^ (((1 : ℕ) : ℝ) - 1)) * whiteCov c A := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.WhiteModel.whiteCov_scaling
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.WhiteModel
