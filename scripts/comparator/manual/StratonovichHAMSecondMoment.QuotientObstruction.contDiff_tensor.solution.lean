namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.QuotientObstruction
open MeasureTheory Set Real Metric
open scoped ContDiff ENNReal Pointwise FourierTransform
open HomogHypothesis
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `ContDiff ℝ ∞` (`∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`)).
/-- If p, q : R -> R are C^infinity: x -> p(x_0) q(x_1) is C^infinity on R^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.QuotientObstruction.contDiff_tensor {p q : ℝ → ℝ} (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun x : Rd 2 => p (x 0) * q (x 1)) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.QuotientObstruction.contDiff_tensor
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.QuotientObstruction
