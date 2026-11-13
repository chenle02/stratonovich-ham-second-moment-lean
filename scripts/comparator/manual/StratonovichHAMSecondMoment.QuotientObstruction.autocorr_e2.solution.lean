namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.QuotientObstruction
open MeasureTheory Set Real Metric
open scoped ContDiff ENNReal Pointwise FourierTransform
open HomogHypothesis
-- Statement copied from the source (the printed type names the instance `WithLp.measurableSpace (2 : ENNReal) ..` explicitly, and its `2 : ENNReal` does not elaborate to the project's instance term).
/-- If f : R^2 -> K is continuous with PlaneDecay f: each y -> f(y+te2) conj f(y) and t -> int f(y+te2) conj f(y) dy are integrable, and int_t int_y f(y+te2) conj f(y) = int_u norm(marg f u)^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.QuotientObstruction.autocorr_e2 {𝕜 : Type*} [RCLike 𝕜] {f : Rd 2 → 𝕜} (hc : Continuous f)
    (hf : PlaneDecay f) :
    (∀ t : ℝ, Integrable (fun y => f (y + t • e2) * (starRingEnd 𝕜) (f y))) ∧
      Integrable (fun t : ℝ => ∫ y, f (y + t • e2) * (starRingEnd 𝕜) (f y)) ∧
      ∫ t : ℝ, ∫ y, f (y + t • e2) * (starRingEnd 𝕜) (f y) =
        ((∫ u, ‖marg f u‖ ^ 2 : ℝ) : 𝕜) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.QuotientObstruction.autocorr_e2
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.QuotientObstruction
