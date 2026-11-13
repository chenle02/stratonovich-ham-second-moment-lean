namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.QuotientObstruction
open MeasureTheory Set Real Metric
open scoped ContDiff ENNReal Pointwise FourierTransform
open HomogHypothesis
-- Statement copied from the source (the printed type names the instance `WithLp.measurableSpace (2 : ENNReal) ..` explicitly, and its `2 : ENNReal` does not elaborate to the project's instance term).
/-- If g : R^2 -> R is continuous with compact support: x -> g(x) g(x-z) is integrable for every z, z -> int g(x) g(x-z) dx is Gamma0-integrable, and spatialCov Gamma0 g g = margV g. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.QuotientObstruction.spatialCov_Gamma0 {g : Rd 2 → ℝ} (hc : Continuous g) (hs : HasCompactSupport g) :
    (∀ z, Integrable (fun x => g x * g (x - z))) ∧
      Integrable (fun z => ∫ x, g x * g (x - z)) Gamma0 ∧
      spatialCov Gamma0 g g = margV g := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.QuotientObstruction.spatialCov_Gamma0
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.QuotientObstruction
