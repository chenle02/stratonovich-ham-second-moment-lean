namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity
open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open WeakSobolev (IsTestFunction)
open SpatialFourierBound (spatialPair)
open TimeSchur (kern kern_nonneg measurable_kern)
open VariationalDilation (CPos conv mean rawCost)
-- Statement copied from the source (the printed type unfolds `Rd d` to `EuclideanSpace ℝ (Fin d)` (a `WithLp` type) at one occurrence where the declaration keeps `Rd d`).
-- The section variables used, written as binders: {d : ℕ}.
/-- If a < 1, Gamma is locally finite and even, Psi, G continuous compactly supported, h = mean a Gamma Psi: x -> h t x G(t,x)^2 is integrable for t in [0,1], t -> int h t x G(t,x)^2 dx is integrable on (0,1), and its integral is stForm a Gamma Psi G^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SpaceTimePositivity.integral_mean_mul_sq_eq_stForm {d : ℕ} {a : ℝ} (ha1 : a < 1) {Γ : Measure (Rd d)}
    [IsLocallyFiniteMeasure Γ] (hE : IsEven Γ) {Ψ G : ℝ × Rd d → ℝ} (hΨ : Continuous Ψ)
    (hΨs : HasCompactSupport Ψ) (hG : Continuous G) (hGs : HasCompactSupport G) :
    (∀ t ∈ Icc (0 : ℝ) 1, Integrable (fun x => mean a Γ Ψ t x * G (t, x) ^ 2)) ∧
      IntegrableOn (fun t => ∫ x, mean a Γ Ψ t x * G (t, x) ^ 2) (Ioo (0 : ℝ) 1) ∧
      ∫ t in Ioo (0 : ℝ) 1, ∫ x, mean a Γ Ψ t x * G (t, x) ^ 2 =
        stForm a Γ Ψ (fun p => G p ^ 2) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.SpaceTimePositivity.integral_mean_mul_sq_eq_stForm
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity
