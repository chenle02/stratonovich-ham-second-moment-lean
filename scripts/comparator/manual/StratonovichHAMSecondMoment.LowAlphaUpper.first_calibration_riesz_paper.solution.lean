namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.LowAlphaUpper
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology Set
open scoped ENNReal Nat
open HomogHypothesis (Rd HomogCovariance IsEven)
open WaveGreen (waveGreen)
open DiagramModel
open FiniteWick (pairings mem_pairings)
open D1Spatial (closers spatialPair Ksp)
open LowAlphaConvolution (heatDens gammaEps specV)
open TwoSimplexTime (Zc)
/-- K_* = Ksp, Riesz case: c > 0, 0 < alpha < 1, 0 < alpha0 < 1 (0 < alpha0 unused), t > 0, MixedMoment and FirstMomentSeries supplied for Gamma = c|y|^(-alpha) dy in d = 1: conclusions of first_calibration_paper with K = Ksp c alpha. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.LowAlphaUpper.first_calibration_riesz_paper {c α α₀ : ℝ} (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1)
    (_hα₀0 : 0 < α₀) (hα₀1 : α₀ < 1) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ} (ht : 0 < t)
    (hM : MixedMoment 1 α₀ (volume.withDensity (HigherRieszTwo.riesz c α)) P X u t)
    (hF : FirstMomentSeries P X u) :
    (∀ k : ℕ, 1 ≤ k → ∫ ω, X (2 * k) ω ∂P ≤
      (Zc α₀ * Ksp c α / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
        ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ∧
      (Zc α₀ * Ksp c α / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) /
          ((k ! : ℝ) * (k : ℝ) ^ ((2 - α) * k)) ≤
        (Zc α₀ * Ksp c α / 2 ^ (3 - α)) ^ k * t ^ ((4 - α - α₀) * k) / (k ! : ℝ) ^ (3 - α)) ∧
    ∫ ω, u ω ∂P ≤ Real.exp (C1 α α₀ (Ksp c α) * t ^ kappa α α₀) ∧
    C1 α α₀ (Ksp c α) = C2 α α₀ (Ksp c α) / 2 ^ ((4 - α) / (3 - α)) ∧
    2 * C1 α α₀ (Ksp c α) < C2 α α₀ (Ksp c α) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.LowAlphaUpper.first_calibration_riesz_paper
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.LowAlphaUpper
