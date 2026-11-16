namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Upper
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology Set
open scoped ENNReal Nat
open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open DiagramModel
open D1Spatial (Ksp)
open TwoSimplexTime (Zc)
open FiniteWick (pairings mem_pairings)
open HigherRieszTwo (riesz)
open WhiteModel (whiteCov)
/-- Riesz case of E:d1-covariances: 0 < alpha0 < 1 (0 < alpha0 unused), c > 0 (used as c >= 0), 0 < alpha < 1, t > 0, MixedMoment supplied: the width-eps coefficient bounds, E:d1-coefficient for sum_m E[X_m X_(2k-m)], and E u^2 <= exp(C_dir t^kappa). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.D1Upper.d1_upper_paper_riesz {c α α₀ t : ℝ} (_hα₀0 : 0 < α₀) (hα₀1 : α₀ < 1) (hc : 0 < c)
    (hα0 : 0 < α) (hα1 : α < 1) (ht : 0 < t) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ}
    (h : MixedMoment 1 α₀ (volume.withDensity (riesz c α)) P X u t) :
    (∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 1 ≤ k →
      coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! * (k : ℝ) ^ ((2 - α) * k))) ∧
      coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! : ℝ) ^ (3 - α))) ∧
    (∀ k : ℕ, 1 ≤ k →
      ∑ m ∈ Finset.range (2 * k + 1), ∫ ω, X m ω * X (2 * k - m) ω ∂P ≤
        (2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! * (k : ℝ) ^ ((2 - α) * k)) ∧
      (2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) / (k ! * (k : ℝ) ^ ((2 - α) * k)) ≤
        (2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) / (k ! : ℝ) ^ (3 - α)) ∧
    ∫ ω, u ω ^ 2 ∂P ≤ Real.exp ((3 - α) * (2 * Zc α₀ * Ksp c α) ^ (1 / (3 - α)) *
      t ^ ((4 - α - α₀) / (3 - α))) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Upper
