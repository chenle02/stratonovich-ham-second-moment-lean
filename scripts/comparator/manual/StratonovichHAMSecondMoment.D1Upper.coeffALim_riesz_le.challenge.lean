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
/-- For c >= 0, 0 < alpha < 1, alpha0 < 1, t > 0, DiagramLimits (supplied) for Gamma = c|y|^(-alpha) dy and k >= 1: coeffALim 1 Gamma alpha0 k t <= (2 Zc Ksp)^k t^(beta k)/(k! k^(b k)) and <= (2 Zc Ksp)^k t^(beta k)/(k!)^(3-alpha). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.D1Upper.coeffALim_riesz_le {c α α₀ t : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1)
    (ha1 : α₀ < 1) (ht : 0 < t) (hlim : DiagramLimits 1 (volume.withDensity (riesz c α)) α₀ t)
    {k : ℕ} (hk : 1 ≤ k) :
    coeffALim 1 (volume.withDensity (riesz c α)) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! * (k : ℝ) ^ ((2 - α) * k))) ∧
      coeffALim 1 (volume.withDensity (riesz c α)) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! : ℝ) ^ (3 - α)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Upper
