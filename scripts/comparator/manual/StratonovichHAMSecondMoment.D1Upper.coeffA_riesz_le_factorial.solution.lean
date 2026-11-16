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
/-- Same hypotheses as coeffA_riesz_le: coeffA (waveGreen 1) (covEps Gamma eps) alpha0 k t <= (2 Zc Ksp)^k t^((4-alpha-alpha0)k)/(k!)^(3-alpha). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.D1Upper.coeffA_riesz_le_factorial {c α α₀ t ε : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1)
    (ha1 : α₀ < 1) (ht : 0 < t) (hε : 0 < ε) {k : ℕ} (hk : 1 ≤ k) :
    coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
      ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
        (k ! : ℝ) ^ (3 - α)) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.D1Upper.coeffA_riesz_le_factorial
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Upper
