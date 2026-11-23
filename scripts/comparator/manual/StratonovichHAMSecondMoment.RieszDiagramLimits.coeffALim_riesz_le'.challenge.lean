-- Printed type replaced by the source's statement in its scope (the printed one elaborates another instance path for the measurable space of `Rd 1`, so CheckFidelity's Expr equality fails).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimits
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal Nat
open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open HigherRieszTwo (riesz)
open DiagramModel
open TwoSimplexTime (Zc)
open D1Spatial (Ksp)
/-- E:d1-coefficient for the limit A_k(t), Riesz case, nothing supplied: c >= 0, 0 < alpha < 1, 0 <= alpha0 < 1, t > 0, k >= 1: coeffALim <= (2 Z K_sp)^k t^(beta k)/(k! k^(bk)) and <= (2 Z K_sp)^k t^(beta k)/(k!)^q, beta = 4-alpha-alpha0, b = 2-alpha, q = 3-alpha. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszDiagramLimits.coeffALim_riesz_le' {c α α₀ t : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1)
    (h0 : 0 ≤ α₀) (ha1 : α₀ < 1) (ht : 0 < t) {k : ℕ} (hk : 1 ≤ k) :
    coeffALim 1 (volume.withDensity (riesz c α)) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k *
          t ^ ((4 - α - α₀) * k) / (k ! * (k : ℝ) ^ ((2 - α) * k))) ∧
      coeffALim 1 (volume.withDensity (riesz c α)) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k *
          t ^ ((4 - α - α₀) * k) / (k ! : ℝ) ^ (3 - α)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimits
