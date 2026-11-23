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
/-- P:d1-upper, Riesz case, coefficient displays with nothing supplied (TeX 5454-5466, Step 3 5532-5538): 0 < alpha0 < 1, c > 0, 0 < alpha < 1, t > 0: both E:d1-coefficient bounds at every eps > 0 and for coeffALim. E:d1-upper not included. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszDiagramLimits.d1_upper_paper_riesz' {c α α₀ t : ℝ} (_hα₀0 : 0 < α₀) (hα₀1 : α₀ < 1) (hc : 0 < c)
    (hα0 : 0 < α) (hα1 : α < 1) (ht : 0 < t) :
    (∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 1 ≤ k →
      coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! * (k : ℝ) ^ ((2 - α) * k))) ∧
      coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) / (k ! : ℝ) ^ (3 - α))) ∧
    (∀ k : ℕ, 1 ≤ k →
      coeffALim 1 (volume.withDensity (riesz c α)) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! * (k : ℝ) ^ ((2 - α) * k))) ∧
      coeffALim 1 (volume.withDensity (riesz c α)) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! : ℝ) ^ (3 - α))) := by
  apply _root_.StratonovichHAMSecondMoment.RieszDiagramLimits.d1_upper_paper_riesz' <;> assumption
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszDiagramLimits
