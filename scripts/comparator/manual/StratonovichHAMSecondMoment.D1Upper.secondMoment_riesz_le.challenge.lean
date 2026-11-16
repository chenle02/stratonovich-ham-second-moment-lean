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
/-- For c >= 0, 0 < alpha < 1, alpha0 < 1, t > 0 and MixedMoment (supplied) for Gamma = c|y|^(-alpha) dy in d = 1: E u^2 <= exp((3-alpha)(2 Zc Ksp)^(1/(3-alpha)) t^((4-alpha-alpha0)/(3-alpha))). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.D1Upper.secondMoment_riesz_le {c α α₀ t : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1)
    (ha1 : α₀ < 1) (ht : 0 < t) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ} {u : Ω → ℝ} (h : MixedMoment 1 α₀ (volume.withDensity (riesz c α)) P X u t) :
    ∫ ω, u ω ^ 2 ∂P ≤ Real.exp ((3 - α) * (2 * Zc α₀ * Ksp c α) ^ (1 / (3 - α)) *
      t ^ ((4 - α - α₀) / (3 - α))) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Upper
