namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Spatial
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology Set
open scoped ENNReal
open HomogHypothesis (Rd)
open WaveGreen (waveGreen coordOne)
open DiagramModel
open FiniteWick (pairings mem_pairings)
open LowAlphaConvolution (heatDens)
open VariationalMean (heatK)
open HigherRieszTwo (riesz smoothCov)
open WhiteModel (whiteCov)
/-- Hypotheses of d1_spatial_riesz, 1 <= k and sum h i <= 2t: spatialPair (waveGreen 1) (covEps (riesz) (eps i)) m D h <= ofReal (Ksp c alpha^k * t^((2-alpha)k) / k^((2-alpha)k)). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.D1Spatial.d1_spatial_riesz_max {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) {N k : ℕ}
    (hk : 1 ≤ k) (hN : N = 2 * k) (m : ℕ) {D : Fin N → Fin N}
    (hD : D ∈ pairings (Finset.univ : Finset (Fin N))) {εs : Fin N → ℝ} (hε : ∀ i, 0 < εs i)
    {h : Fin N → ℝ} (hh : ∀ i, 0 ≤ h i) {t : ℝ} (hsum : ∑ i, h i ≤ 2 * t) :
    spatialPair (waveGreen 1) (fun i => covEps (volume.withDensity (riesz c α)) (εs i)) m D h ≤
      ENNReal.ofReal (Ksp c α ^ k * t ^ ((2 - α) * k) / (k : ℝ) ^ ((2 - α) * k)) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.D1Spatial.d1_spatial_riesz_max
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Spatial
