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
/-- 0 <= c, 0 < alpha < 1, N = 2k, D a pairing of Fin N, eps i > 0, h i >= 0: spatialPair (waveGreen 1) (covEps (riesz) (eps i)) m D h <= ofReal ((c/(1-alpha))^k * prod_O h i * prod_C h j^(1-alpha)). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.D1Spatial.d1_spatial_riesz {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) {N k : ℕ}
    (hN : N = 2 * k) (m : ℕ) {D : Fin N → Fin N}
    (hD : D ∈ pairings (Finset.univ : Finset (Fin N))) {εs : Fin N → ℝ} (hε : ∀ i, 0 < εs i)
    {h : Fin N → ℝ} (hh : ∀ i, 0 ≤ h i) :
    spatialPair (waveGreen 1) (fun i => covEps (volume.withDensity (riesz c α)) (εs i)) m D h ≤
      ENNReal.ofReal ((c / (1 - α)) ^ k * (∏ i ∈ openers D, h i) *
        ∏ j ∈ closers D, h j ^ (1 - α)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Spatial
