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
/-- 0 <= c, 0 < alpha < 1, m + n = 2k, D in Pi2 m n, 0 < eps, h i >= 0: spatialPos green1 (covEps (riesz) eps) m D h <= ofReal ((c/(1-alpha))^k * prod_O h i * prod_C h j^(1-alpha)). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.D1Spatial.spatialPos_riesz_le {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) {m n k : ℕ}
    (hmn : m + n = 2 * k) {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε : ℝ}
    (hε : 0 < ε) {h : Fin (m + n) → ℝ} (hh : ∀ i, 0 ≤ h i) :
    spatialPos green1 (covEps (volume.withDensity (riesz c α)) ε) m D h ≤
      ENNReal.ofReal ((c / (1 - α)) ^ k * (∏ i ∈ openers D, h i) *
        ∏ j ∈ closers D, h j ^ (1 - α)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Spatial
