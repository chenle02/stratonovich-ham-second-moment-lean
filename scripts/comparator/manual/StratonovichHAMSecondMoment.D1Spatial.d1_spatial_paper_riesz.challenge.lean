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
/-- 0 < alpha0 < 1 (unused), 0 < c, 0 < alpha < 1, 1 <= k, m + n = 2k, D in Pi2 m n, eps i > 0, h i > 0: E:d1-spatial-product and, for every t with sum h i <= 2t, E:d1-spatial-max (Riesz case). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.D1Spatial.d1_spatial_paper_riesz {c α α₀ : ℝ} (_hα₀0 : 0 < α₀) (_hα₀1 : α₀ < 1) (hc : 0 < c)
    (hα0 : 0 < α) (hα1 : α < 1) {m n k : ℕ} (hk : 1 ≤ k) (hmn : m + n = 2 * k)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {εs : Fin (m + n) → ℝ}
    (hε : ∀ i, 0 < εs i) {h : Fin (m + n) → ℝ} (hh : ∀ i, 0 < h i) :
    spatialPair (waveGreen 1) (fun i => covEps (volume.withDensity (riesz c α)) (εs i)) m D h ≤
        ENNReal.ofReal ((c / (1 - α)) ^ k * (∏ i ∈ openers D, h i) *
          ∏ j ∈ closers D, h j ^ (1 - α)) ∧
      ∀ t : ℝ, ∑ i, h i ≤ 2 * t →
        spatialPair (waveGreen 1) (fun i => covEps (volume.withDensity (riesz c α)) (εs i))
            m D h ≤
          ENNReal.ofReal (Ksp c α ^ k * t ^ ((2 - α) * k) / (k : ℝ) ^ ((2 - α) * k)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.D1Spatial
