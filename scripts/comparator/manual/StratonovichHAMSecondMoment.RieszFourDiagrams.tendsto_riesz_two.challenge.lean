namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszFourDiagrams
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology Set
open scoped ENNReal
open HomogHypothesis (Rd)
open WaveGreen (waveGreen)
open VariationalMean (heatK)
open HigherRieszTwo (riesz)
open DiagramModel
open DiagramBridge (e1)
open OrderTwoDiagrams
/-- c >= 0, 0 <= alpha < 1, 0 <= alpha0 < 1, t >= 0, m + n = 2, D in Pi2 m n: diagram (waveGreen 1) (covEps Gamma eps) alpha0 m n D t -> diagram (waveGreen 1) (riesz c alpha) alpha0 m n D t as eps -> 0+. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszFourDiagrams.tendsto_riesz_two {c α α₀ t : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    (h0 : 0 ≤ α₀) (h1 : α₀ < 1) (ht : 0 ≤ t) {m n : ℕ} (hmn : m + n = 2)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) :
    Tendsto (fun ε => diagram (waveGreen 1)
        (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) α₀ m n D t) (𝓝[>] 0)
      (𝓝 (diagram (waveGreen 1) (riesz c α) α₀ m n D t)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszFourDiagrams
