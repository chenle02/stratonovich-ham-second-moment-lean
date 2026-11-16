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
/-- c >= 0, 0 <= alpha < 1, D a pairing of Fin 2, h 0, h 1 >= 0: the cross spatial parts with gamma_eps converge to the density one and are <= ofReal(h 0) ofReal(c (2 h 1)^(1-alpha)/(1-alpha)). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszFourDiagrams.spatial_riesz_cross_lim {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα : α < 1)
    {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i) {h : Fin 2 → ℝ} (h0 : 0 ≤ h 0)
    (h1 : 0 ≤ h 1) :
    Tendsto (fun ε => spatial (waveGreen 1)
        (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) 1 D h) (𝓝[>] 0)
        (𝓝 (spatial (waveGreen 1) (riesz c α) 1 D h)) ∧
      ∀ ε, 0 < ε → spatial (waveGreen 1)
        (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) 1 D h ≤
          ENNReal.ofReal (h 0) * ENNReal.ofReal (c * (2 * h 1) ^ (1 - α) / (1 - α)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszFourDiagrams
