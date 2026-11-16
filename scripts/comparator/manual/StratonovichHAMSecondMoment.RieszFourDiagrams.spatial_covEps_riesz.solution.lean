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
/-- For D a pairing of Fin 2: spatial (waveGreen 1) gamma_eps m D h = int ofReal(heatK eps z) * spatial (waveGreen 1) (x -> riesz c alpha (x - z)) m D h dz. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszFourDiagrams.spatial_covEps_riesz {m : ℕ} {D : Fin 2 → Fin 2} (hD : ∀ i, D i ≠ i ∧ D (D i) = i)
    (c α ε : ℝ) (h : Fin 2 → ℝ) :
    spatial (waveGreen 1) (covEps ((volume : Measure (Rd 1)).withDensity (riesz c α)) ε) m D h =
      ∫⁻ z, ENNReal.ofReal (heatK ε z) *
        spatial (waveGreen 1) (fun x => riesz c α (x - z)) m D h := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.RieszFourDiagrams.spatial_covEps_riesz
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszFourDiagrams
