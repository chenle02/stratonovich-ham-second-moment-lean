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
/-- d = 1, H:homog (unused), c > 0, 0 < alpha < 1, 0 < alpha0 < 1, t > 0: for every m + n = 4 three pairings and J = c^2 t^(2 beta) rieszUnit with rieszUnit finite; A_2(t) = c^2 t^(2 beta) sum_m sum_D rieszUnit, finite. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszFourDiagrams.riesz_four_paper {c α α₀ : ℝ} {μ : Measure (Rd 1)}
    (_hH : HomogHypothesis.HomogCovariance 1 α α₀
      ((volume : Measure (Rd 1)).withDensity (riesz c α)) μ)
    (hc : 0 < c) (hα : 0 < α) (hα1 : α < 1) (hα0 : 0 < α₀) (hα01 : α₀ < 1) {t : ℝ}
    (ht : 0 < t) :
    (∀ m n : ℕ, m + n = 4 → (Pi2 m n).card = 3 ∧ ∀ D ∈ Pi2 m n,
      diagram (waveGreen 1) (riesz c α) α₀ m n D t =
        ENNReal.ofReal (c ^ 2 * t ^ (2 * (4 - α - α₀))) * rieszUnit α α₀ m n D ∧
      rieszUnit α α₀ m n D ≠ ⊤) ∧
    coeffA (waveGreen 1) (riesz c α) α₀ 2 t =
        ENNReal.ofReal (c ^ 2 * t ^ (2 * (4 - α - α₀))) *
          ∑ m ∈ Finset.range (2 * 2 + 1), ∑ D ∈ Pi2 m (2 * 2 - m), rieszUnit α α₀ m (2 * 2 - m) D ∧
      coeffA (waveGreen 1) (riesz c α) α₀ 2 t ≠ ⊤ := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.RieszFourDiagrams.riesz_four_paper
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszFourDiagrams
