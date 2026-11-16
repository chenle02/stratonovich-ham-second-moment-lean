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
/-- d = 1, H:homog for Gamma = c|y|^(-alpha) dy (unused), c > 0, 0 < alpha < 1, 0 < alpha0 < 1, t >= 0, X 0 = 1, supplied MixedMoment: E X_2 and E X_1^2 are the two displays of E:riesz-two and sum_(m<3) E[X_m X_(2-m)] = E X_1^2 + 2 E X_2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszFourDiagrams.riesz_small_paper' {c α α₀ : ℝ} {μ : Measure (Rd 1)}
    (_hH : HomogHypothesis.HomogCovariance 1 α α₀
      ((volume : Measure (Rd 1)).withDensity (riesz c α)) μ)
    (hc : 0 < c) (hα : 0 < α) (hα1 : α < 1) (hα0 : 0 < α₀) (hα01 : α₀ < 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → ℝ} {u : Ω → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hM : MixedMoment 1 α₀ ((volume : Measure (Rd 1)).withDensity (riesz c α)) P X u t)
    (hX0 : ∀ ω, X 0 ω = 1) :
    ∫ ω, X 2 ω ∂P = c * t ^ (4 - α - α₀) /
        ((1 - α) * (2 - α - α₀) * (3 - α - α₀) * (4 - α - α₀)) ∧
      ∫ ω, X 1 ω ^ 2 ∂P =
        c / ((1 - α) * (2 - α)) * ∫ v in (0 : ℝ)..t, v ^ (-α₀) * rbr t α v ∧
      ∑ m ∈ Finset.range 3, ∫ ω, X m ω * X (2 - m) ω ∂P =
        ∫ ω, X 1 ω ^ 2 ∂P + 2 * ∫ ω, X 2 ω ∂P := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszFourDiagrams
