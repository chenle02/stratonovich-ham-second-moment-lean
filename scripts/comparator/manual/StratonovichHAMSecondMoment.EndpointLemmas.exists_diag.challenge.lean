namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology FourierTransform InnerProductSpace
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure)
open VariationalMean (heatK)
variable {n : ℕ}
/-- For an invertible continuous linear T of R^n there are an orthonormal basis b and l i > 0 with |T z|^2 = sum_i l i <b i, z>^2 for all z. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.EndpointLemmas.exists_diag (T : Rd n ≃L[ℝ] Rd n) :
    ∃ (b : OrthonormalBasis (Fin n) ℝ (Rd n)) (l : Fin n → ℝ), (∀ i, 0 < l i) ∧
      ∀ z, ‖T z‖ ^ 2 = ∑ i, l i * (b.repr z i) ^ 2 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
