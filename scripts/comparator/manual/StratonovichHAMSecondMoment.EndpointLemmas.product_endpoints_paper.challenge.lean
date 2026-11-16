namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology FourierTransform InnerProductSpace
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure)
open VariationalMean (heatK)
variable {n : ℕ}
/-- RieszProductPD (supplied), 0 <= a j < 1, 1 < alpha = sum a j < 2, 0 < theta < 2 - alpha, c > 0: the arithmetic of L:product-endpoints, the covariance properties and exponents, the comparison, and EndpointPair theta chi gamma_a gamma_b gamma_v. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.EndpointLemmas.product_endpoints_paper (hPD : RieszProductPD) {a : Fin 3 → ℝ} {θ c : ℝ}
    (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j < 1) (hα1 : 1 < ∑ j, a j) (hα2 : ∑ j, a j < 2)
    (hθ0 : 0 < θ) (hθ : θ < 2 - ∑ j, a j) (hc : 0 < c) :
    ((0 < lam θ a ∧ lam θ a < 1) ∧ ∑ j, bVec θ a j = 1 ∧
      ∑ j, vVec θ a j = chi (∑ j, a j) θ ∧
      (∀ j, a j = θ * bVec θ a j + (1 - θ) * vVec θ a j) ∧
      (∀ j, 0 < a j → (0 < bVec θ a j ∧ bVec θ a j < 1) ∧
        (0 < vVec θ a j ∧ vVec θ a j < 1)) ∧
      (∀ j, a j = 0 → bVec θ a j = 0 ∧ vVec θ a j = 0)) ∧
    ((IsCov (prodRieszMeasure c a) ∧ LocallyIntegrable (prodRieszReal c a) ∧
        Scaling (prodRieszMeasure c a) (3 - ∑ j, a j)) ∧
      (IsCov (prodRieszMeasure c (bVec θ a)) ∧ LocallyIntegrable (prodRieszReal c (bVec θ a)) ∧
        Scaling (prodRieszMeasure c (bVec θ a)) 2) ∧
      (IsCov (prodRieszMeasure c (vVec θ a)) ∧ LocallyIntegrable (prodRieszReal c (vVec θ a)) ∧
        Scaling (prodRieszMeasure c (vVec θ a)) (3 - chi (∑ j, a j) θ)) ∧
      (∑ j, a j < chi (∑ j, a j) θ ∧ chi (∑ j, a j) θ < 2)) ∧
    GaussComparison θ (prodRieszMeasure c a) (prodRieszMeasure c (bVec θ a))
      (prodRieszMeasure c (vVec θ a)) ∧
    EndpointPair θ (chi (∑ j, a j) θ) (prodRieszMeasure c a) (prodRieszMeasure c (bVec θ a))
      (prodRieszMeasure c (vVec θ a)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
