namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology FourierTransform InnerProductSpace
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure)
open VariationalMean (heatK)
variable {n : ℕ}
/-- RieszProductPD (supplied), ProductParams a theta, c > 0: gamma_a, gamma_b, gamma_v dx are IsCov, the densities locally integrable, with Scaling 3 - alpha, 2, 3 - chi; and alpha < chi < 2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.EndpointLemmas.product_covariances (hPD : RieszProductPD) {a : Fin 3 → ℝ} {θ c : ℝ}
    (hp : ProductParams a θ) (hc : 0 < c) :
    (IsCov (prodRieszMeasure c a) ∧ LocallyIntegrable (prodRieszReal c a) ∧
        Scaling (prodRieszMeasure c a) (3 - ∑ j, a j)) ∧
      (IsCov (prodRieszMeasure c (bVec θ a)) ∧ LocallyIntegrable (prodRieszReal c (bVec θ a)) ∧
        Scaling (prodRieszMeasure c (bVec θ a)) 2) ∧
      (IsCov (prodRieszMeasure c (vVec θ a)) ∧ LocallyIntegrable (prodRieszReal c (vVec θ a)) ∧
        Scaling (prodRieszMeasure c (vVec θ a)) (3 - chi (∑ j, a j) θ)) ∧
      (∑ j, a j < chi (∑ j, a j) θ ∧ chi (∑ j, a j) θ < 2) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.EndpointLemmas.product_covariances
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
