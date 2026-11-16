namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszPositiveDefinite
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Filter
open scoped ENNReal NNReal Topology
open HomogHypothesis (Rd IsTempered IsPosDefDistr)
open EndpointLemmas
open EndpointCorollaries
/-- For 0 <= a_j < 1, 1 < sum a_j < 2, 0 < theta < 2 - sum a_j, c > 0: every conclusion of EndpointLemmas.product_endpoints_paper (arithmetic, covariance properties and scalings, comparison, endpoint pair), with RieszProductPD proved. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszPositiveDefinite.product_endpoints_paper_proved {a : Fin 3 → ℝ} {θ c : ℝ}
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
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszPositiveDefinite
