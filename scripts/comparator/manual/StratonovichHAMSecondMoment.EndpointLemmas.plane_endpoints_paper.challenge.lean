namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal Pointwise Topology FourierTransform InnerProductSpace
open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure)
open VariationalMean (heatK)
variable {n : ℕ}
/-- PlaneRieszPD (supplied), 0 < alpha0 < 1, 1 < alpha < 2 - alpha0, alpha0 < theta < 2 - alpha, c > 0, a j >= 0, a 0 + a 1 = alpha - 1: exponents, Gamma_pl IsCov with Scaling 3 - alpha, EndpointPair, Gamma_low = c m, its spectral measure, V_low = c/pi. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.EndpointLemmas.plane_endpoints_paper (hPD : PlaneRieszPD) {α₀ α θ c : ℝ} {a : Fin 2 → ℝ}
    (hα₀ : 0 < α₀) (_hα₀1 : α₀ < 1) (hα1 : 1 < α) (_hα2 : α < 2 - α₀) (hθ0 : α₀ < θ)
    (hθ : θ < 2 - α) (hc : 0 < c) (ha : ∀ j, 0 ≤ a j) (hs : a 0 + a 1 = α - 1) :
    ((∀ j, 0 ≤ a j ∧ a j < 1) ∧ (∀ j, 0 ≤ a j / (1 - θ) ∧ a j / (1 - θ) < 1) ∧
      a 0 / (1 - θ) + a 1 / (1 - θ) = chi α θ - 1 ∧ chi α θ - 1 < 1) ∧
    (IsCov (planeMeasure c a) ∧ Scaling (planeMeasure c a) (3 - α)) ∧
    EndpointPair θ (chi α θ) (planeMeasure c a) (planeMeasure c 0)
      (planeMeasure c fun j => a j / (1 - θ)) ∧
    planeMeasure c 0 = ENNReal.ofReal c • (volume : Measure (Rd 2)).map planeEmb ∧
    (IsSpectralMeasure (planeMeasure c 0) (planeLowSpectral c) ∧
      planeLowSpectral c (closedBall 0 1) = ENNReal.ofReal (c / π) ∧
      planeLowSpectral c (ball 0 1) = ENNReal.ofReal (c / π) ∧ π * (c / π) / 2 = c / 2) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.EndpointLemmas
