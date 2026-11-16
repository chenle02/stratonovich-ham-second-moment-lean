namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszPositiveDefinite
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Real Filter
open scoped ENNReal NNReal Topology
open HomogHypothesis (Rd IsTempered IsPosDefDistr)
open EndpointLemmas
open EndpointCorollaries
/-- For 0 < alpha0 < 1, 1 < alpha < 2 - alpha0, alpha0 < theta < 2 - alpha, c > 0, a_j >= 0, a_0 + a_1 = alpha - 1: every conclusion of EndpointLemmas.plane_endpoints_paper with PlaneRieszPD proved (alpha0 < 1, alpha < 2 - alpha0 unused). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.RieszPositiveDefinite.plane_endpoints_paper_proved {α₀ α θ c : ℝ} {a : Fin 2 → ℝ}
    (hα₀ : 0 < α₀) (hα₀1 : α₀ < 1) (hα1 : 1 < α) (hα2 : α < 2 - α₀) (hθ0 : α₀ < θ)
    (hθ : θ < 2 - α) (hc : 0 < c) (ha : ∀ j, 0 ≤ a j) (hs : a 0 + a 1 = α - 1) :
    ((∀ j, 0 ≤ a j ∧ a j < 1) ∧ (∀ j, 0 ≤ a j / (1 - θ) ∧ a j / (1 - θ) < 1) ∧
      a 0 / (1 - θ) + a 1 / (1 - θ) = chi α θ - 1 ∧ chi α θ - 1 < 1) ∧
    (IsCov (planeMeasure c a) ∧ Scaling (planeMeasure c a) (3 - α)) ∧
    EndpointPair θ (chi α θ) (planeMeasure c a) (planeMeasure c 0)
      (planeMeasure c fun j => a j / (1 - θ)) ∧
    planeMeasure c 0 = ENNReal.ofReal c • (volume : Measure (Rd 2)).map planeEmb ∧
    (HomogHypothesis.IsSpectralMeasure (planeMeasure c 0) (planeLowSpectral c) ∧
      planeLowSpectral c (Metric.closedBall 0 1) = ENNReal.ofReal (c / π) ∧
      planeLowSpectral c (Metric.ball 0 1) = ENNReal.ofReal (c / π) ∧
      π * (c / π) / 2 = c / 2) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.RieszPositiveDefinite
