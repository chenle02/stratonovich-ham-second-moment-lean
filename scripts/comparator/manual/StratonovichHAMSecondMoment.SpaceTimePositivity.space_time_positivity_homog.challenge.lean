namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity
open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open WeakSobolev (IsTestFunction)
open SpatialFourierBound (spatialPair)
open TimeSchur (kern kern_nonneg measurable_kern)
open VariationalDilation (CPos conv mean rawCost)
-- Statement copied from the source (the printed type unfolds `Rd d` to `EuclideanSpace ℝ (Fin d)` (a `WithLp` type) at one occurrence where the declaration keeps `Rd d`).
-- The section variables used, written as binders: {d : ℕ}.
/-- If HomogCovariance d alpha alpha0 Gamma mu, F = stForm alpha0 Gamma, for CC fields: F's integrand is integrable, F(P,P) >= 0, F(P,Q)^2 <= F(P,P)F(Q,Q); for Psi in CPos d, CC G: F(Psi,Psi) = rawCost, int int h G^2 = F(Psi,G^2) (integrable), <= sqrt(rawCost F(G^2,G^2)). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SpaceTimePositivity.space_time_positivity_homog {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) :
    (∀ Φ₁ Φ₂ : ℝ × Rd d → ℝ, Continuous Φ₁ → HasCompactSupport Φ₁ → Continuous Φ₂ →
      HasCompactSupport Φ₂ →
      Integrable (fun p : ℝ × ℝ => kern alpha0 (p.1 - p.2) * stPair Γ Φ₁ Φ₂ p)
        (timeMeasure.prod timeMeasure)) ∧
    (∀ Φ : ℝ × Rd d → ℝ, Continuous Φ → HasCompactSupport Φ → 0 ≤ stForm alpha0 Γ Φ Φ) ∧
    (∀ Φ₁ Φ₂ : ℝ × Rd d → ℝ, Continuous Φ₁ → HasCompactSupport Φ₁ → Continuous Φ₂ →
      HasCompactSupport Φ₂ →
      stForm alpha0 Γ Φ₁ Φ₂ ^ 2 ≤ stForm alpha0 Γ Φ₁ Φ₁ * stForm alpha0 Γ Φ₂ Φ₂) ∧
    (∀ Ψ ∈ CPos d, stForm alpha0 Γ Ψ Ψ = rawCost alpha0 Γ Ψ) ∧
    (∀ Ψ ∈ CPos d, ∀ G : ℝ × Rd d → ℝ, Continuous G → HasCompactSupport G →
      (∀ t ∈ Icc (0 : ℝ) 1, Integrable (fun x => mean alpha0 Γ Ψ t x * G (t, x) ^ 2)) ∧
      IntegrableOn (fun t => ∫ x, mean alpha0 Γ Ψ t x * G (t, x) ^ 2) (Ioo (0 : ℝ) 1) ∧
      ∫ t in Ioo (0 : ℝ) 1, ∫ x, mean alpha0 Γ Ψ t x * G (t, x) ^ 2 =
        stForm alpha0 Γ Ψ (fun p => G p ^ 2)) ∧
    (∀ Ψ ∈ CPos d, ∀ G : ℝ × Rd d → ℝ, Continuous G → HasCompactSupport G →
      ∫ t in Ioo (0 : ℝ) 1, ∫ x, mean alpha0 Γ Ψ t x * G (t, x) ^ 2 ≤
        Real.sqrt (rawCost alpha0 Γ Ψ *
          stForm alpha0 Γ (fun p => G p ^ 2) (fun p => G p ^ 2))) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpaceTimePositivity
