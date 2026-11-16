namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Metric
open scoped ContDiff
open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open VariationalDilation (CPos conv mean)
open VariationalMean (gMass exists_radius)
variable {d : ℕ}
variable {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
  (hsp : IsSpectralMeasure Γ μ)
include hΓt hμt hsp
/-- Gamma, mu tempered with the spectral convention, Psi in CPos d, a < 1: (s,x) -> h_s(x) is C^infinity on R x R^d, its integrand is integrable on (0,1) for every s, x, and each D^n h is bounded on K x R^d for every compact K. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.VariationalMeanDerivatives.mean_derivatives {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) {a : ℝ} (ha : a < 1) :
    ContDiff ℝ ∞ (fun p : ℝ × Rd d => mean a Γ Ψ p.1 p.2) ∧
    (∀ s x, IntegrableOn (fun u => |s - u| ^ (-a) * conv Γ (fun y => Ψ (u, y)) x)
      (Ioo 0 1)) ∧
    ∀ n : ℕ, ∀ K : Set ℝ, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ∀ x : Rd d,
      ‖iteratedFDeriv ℝ n (fun p : ℝ × Rd d => mean a Γ Ψ p.1 p.2) (s, x)‖ ≤ C := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
