namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Metric
open scoped ContDiff
open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open VariationalDilation (CPos conv mean)
open VariationalMean (gMass exists_radius)
variable {d : ℕ}
/-- Under H:homog (HomogCovariance d alpha alpha0 Gamma mu), Gamma != 0 (unused) and Psi in CPos d: the three conclusions of mean_derivatives with a = alpha0. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.VariationalMeanDerivatives.variational_global_mean_derivatives_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) :
    ContDiff ℝ ∞ (fun p : ℝ × Rd d => mean alpha0 Γ Ψ p.1 p.2) ∧
    (∀ s x, IntegrableOn (fun u => |s - u| ^ (-alpha0) * conv Γ (fun y => Ψ (u, y)) x)
      (Ioo 0 1)) ∧
    ∀ n : ℕ, ∀ K : Set ℝ, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ∀ x : Rd d,
      ‖iteratedFDeriv ℝ n (fun p : ℝ × Rd d => mean alpha0 Γ Ψ p.1 p.2) (s, x)‖ ≤ C := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.VariationalMeanDerivatives.variational_global_mean_derivatives_paper
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
