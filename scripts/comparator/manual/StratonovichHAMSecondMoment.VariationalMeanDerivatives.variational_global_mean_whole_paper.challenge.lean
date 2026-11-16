namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Metric
open scoped ContDiff
open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open VariationalDilation (CPos conv mean)
open VariationalMean (gMass exists_radius)
variable {d : ℕ}
/-- Under H:homog, Gamma != 0 and Psi in CPos d: the first sentence (C^infinity, integrable integrands, derivatives bounded on K x R^d) and E:variational-global-mean on [0,1]: M, C_Psi >= 0, 0 <= h_s <= M, |h_s(x) - h_t(x)| <= C_Psi |s-t|. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.VariationalMeanDerivatives.variational_global_mean_whole_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) :
    (ContDiff ℝ ∞ (fun p : ℝ × Rd d => mean alpha0 Γ Ψ p.1 p.2) ∧
      (∀ s x, IntegrableOn (fun u => |s - u| ^ (-alpha0) * conv Γ (fun y => Ψ (u, y)) x)
        (Ioo 0 1)) ∧
      ∀ n : ℕ, ∀ K : Set ℝ, IsCompact K → ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ K, ∀ x : Rd d,
        ‖iteratedFDeriv ℝ n (fun p : ℝ × Rd d => mean alpha0 Γ Ψ p.1 p.2) (s, x)‖ ≤ C) ∧
    ∃ M CΨ : ℝ, 0 ≤ M ∧ 0 ≤ CΨ ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ x, 0 ≤ mean alpha0 Γ Ψ s x ∧ mean alpha0 Γ Ψ s x ≤ M) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
        |mean alpha0 Γ Ψ s x - mean alpha0 Γ Ψ t x| ≤ CΨ * |s - t|) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.VariationalMeanDerivatives
