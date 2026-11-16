namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (bridge_auto needs more heartbeats than the default for this statement).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
open HomogHypothesis (IsTempered IsEven IsSpectralMeasure HomogCovariance)
open SpectralHomog (SpectralHomogeneous)
open SpectralMassIdentity (ralpha)
open HermiteFock (Supp degLE fieldOp iota)
/-- Under PhaseCovariance alpha Gamma mu (R^3), R = R_alpha, eps, rho > 0, orthonormal psi_i in L^2(nuEps mu eps) with psi_i(-xi) = conj(psi_i xi) a.e.: each H_i = S M_i S (S = sqrtResolvent rho) is self-adjoint and FockColumn H (R * rho^(alpha - 4)). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.fock_column_completed {alpha R ε ρ : ℝ} {Γ μ : Measure (Rd 3)}
    (hPC : PhaseContractions.PhaseCovariance alpha Γ μ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hε : 0 < ε) (hρ : 0 < ρ) {m : ℕ} (ψ : Fin m → Lp ℂ 2 (nuEps μ ε))
    (hψ : Orthonormal ℂ ψ) (hreal : ∀ i, ∀ᵐ ξ ∂(nuEps μ ε), ψ i (-ξ) = conj (ψ i ξ)) :
    (∀ i, IsSelfAdjoint (sqrtResolvent ρ hρ ∘L
        modes (nuEps_finite hPC.μ_tempered hε) ψ hψ i ∘L sqrtResolvent ρ hρ)) ∧
      FockForm.FockColumn (fun i => sqrtResolvent ρ hρ ∘L
        modes (nuEps_finite hPC.μ_tempered hε) ψ hψ i ∘L sqrtResolvent ρ hρ)
        (R * ρ ^ (alpha - 4)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
