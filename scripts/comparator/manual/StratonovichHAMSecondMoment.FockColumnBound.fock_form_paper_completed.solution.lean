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
set_option maxHeartbeats 4000000 in
/-- PhaseCovariance alpha Gamma mu on R^3, R = R_alpha, eps, rho > 0, orthonormal real modes psi_i in L^2(nuEps mu eps), P = bandProj b, H_i = S M_i S, v of degree <= N: fock_form_paper's bounds (d_N rho^(alpha/2-2), coefficients and Gaussian L^2 with integrability) and symmetry. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.fock_form_paper_completed {alpha R ε ρ b : ℝ} {Γ μ : Measure (Rd 3)}
    (hPC : PhaseContractions.PhaseCovariance alpha Γ μ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hε : 0 < ε) (hρ : 0 < ρ) {m : ℕ} (ψ : Fin m → Lp ℂ 2 (nuEps μ ε))
    (hψ : Orthonormal ℂ ψ) (hreal : ∀ i, ∀ᵐ ξ ∂(nuEps μ ε), ψ i (-ξ) = conj (ψ i ξ))
    (N : ℕ) {v : (Fin m → ℕ) → Lp ℂ 2 (volume : Measure (Rd 3))} (hv : Supp N v) :
    let H := fun i => sqrtResolvent ρ hρ ∘L
      modes (nuEps_finite hPC.μ_tempered hε) ψ hψ i ∘L sqrtResolvent ρ hρ
    let P := bandProj (d := 3) b
    ∑ k ∈ degLE m N, ‖fieldOp (fun i => P ∘L H i ∘L P) v k‖ ^ 2 ≤
        (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 * ∑ k ∈ degLE m N, ‖v k‖ ^ 2 ∧
      Integrable (fun x => ‖iota N (fieldOp (fun i => P ∘L H i ∘L P) v) x‖ ^ 2)
        (GaussianIBP.stdPi m) ∧
      ∫ x, ‖iota N (fieldOp (fun i => P ∘L H i ∘L P) v) x‖ ^ 2 ∂GaussianIBP.stdPi m ≤
        (StaticPhaseCauchy.fockD N R * ρ ^ (alpha / 2 - 2)) ^ 2 *
          ∫ x, ‖iota N v x‖ ^ 2 ∂GaussianIBP.stdPi m ∧
      ∀ w : (Fin m → ℕ) → Lp ℂ 2 (volume : Measure (Rd 3)), Supp N w →
        ∑ k ∈ degLE m N, inner ℂ (fieldOp (fun i => P ∘L H i ∘L P) v k) (w k) =
          ∑ k ∈ degLE m N, inner ℂ (v k) (fieldOp (fun i => P ∘L H i ∘L P) w k) := by
  bridge_revert_all
  bridge_rw
  intro alpha R ε ρ b Γ μ hPC hRdef hε hρ m ψ hψ hreal N v hv
  first
    | exact _root_.StratonovichHAMSecondMoment.FockColumnBound.fock_form_paper_completed (StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcToP hPC) hRdef hε hρ ψ hψ hreal N hv
    | exact _root_.StratonovichHAMSecondMoment.FockColumnBound.fock_form_paper_completed hPC hRdef hε hρ ψ hψ hreal N hv
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
