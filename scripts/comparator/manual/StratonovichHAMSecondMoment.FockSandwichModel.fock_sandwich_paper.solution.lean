namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockSandwichModel
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Real Finset Filter Topology Set
open scoped ComplexConjugate Nat
open HomogHypothesis (Rd)
open HermiteFock (Supp degLE fieldOp mem_degLE deg gmul cre ann)
open GaussianHermite (unitIdx)
open FockColumnBound (mulOp mulOp_ae op_ext band measurable_band abs_band_le bandProj wt measurable_wt sqrtResolvent nuEps nuEps_finite modes)
open ComplexPhaseScalar (invSqrtShift shiftOp)
open StaticInteractionCompleted (FockSandwich CPInputs PropagatorBlock InDisc)
open StaticPhaseCauchy (fockD taylorCoeff allOrdersA)
open SpectralMassIdentity (ralpha)
open PhaseContractions (PhaseCovariance dGam)
open IntervalScalar (staticE)
variable {m : ℕ}
/-- PhaseCovariance alpha Gamma mu, R = R_alpha, eps > 0, real orthonormal modes psi in L^2(mu_eps), N, b: A_0 positive, B self-adjoint, S_b B = B = B S_b, invSqrtShift A_0 rho S_b = A_rho^(-1/2) S_b for rho > 0, FockSandwich A_0 B (fockD N R) (alpha/2). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockSandwichModel.fock_sandwich_paper {alpha R ε : ℝ} {Γ μ : Measure (Rd 3)}
    (hPC : PhaseCovariance alpha Γ μ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hε : 0 < ε) (ψ : Fin m → Lp ℂ 2 (nuEps μ ε)) (hψ : Orthonormal ℂ ψ)
    (hreal : ∀ i, ∀ᵐ ξ ∂(nuEps μ ε), ψ i (-ξ) = conj (ψ i ξ)) (N : ℕ) (b : ℝ) :
    let A0 := opA0 (d := 3) (m := m) (N := N) b
    let B := fieldB (N := N) b (nuEps_finite hPC.μ_tempered hε) ψ hψ
    let P := toH (m := m) (N := N) (diagOp (bandProj (d := 3) b))
    A0.IsPositive ∧ IsSelfAdjoint B ∧ (P * B = B ∧ B * P = B) ∧
      (∀ ρ (hρ : 0 < ρ), invSqrtShift A0 ρ * P = toH (diagOp (sqrtResolvent ρ hρ)) * P) ∧
      FockSandwich A0 B (fockD N R) (alpha / 2) := by
  exact _root_.StratonovichHAMSecondMoment.FockSandwichModel.fock_sandwich_paper (StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcToP hPC) hRdef hε ψ hψ hreal N b
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockSandwichModel
