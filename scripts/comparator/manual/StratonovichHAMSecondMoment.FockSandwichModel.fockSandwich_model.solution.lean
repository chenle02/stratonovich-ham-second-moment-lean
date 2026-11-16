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
/-- Under PhaseCovariance alpha Gamma mu, eps > 0, psi orthonormal real modes in L^2(mu_eps), N, b: opA0 b is positive, fieldB is self-adjoint and FockSandwich (opA0 b) fieldB (fockD N (ralpha mu alpha)) (alpha/2). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockSandwichModel.fockSandwich_model {alpha ε : ℝ} {Γ μ : Measure (Rd 3)}
    (hPC : PhaseCovariance alpha Γ μ) (hε : 0 < ε) (ψ : Fin m → Lp ℂ 2 (nuEps μ ε))
    (hψ : Orthonormal ℂ ψ) (hreal : ∀ i, ∀ᵐ ξ ∂(nuEps μ ε), ψ i (-ξ) = conj (ψ i ξ))
    (N : ℕ) (b : ℝ) :
    (opA0 (d := 3) (m := m) (N := N) b).IsPositive ∧
      IsSelfAdjoint (fieldB (N := N) b (nuEps_finite hPC.μ_tempered hε) ψ hψ) ∧
      FockSandwich (opA0 (d := 3) (m := m) (N := N) b)
        (fieldB b (nuEps_finite hPC.μ_tempered hε) ψ hψ) (fockD N (ralpha μ alpha))
        (alpha / 2) := by
  exact _root_.StratonovichHAMSecondMoment.FockSandwichModel.fockSandwich_model (StratonovichHamSecondMomentLeanAuditBridge.PhaseContractions.pcToP hPC) hε ψ hψ hreal N b
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockSandwichModel
