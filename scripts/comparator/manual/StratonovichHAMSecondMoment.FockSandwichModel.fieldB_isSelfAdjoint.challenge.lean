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
variable {d m N : ℕ}
variable {ν : Measure (Rd d)}
/-- For nu finite and even (map (x -> -x) nu = nu), psi orthonormal with psi i (-xi) = conj (psi i xi) nu-a.e.: fieldB b hfin psi hpsi is self-adjoint. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockSandwichModel.fieldB_isSelfAdjoint (b : ℝ) (hfin : IsFiniteMeasure ν)
    (heven : ν.map (fun x => -x) = ν) (ψ : Fin m → Lp ℂ 2 ν) (hψ : Orthonormal ℂ ψ)
    (hreal : ∀ i, ∀ᵐ ξ ∂ν, ψ i (-ξ) = conj (ψ i ξ)) :
    IsSelfAdjoint (fieldB (N := N) b hfin ψ hψ) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockSandwichModel
