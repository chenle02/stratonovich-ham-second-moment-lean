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
/-- For nu finite and psi orthonormal: diag S_b * fieldB = fieldB and fieldB * diag S_b = fieldB. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockSandwichModel.fieldB_band (b : ℝ) (hfin : IsFiniteMeasure ν) (ψ : Fin m → Lp ℂ 2 ν)
    (hψ : Orthonormal ℂ ψ) :
    toH (diagOp (bandProj b)) * fieldB (N := N) b hfin ψ hψ = fieldB b hfin ψ hψ ∧
      fieldB (N := N) b hfin ψ hψ * toH (diagOp (bandProj b)) = fieldB b hfin ψ hψ := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.FockSandwichModel.fieldB_band
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockSandwichModel
