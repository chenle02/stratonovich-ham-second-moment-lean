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
/-- For rho > 0: invSqrtShift (opA0 b) rho * toH (diagOp (bandProj b)) = toH (diagOp (sqrtResolvent rho hrho)) * toH (diagOp (bandProj b)). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockSandwichModel.invSqrtShift_band {ρ : ℝ} (hρ : 0 < ρ) (b : ℝ) :
    invSqrtShift (opA0 (d := d) (m := m) (N := N) b) ρ * toH (diagOp (bandProj b)) =
      toH (diagOp (sqrtResolvent ρ hρ)) * toH (diagOp (bandProj b)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockSandwichModel
