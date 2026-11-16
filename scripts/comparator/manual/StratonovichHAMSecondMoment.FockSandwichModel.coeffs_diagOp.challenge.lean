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
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] {m N : ℕ}
/-- coeffs (diagOp T x) k = T (coeffs x k). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockSandwichModel.coeffs_diagOp (T : X →L[ℂ] X) (x : FockSp X m N) (k : Fin m → ℕ) :
    coeffs (diagOp T x) k = T (coeffs x k) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockSandwichModel
