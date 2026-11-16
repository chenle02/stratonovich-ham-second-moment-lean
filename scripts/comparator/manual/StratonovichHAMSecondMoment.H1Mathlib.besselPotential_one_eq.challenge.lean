namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform TemperedDistribution
open scoped ENNReal ContDiff SchwartzMap LineDeriv Real
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad)
variable {d : ℕ}
/-- For a complex tempered distribution T on R^d: J^1 T = J^(-1) T + sum_j R_j(xi_j T), R_j the multiplier of rieszSym j, xi_j T that of coordSym j. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Mathlib.besselPotential_one_eq (T : 𝓢'(Rd d, ℂ)) :
    besselPotential (Rd d) ℂ 1 T = besselPotential (Rd d) ℂ (-1) T +
      ∑ j, fourierMultiplierCLM ℂ (rieszSym j) (fourierMultiplierCLM ℂ (coordSym j) T) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
