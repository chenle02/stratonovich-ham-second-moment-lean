namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ComplexConjugate BesselPotentialSpace Real
open HomogHypothesis (Rd)
open H1Mathlib WeakSobolev
variable {d : ℕ}
/-- For u in Mathlib's H^1(R^d): msNormSq u = int msWeight |fourierH1 u|^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ResolventForm.msNormSq_eq_integral (u : H^{1}(Rd d)) :
    msNormSq u = ∫ x, msWeight x * ‖fourierH1 u x‖ ^ 2 := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.ResolventForm.msNormSq_eq_integral
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
