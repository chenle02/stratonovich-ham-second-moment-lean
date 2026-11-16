namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ComplexConjugate BesselPotentialSpace Real
open HomogHypothesis (Rd)
open H1Mathlib WeakSobolev
variable {d : ℕ}
/-- For u in Mathlib's H^1(R^d): h12NormSq u = int om jinv |fourierH1 u|^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ResolventForm.h12NormSq_eq_integral (u : H^{1}(Rd d)) :
    h12NormSq u = ∫ x, om x * jinv x * ‖fourierH1 u x‖ ^ 2 := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.ResolventForm.h12NormSq_eq_integral
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
