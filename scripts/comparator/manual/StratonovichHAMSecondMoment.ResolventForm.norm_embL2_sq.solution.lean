namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ComplexConjugate BesselPotentialSpace Real
open HomogHypothesis (Rd)
open H1Mathlib WeakSobolev
variable {d : ℕ}
/-- For u in Mathlib's H^1(R^d): |embL2 u|^2 = int jinv^2 |fourierH1 u|^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ResolventForm.norm_embL2_sq (u : H^{1}(Rd d)) :
    ‖embL2 u‖ ^ 2 = ∫ x, jinv x ^ 2 * ‖fourierH1 u x‖ ^ 2 := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.ResolventForm.norm_embL2_sq
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
