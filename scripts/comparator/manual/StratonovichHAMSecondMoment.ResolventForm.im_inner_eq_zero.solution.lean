namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ComplexConjugate BesselPotentialSpace Real
open HomogHypothesis (Rd)
open H1Mathlib WeakSobolev
variable {d : ℕ}
local notation "L²[" d "]" => Lp ℂ 2 (volume : Measure (Rd d))
/-- For F, G in L^2(R^d; C) with im F x = 0 and im G x = 0 almost everywhere: im <F, G> = 0. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ResolventForm.im_inner_eq_zero {F G : L²[d]} (hF : ∀ᵐ x ∂volume, (F x).im = 0)
    (hG : ∀ᵐ x ∂volume, (G x).im = 0) : (⟪F, G⟫_ℂ).im = 0 := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.ResolventForm.im_inner_eq_zero
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
