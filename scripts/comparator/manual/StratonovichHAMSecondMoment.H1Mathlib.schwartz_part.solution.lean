namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Filter Topology FourierTransform TemperedDistribution
open scoped ENNReal ContDiff SchwartzMap LineDeriv Real
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad)
variable {d : ℕ}
/-- For chi complex Schwartz and L : C ->L[R] R with |L| <= 1: x -> L(chi x) is smooth, in L^2, has gradient in L^2, and its derivative is L applied to that of chi. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Mathlib.schwartz_part {χ : 𝓢(Rd d, ℂ)} (L : ℂ →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1) :
    ContDiff ℝ ∞ (fun x => L (χ x)) ∧ MemLp (fun x => L (χ x)) 2 volume ∧
      MemLp (grad fun x => L (χ x)) 2 volume ∧
      ∀ x v, fderiv ℝ (fun y => L (χ y)) x v = L (fderiv ℝ χ x v) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.H1Mathlib.schwartz_part
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
