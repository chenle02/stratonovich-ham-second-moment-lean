namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Filter Topology FourierTransform TemperedDistribution
open scoped ENNReal ContDiff SchwartzMap LineDeriv Real
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad)
variable {d : ℕ}
/-- f, g in L^2 (real f, g : R^d -> R^d) with g a weak gradient of f, h smooth with h, grad h in L^2, v: int f * fderiv h x v = -int <g x, v> * h x. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Mathlib.weak_smooth {f : Rd d → ℝ} {g : Rd d → Rd d} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (hw : HasWeakGradient f g) {h : Rd d → ℝ}
    (hh : ContDiff ℝ ∞ h) (hL : MemLp h 2 volume) (hG : MemLp (grad h) 2 volume) (v : Rd d) :
    ∫ x, f x * fderiv ℝ h x v = -∫ x, inner ℝ (g x) v * h x := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.H1Mathlib.weak_smooth
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
