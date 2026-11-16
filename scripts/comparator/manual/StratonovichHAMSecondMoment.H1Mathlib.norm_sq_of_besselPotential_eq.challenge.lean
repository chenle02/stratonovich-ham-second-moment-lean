namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform TemperedDistribution
open scoped ENNReal ContDiff SchwartzMap LineDeriv Real
open HomogHypothesis (Rd)
open WeakSobolev
open VariationalFloor (grad)
variable {d : ℕ}
/-- f, g in L^2 (real f, g : R^d -> R^d) with g a weak gradient of f, W in L^2(R^d; C) with J^1 T_f = T_W: |W|^2 = int f^2 + (2 pi)^(-2) int |g|^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.H1Mathlib.norm_sq_of_besselPotential_eq {f : Rd d → ℝ} {g : Rd d → Rd d}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (hw : HasWeakGradient f g)
    (W : Lp ℂ 2 (volume : Measure (Rd d)))
    (hW : besselPotential (Rd d) ℂ 1 (toDistr hf) = (W : 𝓢'(Rd d, ℂ))) :
    ‖W‖ ^ 2 = (∫ x, f x ^ 2) + ((2 * π) ^ 2)⁻¹ * ∫ x, ‖g x‖ ^ 2 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.H1Mathlib
