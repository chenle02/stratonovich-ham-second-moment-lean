namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ComplexConjugate BesselPotentialSpace Real
open HomogHypothesis (Rd)
open H1Mathlib WeakSobolev
variable {d : ℕ}
local notation "L²[" d "]" => Lp ℂ 2 (volume : Measure (Rd d))
/-- For measurable real a with |a| <= M and f in L^2(R^d; C): <M_a f, f> = int a |f|^2 (as a complex number). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ResolventForm.inner_mulOp_left (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ x, |a x| ≤ M)
    (f : L²[d]) : ⟪mulOp a ha M hM f, f⟫_ℂ = ((∫ x, a x * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
