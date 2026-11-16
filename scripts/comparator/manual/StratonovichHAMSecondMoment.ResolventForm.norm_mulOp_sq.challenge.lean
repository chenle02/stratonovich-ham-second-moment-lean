namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ComplexConjugate BesselPotentialSpace Real
open HomogHypothesis (Rd)
open H1Mathlib WeakSobolev
variable {d : ℕ}
local notation "L²[" d "]" => Lp ℂ 2 (volume : Measure (Rd d))
/-- For measurable real a with |a| <= M and f in L^2(R^d; C): |M_a f|^2 = int a^2 |f|^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ResolventForm.norm_mulOp_sq (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ x, |a x| ≤ M)
    (f : L²[d]) :
    ‖mulOp a ha M hM f‖ ^ 2 = ∫ x, a x ^ 2 * ‖f x‖ ^ 2 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
