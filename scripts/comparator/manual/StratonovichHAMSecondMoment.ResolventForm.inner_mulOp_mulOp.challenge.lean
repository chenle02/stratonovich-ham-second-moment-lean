namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ComplexConjugate BesselPotentialSpace Real
open HomogHypothesis (Rd)
open H1Mathlib WeakSobolev
variable {d : ℕ}
local notation "L²[" d "]" => Lp ℂ 2 (volume : Measure (Rd d))
/-- For measurable real a, b with |a| <= M, |b| <= N and f in L^2(R^d; C): <M_a f, M_b f> = int a b |f|^2 (as a complex number). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ResolventForm.inner_mulOp_mulOp (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ x, |a x| ≤ M)
    (b : Rd d → ℝ) (hb : Measurable b) (N : ℝ) (hN : ∀ x, |b x| ≤ N) (f : L²[d]) :
    ⟪mulOp a ha M hM f, mulOp b hb N hN f⟫_ℂ = ((∫ x, a x * b x * ‖f x‖ ^ 2 : ℝ) : ℂ) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
