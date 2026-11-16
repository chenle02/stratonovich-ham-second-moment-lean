namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ComplexConjugate BesselPotentialSpace Real
open HomogHypothesis (Rd)
open H1Mathlib WeakSobolev
variable {d : ℕ}
local notation "L²[" d "]" => Lp ℂ 2 (volume : Measure (Rd d))
/-- For measurable real b with |b x| <= N for all x and f in L^2(R^d; C): x -> b(x) |f x|^2 is integrable. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ResolventForm.integrable_mul_norm_sq {b : Rd d → ℝ} (hb : Measurable b) {N : ℝ}
    (hN : ∀ x, |b x| ≤ N) (f : L²[d]) : Integrable (fun x => b x * ‖f x‖ ^ 2) volume := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
