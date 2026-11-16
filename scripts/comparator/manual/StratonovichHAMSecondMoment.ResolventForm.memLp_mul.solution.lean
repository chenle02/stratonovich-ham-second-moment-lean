namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ComplexConjugate BesselPotentialSpace Real
open HomogHypothesis (Rd)
open H1Mathlib WeakSobolev
variable {d : ℕ}
local notation "L²[" d "]" => Lp ℂ 2 (volume : Measure (Rd d))
/-- For a measurable real a on R^d with |a x| <= M for all x and f in L^2(R^d; C): x -> a(x) f(x) is in L^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ResolventForm.memLp_mul (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀ x, |a x| ≤ M)
    (f : L²[d]) : MemLp (fun x => (a x : ℂ) * f x) 2 volume := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.ResolventForm.memLp_mul
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
