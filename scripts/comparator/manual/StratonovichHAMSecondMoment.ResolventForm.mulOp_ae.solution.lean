namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Filter Topology FourierTransform
open scoped ENNReal InnerProductSpace ComplexConjugate BesselPotentialSpace Real
open HomogHypothesis (Rd)
open H1Mathlib WeakSobolev
variable {d : ℕ}
local notation "L²[" d "]" => Lp ℂ 2 (volume : Measure (Rd d))
/-- For measurable real a with |a| <= M and f in L^2(R^d; C): M_a f = a f almost everywhere. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ResolventForm.mulOp_ae (a : Rd d → ℝ) (ha : Measurable a) (M : ℝ)
    (hM : ∀ x, |a x| ≤ M) (f : L²[d]) :
    (mulOp a ha M hM f : Rd d → ℂ) =ᵐ[volume] fun x => (a x : ℂ) * f x := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.ResolventForm.mulOp_ae
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ResolventForm
