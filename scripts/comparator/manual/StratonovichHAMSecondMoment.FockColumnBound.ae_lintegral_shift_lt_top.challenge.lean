namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ} {ν : Measure (Rd d)}
/-- For finite nu and f in Lp C 2 (Lebesgue on R^d): for a.e. eta, the lower integral of |f (eta - xi)|^2 against nu is finite. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.ae_lintegral_shift_lt_top [IsFiniteMeasure ν] (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    ∀ᵐ η ∂(volume : Measure (Rd d)), ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν < ⊤ := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
