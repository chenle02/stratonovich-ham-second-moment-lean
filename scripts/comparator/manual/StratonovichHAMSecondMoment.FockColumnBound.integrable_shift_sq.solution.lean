namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
variable {ν : Measure (Rd d)}
/-- For finite nu and f in L^2(Lebesgue on R^d): (eta, xi) -> |f(eta - xi)|^2 is integrable for Lebesgue x nu. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.integrable_shift_sq [IsFiniteMeasure ν] (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    Integrable (fun p : Rd d × Rd d => ‖f (p.1 - p.2)‖ ^ 2)
      ((volume : Measure (Rd d)).prod ν) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.FockColumnBound.integrable_shift_sq
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
