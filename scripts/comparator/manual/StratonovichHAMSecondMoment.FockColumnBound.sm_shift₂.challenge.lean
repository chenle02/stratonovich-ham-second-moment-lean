namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ} {ν : Measure (Rd d)}
/-- For f in Lp C 2 (Lebesgue on R^d): (eta, xi) -> f (eta - xi) is strongly measurable on R^d x R^d. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.sm_shift₂ (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    StronglyMeasurable (fun p : Rd d × Rd d => f (p.1 - p.2)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
