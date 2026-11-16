namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ} {ν : Measure (Rd d)}
/-- For f in Lp C 2 (Lebesgue on R^d) and eta: xi -> f (eta - xi) is strongly measurable. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.sm_shift (f : Lp ℂ 2 (volume : Measure (Rd d))) (η : Rd d) :
    StronglyMeasurable (fun ξ : Rd d => f (η - ξ)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
