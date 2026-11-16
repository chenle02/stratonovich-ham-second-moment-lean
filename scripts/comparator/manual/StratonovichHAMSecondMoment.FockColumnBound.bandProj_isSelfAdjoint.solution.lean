namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
/-- For real b: bandProj b is self-adjoint. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.bandProj_isSelfAdjoint (b : ℝ) : IsSelfAdjoint (bandProj (d := d) b) := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.FockColumnBound.bandProj_isSelfAdjoint
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
