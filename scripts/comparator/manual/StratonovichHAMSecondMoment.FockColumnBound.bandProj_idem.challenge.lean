namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
/-- For real b: bandProj b composed with itself equals bandProj b. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.bandProj_idem (b : ℝ) : bandProj (d := d) b ∘L bandProj b = bandProj b := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
