namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
/-- For rho > 0 and real b: bandProj b composed with sqrtResolvent rho equals sqrtResolvent rho composed with bandProj b. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.bandProj_comm {ρ : ℝ} (hρ : 0 < ρ) (b : ℝ) :
    bandProj (d := d) b ∘L sqrtResolvent ρ hρ = sqrtResolvent ρ hρ ∘L bandProj b := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
