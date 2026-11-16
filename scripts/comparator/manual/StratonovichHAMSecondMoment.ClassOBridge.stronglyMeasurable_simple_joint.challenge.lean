namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter Topology
open scoped ENNReal
open HomogHypothesis (Rd HomogCovariance)
variable {d : ℕ}
variable {E : Type*} [NormedAddCommGroup E]
/-- For a simple function phi from R to L^2(R^d; E): (s, x) -> (phi s)(x) is strongly measurable on R x R^d. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ClassOBridge.stronglyMeasurable_simple_joint (φ : SimpleFunc ℝ (Lp E 2 (volume : Measure (Rd d)))) :
    StronglyMeasurable (fun p : ℝ × Rd d => (φ p.1 : Rd d → E) p.2) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge
