namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter Topology
open scoped ENNReal
open HomogHypothesis (Rd HomogCovariance)
variable {d : ℕ}
variable {E : Type*} [NormedAddCommGroup E]
/-- For u, v in L^2(R^d; E): int |u x - v x|^2 dx = |u - v|^2 in [0, infinity]. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ClassOBridge.lintegral_slice (u v : Lp E 2 (volume : Measure (Rd d))) :
    ∫⁻ x, ‖(u : Rd d → E) x - v x‖ₑ ^ (2 : ℝ) = ‖u - v‖ₑ ^ (2 : ℝ) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOBridge
