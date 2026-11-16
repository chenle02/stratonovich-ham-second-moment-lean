namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOH1
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter Topology
open scoped ENNReal BesselPotentialSpace
open HomogHypothesis (Rd HomogCovariance)
open WeakSobolev (HasWeakGradient MemH1)
open SpatialFourLinear (IsH1Pair H1Tendsto C4 SquareBound Nnorm)
open SpatialStaticControls (zE)
open OccupationKernelRow (pairing pairMeasure)
variable {d : ℕ}
/-- For a real inner product space E and u, v in L^2(R^d; E): int |u x - v x|^2 = |u - v|^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.ClassOH1.integral_norm_sub_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : Lp E 2 (volume : Measure (Rd d))) :
    ∫ x, ‖(u : Rd d → E) x - v x‖ ^ 2 = ‖u - v‖ ^ 2 := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.ClassOH1.integral_norm_sub_sq
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.ClassOH1
