namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal RealInnerProductSpace
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)
open SpaceTimePositivity (timeMeasure timeMeasure_eq_Icc)
open OccupationCeilingFinite (K0 K0_pos)
open WeakSobolev (IsTestFunction)
open SpatialFourierBound (spatialPair)
open VariationalDilation (CPos rawCost)
variable {d : ℕ}
variable (S : SpData d)
variable {S}
/-- For Psi smooth with compact support: s |-> [Psi(s,.)] is in L^2(I; H_sp). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OccupationCompletion.sliceField_memLp {Ψ : ℝ × Rd d → ℝ} (hΨ : ContDiff ℝ ∞ Ψ)
    (hΨs : HasCompactSupport Ψ) : MemLp (sliceField S Ψ) 2 timeMeasure := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
