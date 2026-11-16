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
variable {p : TParams}
/-- For Psi, Phi smooth with compact support: <incl Psi, incl Phi>_(H_I) = stForm a Gamma Psi Phi = int int_(I^2) |s-t|^(-a) B_Gamma(Psi(s,.), Phi(t,.)). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OccupationCompletion.inner_incl {Ψ Φ : ℝ × Rd d → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hΨs : HasCompactSupport Ψ)
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : HasCompactSupport Φ) :
    ⟪incl p S Ψ, incl p S Φ⟫ = SpaceTimePositivity.stForm p.a S.Γ Ψ Φ := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.OccupationCompletion.inner_incl
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
