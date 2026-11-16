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
open SpatialFourLinear (IsH1Pair C4 SquareBound)
open OccupationPhysicalClass (volI sqPair gradSqE Tlin IsOccField SquarePairingBounds)
open OccupationKernelRow (pairMeasure pairing)
open SpatialStaticControls (IsUnitH1)
open VariationalDilation (CPos rawCost)
variable {d : ℕ} (S : SpData d)
variable {S}
variable {p : TParams}
/-- SquareBound and SquarePairingBounds; R >= 0; 0 < alpha < 2; IsOccField G DG; Psi smooth with compact support: <incl Psi, rho_g> = int int_(I^2) |s-t|^(-a) B_Gamma(Psi(s,.), g_t^2). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OccupationCompletion.inner_incl_rho {alpha R : ℝ} (hB : SquareBound S.Γ alpha R)
    (hSPB : SquarePairingBounds S.Γ alpha R) (hR0 : 0 ≤ R) (ha0 : 0 < alpha) (ha2 : alpha < 2)
    {G : ℝ → Rd d → ℝ} {DG : ℝ → Rd d → Rd d} (hO : IsOccField G DG) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : ContDiff ℝ ∞ Ψ) (hΨs : HasCompactSupport Ψ) :
    ⟪incl p S Ψ, rho p S G⟫ = ∫ q, kern p.a (q.1 - q.2) *
      testSqPair S (fun x => Ψ (q.1, x)) (G q.2) ∂(timeMeasure.prod timeMeasure) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.OccupationCompletion.inner_incl_rho
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
