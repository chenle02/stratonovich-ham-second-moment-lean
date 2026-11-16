namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal RealInnerProductSpace
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)
open SpaceTimePositivity (timeMeasure timeMeasure_eq_Icc)
open OccupationCeilingFinite (K0 K0_pos)
open WeakSobolev (IsTestFunction)
open SpatialFourLinear (IsH1Pair SquareBound)
open OccupationPhysicalClass (volI IsOccField SquarePairingBounds)
open OccupationKernelRow (pairMeasure)
open VariationalDilation (CPos mean conv)
variable {d : ℕ}
/-- Gamma even and s-finite, any real a, psi and Gm measurable on R x R^d: the time-kernel Tonelli identity of lines 102-105 for the nonnegative parts ofReal psi, ofReal Gm^2, as lower integrals. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OccupationCompletion.lintegral_kern_pair_even {Γ : Measure (Rd d)} [SFinite Γ] (hE : IsEven Γ) (a : ℝ)
    {ψ Gm : ℝ × Rd d → ℝ} (hψ : Measurable ψ) (hGm : Measurable Gm) :
    ∫⁻ q, ENNReal.ofReal (kern a (q.1 - q.2)) * ∫⁻ z, ENNReal.ofReal (ψ (q.1, z.1)) *
        ENNReal.ofReal (Gm (q.2, z.1 - z.2) ^ 2) ∂(pairMeasure Γ)
        ∂(timeMeasure.prod timeMeasure) =
      ∫⁻ s, ∫⁻ x, (∫⁻ u, ENNReal.ofReal (kern a (s - u)) *
        ∫⁻ y, ENNReal.ofReal (ψ (u, x - y)) ∂Γ ∂timeMeasure) * ENNReal.ofReal (Gm (s, x) ^ 2)
        ∂volume ∂timeMeasure := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
