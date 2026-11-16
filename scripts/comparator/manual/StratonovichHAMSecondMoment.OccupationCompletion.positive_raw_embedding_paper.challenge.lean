namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal RealInnerProductSpace
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)
open SpaceTimePositivity (timeMeasure timeMeasure_eq_Icc)
open OccupationCeilingFinite (K0 K0_pos)
open SpatialFourLinear (IsH1Pair H1Tendsto)
open OccupationPhysicalClass (volI sqPair IsOccField)
open VariationalDilation (CPos rawCost)
variable {d : ℕ}
/-- HomogCovariance d alpha alpha0 Gamma mu, Gamma != 0 (unused), G a real Hilbert space: E:positive-bochner-inclusion (integrable, |J_G F|^2 = kernel integral <= K_0 |F|^2) and, for Psi in C_pos, |incl Psi|^2_(H_I) = v_Psi = stForm. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OccupationCompletion.positive_raw_embedding_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ : Γ ≠ 0) (G : Type*) [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [CompleteSpace G] :
    (∀ F : Lp G 2 timeMeasure,
      Integrable (fun q : ℝ × ℝ => kern alpha0 (q.1 - q.2) * ⟪F q.1, F q.2⟫)
        (timeMeasure.prod timeMeasure) ∧
      ‖J (TParams.ofHomog hH) G F‖ ^ 2 =
        ∫ q, kern alpha0 (q.1 - q.2) * ⟪F q.1, F q.2⟫ ∂(timeMeasure.prod timeMeasure) ∧
      ‖J (TParams.ofHomog hH) G F‖ ^ 2 ≤ K0 alpha0 * ‖F‖ ^ 2) ∧
    ∀ Ψ ∈ CPos d,
      ‖incl (TParams.ofHomog hH) (SpData.ofHomog hH) Ψ‖ ^ 2 = rawCost alpha0 Γ Ψ ∧
      ‖incl (TParams.ofHomog hH) (SpData.ofHomog hH) Ψ‖ ^ 2 =
        SpaceTimePositivity.stForm alpha0 Γ Ψ Ψ := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
