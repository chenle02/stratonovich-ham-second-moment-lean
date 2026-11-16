namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Filter Metric Topology
open scoped ContDiff ENNReal RealInnerProductSpace
open HomogHypothesis (Rd HomogCovariance IsSpectralMeasure IsEven)
open TimeSchur (kern kern_nonneg measurable_kern kern_sub_comm)
open SpaceTimePositivity (timeMeasure timeMeasure_eq_Icc)
open OccupationCeilingFinite (K0 K0_pos)
variable (p : TParams) (G : Type*) [NormedAddCommGroup G] [InnerProductSpace ℝ G]
variable {p G}
variable (p G)
variable {p G}
variable (p G)
variable {p G}
/-- G a real Hilbert space, F in L^2(I; G): |s-t|^(-a)<F(s),F(t)> integrable on I^2, |J_G F|^2 = int int |s-t|^(-a)<F(s),F(t)> <= K_0 |F|^2, and <J_G F, J_G F'> = kform a F F' for all F'. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OccupationCompletion.positive_bochner_inclusion [CompleteSpace G] (F : Lp G 2 timeMeasure) :
    Integrable (fun q : ℝ × ℝ => kern p.a (q.1 - q.2) * ⟪F q.1, F q.2⟫)
        (timeMeasure.prod timeMeasure) ∧
      ‖J p G F‖ ^ 2 = ∫ q, kern p.a (q.1 - q.2) * ⟪F q.1, F q.2⟫
        ∂(timeMeasure.prod timeMeasure) ∧
      ‖J p G F‖ ^ 2 ≤ K0 p.a * ‖F‖ ^ 2 ∧
      ∀ F' : Lp G 2 timeMeasure, ⟪J p G F, J p G F'⟫ = kform p.a ⇑F ⇑F' := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationCompletion
