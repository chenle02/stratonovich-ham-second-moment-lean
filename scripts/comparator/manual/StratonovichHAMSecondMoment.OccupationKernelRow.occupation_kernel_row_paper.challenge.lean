namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationKernelRow
open MeasureTheory Set Real Filter
open scoped ENNReal
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeFractional
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's); section variables written as binders.
/-- Under HomogCovariance d alpha a Gamma mu, Gamma != 0 and D = (4 - alpha) - 2a (section standing assumptions): the nine conjuncts of occupation_kernel_row for Kstar a D. Gamma != 0 is not used. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OccupationKernelRow.occupation_kernel_row_paper {d : ℕ} {alpha a : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha a Γ μ) (_hΓ : Γ ≠ 0) (D : ℝ)
    (hD : D = (4 - alpha) - 2 * a) :
    (∀ u, Kstar a D (-u) = Kstar a D u) ∧
    (∀ u, u ≠ 0 → 0 < Kstar a D u) ∧
    LocallyIntegrable (Kstar a D) ∧
    StrictAntiOn (Kstar a D) (Ioi 0) ∧
    (∀ u, u ≠ 0 → Kstar a D u ≤ |u| ^ (-a)) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, IntervalIntegrable (fun t => Kstar a D (s - t)) volume 0 1) ∧
    IsGreatest (row a D '' Icc (0 : ℝ) 1) (Rstar a D) ∧
    IntervalIntegrable (Kstar a D) volume 0 (1 / 2) ∧
    0 < Rstar a D := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationKernelRow
