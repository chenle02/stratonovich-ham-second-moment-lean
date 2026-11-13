namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationKernelRow
open MeasureTheory Set Real Filter
open scoped ENNReal
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeFractional
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's); section variables written as binders.
/-- For 0 < a < 1, D > 0: Kstar even; positive off 0; locally integrable; StrictAntiOn on Ioi 0; <= |u|^(-a) off 0; each row t -> Kstar(s-t), s in [0,1], interval integrable on [0,1]; Rstar = IsGreatest of row on [0,1]; Kstar integrable on [0,1/2]; 0 < Rstar. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OccupationKernelRow.occupation_kernel_row (a D : ℝ) (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D) :
    (∀ u, Kstar a D (-u) = Kstar a D u) ∧
    (∀ u, u ≠ 0 → 0 < Kstar a D u) ∧
    LocallyIntegrable (Kstar a D) ∧
    StrictAntiOn (Kstar a D) (Ioi 0) ∧
    (∀ u, u ≠ 0 → Kstar a D u ≤ |u| ^ (-a)) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, IntervalIntegrable (fun t => Kstar a D (s - t)) volume 0 1) ∧
    IsGreatest (row a D '' Icc (0 : ℝ) 1) (Rstar a D) ∧
    IntervalIntegrable (Kstar a D) volume 0 (1 / 2) ∧
    0 < Rstar a D := by
  exact _root_.StratonovichHAMSecondMoment.OccupationKernelRow.occupation_kernel_row a D ha ha1 hD
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationKernelRow
