namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationKernelRow
open MeasureTheory Set Real Filter
open scoped ENNReal
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeFractional
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's); section variables written as binders.
/-- For 0 < a < 1, D > 0: Kstar a D is locally integrable on R (Lebesgue). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.OccupationKernelRow.Kstar_locallyIntegrable (a D : ℝ) (ha : 0 < a) (ha1 : a < 1) (hD : 0 < D) :
    LocallyIntegrable (Kstar a D) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.OccupationKernelRow
