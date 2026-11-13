namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.L8Completed
open MeasureTheory
-- Statement copied from the source (the printed type writes `MeasureTheory.MeasureSpace.volume` without its type, which does not elaborate).
/-- The supplied structure SymplecticFree.FreeWaveData d E is not vacuous: it has an instance on E = L2(R^d) with genuine translations (weakly null) and the trivial group S = 1, R = 1. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.L8Completed.freeWaveData_nonempty (d : ℕ) :
    Nonempty (SymplecticFree.FreeWaveData d
      (Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.L8Completed
