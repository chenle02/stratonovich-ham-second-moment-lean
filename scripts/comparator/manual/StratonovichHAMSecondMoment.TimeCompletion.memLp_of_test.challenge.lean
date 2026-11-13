namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion
open MeasureTheory Set
open scoped ComplexConjugate ENNReal
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeSchur
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `(⊤ : ℕ∞)`).
/-- If f : R -> R is smooth with compact support: MemLp f 2 on [0,T], for every T. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TimeCompletion.memLp_of_test (T : ℝ) (f : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) : MemLp f 2 (volume.restrict (Icc 0 T)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion
