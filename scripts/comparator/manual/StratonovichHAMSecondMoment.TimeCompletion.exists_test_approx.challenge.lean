namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion
open MeasureTheory Set
open scoped ComplexConjugate ENNReal
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeSchur
-- Statement copied from the source (the printed type writes `ContDiff ℝ (↑⊤)` for the source's `(⊤ : ℕ∞)`).
/-- If T>0, f in L^2(0,T) and eps>0: there is g : R -> C smooth, compactly supported, tsupport g in Ioo 0 T, with eLpNorm (f - g) 2 on [0,T] <= eps. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TimeCompletion.exists_test_approx {T : ℝ} (hT : 0 < T) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc 0 T))) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧ tsupport g ⊆ Ioo 0 T ∧
      eLpNorm (f - g) 2 (volume.restrict (Icc 0 T)) ≤ ENNReal.ofReal ε := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion
