namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion
open MeasureTheory Set
open scoped ComplexConjugate ENNReal
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeSchur
-- Statement copied from the source (the printed type round-trips only up to definitional equality (`MeasureSpace.toMeasurableSpace` versus `Real.measurableSpace`)).
/-- If a<1, 0<=T and f, g in L^2(0,T): f(t) conj g(s) |t-s|^(-a) is integrable on [0,T]^2 (product measure). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TimeCompletion.cross_integrable {a T : ℝ} (ha1 : a < 1) (hT : 0 ≤ T) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Icc 0 T))) (hg : MemLp g 2 (volume.restrict (Icc 0 T))) :
    Integrable (fun p : ℝ × ℝ => f p.1 * conj (g p.2) * ((kern a (p.1 - p.2) : ℝ) : ℂ))
      ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.TimeCompletion.cross_integrable
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion
