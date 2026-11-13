namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion
open MeasureTheory Set
open scoped ComplexConjugate ENNReal
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeSchur
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
-- The section variables used, written as binders: {p : TimeParams}.
/-- For real g with MemLp g 2 on [0,T]: ||emb p (g as complex)||^2 = int_[0,T] int_[0,T] g(t) g(s) |t-s|^(-a) ds dt. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TimeCompletion.emb_norm_sq_real {p : TimeParams} (g : ℝ → ℝ) (hg : MemLp g 2 (volume.restrict (Icc (0 : ℝ) p.T))) :
    ‖emb p ⟨fun t => (g t : ℂ), hg.ofReal⟩‖ ^ 2 =
      ∫ t in Icc 0 p.T, ∫ s in Icc 0 p.T, g t * g s * |t - s| ^ (-p.a) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeCompletion
