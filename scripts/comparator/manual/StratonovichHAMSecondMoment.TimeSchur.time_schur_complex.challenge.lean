namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeSchur
open MeasureTheory Set
open scoped ENNReal ComplexConjugate
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's); section variables written as binders.
/-- For 0 < a < 1, T > 0 and complex f in L^2(0,T): (t,s) -> f t * conj(f s) * |t-s|^(-a) is integrable on [0,T]^2 and |timeForm a T f f| <= 2 T^(1-a)/(1-a) * int_[0,T] |f|^2 (E:masked-time-schur after complexification, double-integral form). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TimeSchur.time_schur_complex {a T : ℝ} (_ha0 : 0 < a) (ha1 : a < 1) (hT : 0 < T)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Icc 0 T))) :
    Integrable (fun p : ℝ × ℝ => f p.1 * conj (f p.2) * ((kern a (p.1 - p.2) : ℝ) : ℂ))
        ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) ∧
      ‖timeForm a T f f‖ ≤ 2 * T ^ (1 - a) / (1 - a) * ∫ t in Icc 0 T, ‖f t‖ ^ 2 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeSchur
