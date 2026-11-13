namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeSchur
open MeasureTheory Set
open scoped ENNReal ComplexConjugate
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's); section variables written as binders.
/-- For 0 < a < 1, T > 0 and real f in L^2(0,T) (MemLp f 2 on [0,T]): (t,s) -> f t * f s * |t-s|^(-a) is integrable on [0,T]^2 and int_[0,T] int_[0,T] f(t) f(s) |t-s|^(-a) <= 2 T^(1-a)/(1-a) * int_[0,T] f^2 (E:masked-time-schur, double-integral form). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TimeSchur.time_schur_paper {a T : ℝ} (_ha0 : 0 < a) (ha1 : a < 1) (hT : 0 < T)
    (f : ℝ → ℝ) (hf : MemLp f 2 (volume.restrict (Icc 0 T))) :
    Integrable (fun p : ℝ × ℝ => f p.1 * f p.2 * |p.1 - p.2| ^ (-a))
        ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) ∧
      ∫ t in Icc 0 T, ∫ s in Icc 0 T, f t * f s * |t - s| ^ (-a) ≤
        2 * T ^ (1 - a) / (1 - a) * ∫ t in Icc 0 T, f t ^ 2 := by
  exact _root_.StratonovichHAMSecondMoment.TimeSchur.time_schur_paper _ha0 ha1 hT f hf
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeSchur
