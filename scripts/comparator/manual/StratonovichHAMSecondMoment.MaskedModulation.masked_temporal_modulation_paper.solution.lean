namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedModulation
open MeasureTheory Set
open scoped ComplexConjugate
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeSchur StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's); section variables written as binders.
/-- With 0<a<1, T>0, 0<h<=1, 0<=s, s+h<=T, A C^1 on I=[s,s+h], M=sup_I|A|, D=sup_I|A'|, real omega: F=1_I A e^(i omega t) gives an integrable integrand on [0,T]^2 and |timeForm a T F F| <= C0(a) h^(2-a) (M+hD)^2 <h omega>^(a-1). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MaskedModulation.masked_temporal_modulation_paper (a T s h : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (_hT : 0 < T)
    (hh0 : 0 < h) (_hh1 : h ≤ 1) (hs : 0 ≤ s) (hsT : s + h ≤ T)
    (A : ℝ → ℂ) (hA : ContDiffOn ℝ 1 A (Icc s (s + h)))
    (M D : ℝ)
    (hM : M = sSup ((fun t => ‖A t‖) '' Icc s (s + h)))
    (hD : D = sSup ((fun t => ‖derivWithin A (Icc s (s + h)) t‖) '' Icc s (s + h)))
    (ω : ℝ) :
    Integrable (fun p : ℝ × ℝ => modeFn (Icc s (s + h)) A ω p.1 *
        conj (modeFn (Icc s (s + h)) A ω p.2) * ((kern a (p.1 - p.2) : ℝ) : ℂ))
        ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) ∧
      ‖timeForm a T (modeFn (Icc s (s + h)) A ω) (modeFn (Icc s (s + h)) A ω)‖ ≤
        C₀ a * h ^ (2 - a) * (M + h * D) ^ 2 * bracket (h * ω) ^ (a - 1) := by
  exact _root_.StratonovichHAMSecondMoment.MaskedModulation.masked_temporal_modulation_paper a T s h ha0 ha1 _hT hh0 _hh1 hs hsT A hA M D hM hD ω
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedModulation
