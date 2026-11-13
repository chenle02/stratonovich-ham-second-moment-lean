namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedModulation
open MeasureTheory Set
open scoped ComplexConjugate
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeSchur StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's); section variables written as binders.
/-- If 0<a<1, h>0, 0<=s, s+h<=T, A continuous on I=[s,s+h], |A|<=M on I and |A x - A y| <= D|x-y| on I: for every real omega, F=1_I A e^(i omega t) has integrable integrand on [0,T]^2 and |timeForm a T F F| <= C0(a) h^(2-a) (M+hD)^2 <h omega>^(a-1). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MaskedModulation.modulation_bound {a T s h : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hh : 0 < h) (hs : 0 ≤ s)
    (hsT : s + h ≤ T) (A : ℝ → ℂ) (hcont : ContinuousOn A (Icc s (s + h))) (M D : ℝ)
    (hMb : ∀ u ∈ Icc s (s + h), ‖A u‖ ≤ M)
    (hDl : ∀ x ∈ Icc s (s + h), ∀ y ∈ Icc s (s + h), ‖A x - A y‖ ≤ D * |x - y|) (ω : ℝ) :
    Integrable (fun p : ℝ × ℝ => modeFn (Icc s (s + h)) A ω p.1 *
        conj (modeFn (Icc s (s + h)) A ω p.2) * ((kern a (p.1 - p.2) : ℝ) : ℂ))
        ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) ∧
      ‖timeForm a T (modeFn (Icc s (s + h)) A ω) (modeFn (Icc s (s + h)) A ω)‖ ≤
        C₀ a * h ^ (2 - a) * (M + h * D) ^ 2 * bracket (h * ω) ^ (a - 1) := by
  exact _root_.StratonovichHAMSecondMoment.MaskedModulation.modulation_bound ha0 ha1 hh hs hsT A hcont M D hMb hDl ω
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedModulation
