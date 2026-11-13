namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedModulation
open MeasureTheory Set
open scoped ComplexConjugate
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TimeSchur StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedTrigProducts
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's); section variables written as binders.
/-- If a<1, Phi measurable, = 0 outside [s,s+h], |Phi| <= M, h >= 0: (t,v) -> F t conj(F(t-v)) |v|^(-a), F = Phi e^(i omega .), is integrable on R^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MaskedModulation.shear_integrable {Φ : ℝ → ℂ} {s h M : ℝ} {a : ℝ} (ha1 : a < 1) (hΦm : Measurable Φ)
    (hΦ0 : ∀ u ∉ Icc s (s + h), Φ u = 0) (hΦb : ∀ u, ‖Φ u‖ ≤ M) (hh : 0 ≤ h) (ω : ℝ) :
    Integrable (fun p : ℝ × ℝ => Φ p.1 * phase ω p.1 * conj (Φ (p.1 - p.2) * phase ω (p.1 - p.2)) *
      ((kern a p.2 : ℝ) : ℂ)) (volume.prod volume) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedModulation
