namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedSpectralGrowth
open MeasureTheory Real Metric
open scoped ENNReal NNReal Pointwise
open StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.HomogHypothesis StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SpectralHomog StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.GaussianTest
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's); section variables written as binders.
/-- For any measure mu on R^d, real c and t: charFun ((mu.map (c . )).withDensity gdens) t = integral over mu of cexp(I <xi, c t>) * exp(-(c^2 norm(xi)^2)). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MaskedSpectralGrowth.charFun_map_withDensity {d : ℕ} (μ : Measure (Rd d)) (c : ℝ) (t : Rd d) :
    charFun ((μ.map (fun ξ => c • ξ)).withDensity (fun ξ => (gdens ξ : ℝ≥0∞))) t =
      ∫ ξ, Complex.exp (Complex.I * (inner ℝ ξ (c • t) : ℝ)) *
        (Real.exp (-((c ^ 2) * ‖ξ‖ ^ 2)) : ℂ) ∂μ := by
  exact _root_.StratonovichHAMSecondMoment.MaskedSpectralGrowth.charFun_map_withDensity μ c t
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MaskedSpectralGrowth
