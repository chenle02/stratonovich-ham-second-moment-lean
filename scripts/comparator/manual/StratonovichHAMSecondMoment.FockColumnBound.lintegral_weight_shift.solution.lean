namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ} {ν : Measure (Rd d)}
/-- For s-finite nu, f in Lp C 2 (Lebesgue on R^d), measurable W >= 0: int W(eta) int |f(eta - xi)|^2 nu(dxi) d eta = int |f(z)|^2 int W(z + xi) nu(dxi) dz (lower integrals). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.lintegral_weight_shift [SFinite ν] (f : Lp ℂ 2 (volume : Measure (Rd d)))
    (W : Rd d → ℝ≥0∞) (hW : Measurable W) :
    ∫⁻ η, W η * ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν =
      ∫⁻ ζ, ‖f ζ‖ₑ ^ 2 * ∫⁻ ξ, W (ζ + ξ) ∂ν := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.FockColumnBound.lintegral_weight_shift
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
