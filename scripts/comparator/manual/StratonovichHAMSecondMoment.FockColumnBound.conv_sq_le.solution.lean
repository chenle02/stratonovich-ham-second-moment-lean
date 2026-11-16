namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
variable {ν : Measure (Rd d)}
/-- For psi in Lp C 2 nu with |psi| = 1, f in L^2(Lebesgue on R^d) and eta: |conv nu psi f eta|^2 <= the lower integral of |f (eta - xi)|^2 against nu. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.conv_sq_le (ψ : Lp ℂ 2 ν) (hψ : ‖ψ‖ = 1) (f : Lp ℂ 2 (volume : Measure (Rd d)))
    (η : Rd d) : ‖conv ν ψ f η‖ₑ ^ 2 ≤ ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.FockColumnBound.conv_sq_le
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
