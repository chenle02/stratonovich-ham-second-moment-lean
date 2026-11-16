namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
variable {ν : Measure (Rd d)}
/-- For an orthonormal family psi_1..psi_m in Lp C 2 nu, f in L^2(Lebesgue on R^d) and every eta: sum_i |conv nu psi_i f eta|^2 <= the lower integral of |f (eta - xi)|^2 against nu. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.sum_conv_le {m : ℕ} (ψ : Fin m → Lp ℂ 2 ν) (hψ : Orthonormal ℂ ψ)
    (f : Lp ℂ 2 (volume : Measure (Rd d))) (η : Rd d) :
    ∑ i, ‖conv ν (ψ i) f η‖ₑ ^ 2 ≤ ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.FockColumnBound.sum_conv_le
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
