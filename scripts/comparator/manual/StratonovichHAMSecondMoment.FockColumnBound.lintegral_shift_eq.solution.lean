namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
variable {ν : Measure (Rd d)}
/-- For s-finite nu and f in L^2(Lebesgue on R^d): int int |f(eta - xi)|^2 nu(dxi) d eta = (int |f|^2) * nu(R^d) (lower integrals). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.lintegral_shift_eq [SFinite ν] (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    ∫⁻ η, ∫⁻ ξ, ‖f (η - ξ)‖ₑ ^ 2 ∂ν = (∫⁻ ζ, ‖f ζ‖ₑ ^ 2) * ν univ := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.FockColumnBound.lintegral_shift_eq
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
