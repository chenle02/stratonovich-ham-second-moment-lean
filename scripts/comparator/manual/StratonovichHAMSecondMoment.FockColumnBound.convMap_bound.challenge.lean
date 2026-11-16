namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
variable {ν : Measure (Rd d)}
/-- For finite nu, psi in Lp C 2 nu with |psi| = 1 and f in L^2(Lebesgue on R^d): int |conv nu psi f|^2 <= nu(R^d) * int |f|^2 (lower integrals). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.convMap_bound [IsFiniteMeasure ν] (ψ : Lp ℂ 2 ν) (hψ : ‖ψ‖ = 1)
    (f : Lp ℂ 2 (volume : Measure (Rd d))) :
    ∫⁻ η, ‖conv ν ψ f η‖ₑ ^ 2 ≤ ν univ * ∫⁻ ζ, ‖f ζ‖ₑ ^ 2 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
