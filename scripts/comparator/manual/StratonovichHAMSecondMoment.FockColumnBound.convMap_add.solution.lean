namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type fails lean-pkg's round-trip check).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
variable {ν : Measure (Rd d)}
/-- For finite nu, psi in Lp C 2 nu and f, g in L^2(Lebesgue on R^d): conv nu psi (f + g) = conv nu psi f + conv nu psi g Lebesgue-a.e. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.convMap_add [IsFiniteMeasure ν] (ψ : Lp ℂ 2 ν) (f g : Lp ℂ 2 (volume : Measure (Rd d))) :
    conv ν ψ ⇑(f + g) =ᵐ[volume] conv ν ψ ⇑f + conv ν ψ ⇑g := by
  bridge_revert_all
  exact @_root_.StratonovichHAMSecondMoment.FockColumnBound.convMap_add
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
