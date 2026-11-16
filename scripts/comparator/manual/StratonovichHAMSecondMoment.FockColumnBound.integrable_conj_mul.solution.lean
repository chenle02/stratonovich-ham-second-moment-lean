namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's (an instance path differs: `SeminormedAddCommGroup.toIsTopologicalAddGroup` for `Lp`'s, or `WithLp.measurableSpace`); CheckFidelity requires Expr equality).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
variable {ν : Measure (Rd d)}
/-- For psi in Lp C 2 nu and k with MemLp k 2 nu: xi -> conj(psi xi) * k xi is nu-integrable. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.integrable_conj_mul (ψ : Lp ℂ 2 ν) {k : Rd d → ℂ} (hk : MemLp k 2 ν) :
    Integrable (fun ξ => conj (ψ ξ) * k ξ) ν := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.FockColumnBound.integrable_conj_mul
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
