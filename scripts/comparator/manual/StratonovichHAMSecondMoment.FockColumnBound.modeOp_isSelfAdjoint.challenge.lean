namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's (an instance path differs: `SeminormedAddCommGroup.toIsTopologicalAddGroup` for `Lp`'s, or `WithLp.measurableSpace`); CheckFidelity requires Expr equality).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ}
variable {ν : Measure (Rd d)}
/-- For finite even nu (nu.map neg = nu) and psi in Lp C 2 nu with |psi| = 1 and psi(-xi) = conj(psi xi) for nu-a.e. xi: modeOp psi is self-adjoint on L^2(Lebesgue on R^d). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.modeOp_isSelfAdjoint (hfin : IsFiniteMeasure ν) (hν : ν.map (fun x => -x) = ν)
    (ψ : Lp ℂ 2 ν) (hψ : ‖ψ‖ = 1) (hherm : ∀ᵐ ξ ∂ν, ψ (-ξ) = conj (ψ ξ)) :
    IsSelfAdjoint (modeOp hfin ψ hψ) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
