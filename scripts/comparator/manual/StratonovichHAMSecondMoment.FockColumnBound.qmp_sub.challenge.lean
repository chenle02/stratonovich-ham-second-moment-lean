namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
-- Statement copied from the source (the printed type is only definitionally equal to the declaration's (an instance path differs: `SeminormedAddCommGroup.toIsTopologicalAddGroup` for `Lp`'s, or `WithLp.measurableSpace`); CheckFidelity requires Expr equality).
open MeasureTheory Set Real Filter
open scoped ENNReal ComplexConjugate
open HomogHypothesis (Rd)
variable {d : ℕ} {ν : Measure (Rd d)}
/-- For s-finite nu on R^d: (eta, xi) -> eta - xi is quasi-measure-preserving from Lebesgue x nu to Lebesgue measure. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FockColumnBound.qmp_sub [SFinite ν] :
    QuasiMeasurePreserving (fun p : Rd d × Rd d => p.1 - p.2)
      ((volume : Measure (Rd d)).prod ν) volume := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FockColumnBound
