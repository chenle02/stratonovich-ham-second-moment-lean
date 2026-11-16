namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickComplete
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Filter Topology Finset
open scoped ComplexConjugate
open TerminalWick TerminalWickInputs FiniteWick HomogHypothesis
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
/-- For f in Lp C 2 P: int |f omega|^2 dP = |f|^2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWickComplete.integral_norm_sq_eq (f : Lp ℂ 2 P) : ∫ ω, ‖f ω‖ ^ 2 ∂P = ‖f‖ ^ 2 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickComplete
