namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickComplete
-- Statement copied from the source (the printed type round-trips only up to definitional equality).
open MeasureTheory Set Filter Topology Finset
open scoped ComplexConjugate
open TerminalWick TerminalWickInputs FiniteWick HomogHypothesis
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
/-- For f in Lp R 2 P: toC f = (omega -> (f omega : C)) P-almost everywhere. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.TerminalWickComplete.coeFn_toC (f : Lp ℝ 2 P) : (toC f : Ω → ℂ) =ᵐ[P] fun ω => (f ω : ℂ) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.TerminalWickComplete
