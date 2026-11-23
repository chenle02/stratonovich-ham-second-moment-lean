-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceExpansion
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 diagram covEps diagramLim coeffALim MixedMoment)
open SourceInterface
open SourceMixed
variable {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt d → Ω → ℝ}
/-- For every d, with hM : TerminalMixedMomentTarget d (item C) and hX : FixedOrderL2Target d (item D), discharged in SourceFinal: ExpansionL2Target d: for every source field, t > 0, x: sum_n ||X_n(t,x)|| < infinity and HasSum X_n u in L2 (E:expansion; TeX 542-549, 796, 911-920). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceExpansion.expansion_l2 (d : ℕ) (hM : TerminalMixedMomentTarget.{u} d)
    (hX : FixedOrderL2Target.{u} d) : ExpansionL2Target.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceExpansion.expansion_l2)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceExpansion
