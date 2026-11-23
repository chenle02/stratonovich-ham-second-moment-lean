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
/-- For every d, with hM, hX (items C, D), discharged in SourceFinal: MixedTermsTarget d: for every source field, t > 0, x: DiagramModel.MixedMoment d alpha0 Gamma P (srcX hW t x) (srcU hW t x) t; P:mixed whole (TeX 834-849, 851-927), the named input MixedMoment discharged. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceExpansion.mixed_terms (d : ℕ) (hM : TerminalMixedMomentTarget.{u} d)
    (hX : FixedOrderL2Target.{u} d) : MixedTermsTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceExpansion.mixed_terms)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceExpansion
