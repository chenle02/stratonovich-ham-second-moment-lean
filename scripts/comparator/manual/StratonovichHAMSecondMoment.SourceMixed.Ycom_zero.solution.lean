-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceMixed
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open WickInterface (capDom wickF widthFilter posOrthant)
open DiagramModel (Pi2 diagram covEps diagramLim)
open SourceInterface
variable {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt d → Ω → ℝ}
omit [IsProbabilityMeasure P] in
/-- For a source field (no H:homog), t >= 0, x and every width pair p: Ycom hW t x 0 p = XL2 hW t x 0 (one width vector on Fin 0; the zero-order factor, TeX 881). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceMixed.Ycom_zero (hW : SourceField α₀ Γ P W) (t : ℝ) (ht : 0 ≤ t) (x : Rd d) (p : ℝ × ℝ) :
    Ycom hW t ht x 0 p = XL2 hW t ht x 0 := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceMixed.Ycom_zero)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceMixed
