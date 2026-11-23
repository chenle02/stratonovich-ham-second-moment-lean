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
/-- Under H:homog, source field, t >= 0, x, all m, n: the P-integral of srcX m * srcX n equals the L^2 inner product <XL2 m, XL2 n>. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceMixed.integral_srcX_mul (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W)
    {t : ℝ} (ht : 0 ≤ t) (x : Rd d) (m n : ℕ) :
    ∫ ω, srcX hW t ht x m ω * srcX hW t ht x n ω ∂P =
      inner ℝ (XL2 hW t ht x m) (XL2 hW t ht x n) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceMixed.integral_srcX_mul)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceMixed
