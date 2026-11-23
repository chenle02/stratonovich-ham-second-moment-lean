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
/-- Under H:homog (used for d in 1, 2, 3), source field, t >= 0, x: <X_0, X_0> = 1 in L^2 (X_0 = Y_0 = 1 a.s. by Ya_zero; the case m = n = 0, TeX 843). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceMixed.inner_XL2_zero (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W)
    {t : ℝ} (ht : 0 ≤ t) (x : Rd d) :
    inner ℝ (XL2 hW t ht x 0) (XL2 hW t ht x 0) = 1 := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceMixed.inner_XL2_zero)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceMixed
