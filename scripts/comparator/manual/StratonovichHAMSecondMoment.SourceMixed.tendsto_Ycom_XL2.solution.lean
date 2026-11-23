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
/-- Hypothesis hX : FixedOrderL2Target d (item D, second clause only); H:homog, source field, t > 0, x, every n: Ycom n -> XL2 n (X_n) in L^2 as the common widths (eps, delta) -> (0+, 0+); n = 0 by Ycom_zero. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceMixed.tendsto_Ycom_XL2 (hX : FixedOrderL2Target.{u} d) (hH : HomogCovariance d alpha α₀ Γ μ)
    (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t) (x : Rd d) (n : ℕ) :
    Tendsto (Ycom hW t ht.le x n) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝 (XL2 hW t ht.le x n)) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceMixed.tendsto_Ycom_XL2)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceMixed
