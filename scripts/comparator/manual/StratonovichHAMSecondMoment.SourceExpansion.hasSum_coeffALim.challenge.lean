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
/-- With hM, hX (items C, D) and H:homog, for every source field hW, t > 0, x: k -> (coeffALim d Gamma alpha0 k t).toReal has sum <u, u>_L2, i.e. E:full-second with A_k(t) = sum_(m <= 2k) sum_D J_(m,2k-m,D)(t) (TeX 844-847, 908-926). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceExpansion.hasSum_coeffALim (hM : TerminalMixedMomentTarget.{u} d) (hX : FixedOrderL2Target.{u} d)
    (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t)
    (x : Rd d) :
    HasSum (fun k => (coeffALim d Γ α₀ k t).toReal)
      (inner ℝ (uL2 hW t ht.le x) (uL2 hW t ht.le x)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceExpansion
