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
/-- With hM (item C), hX (item D), H:homog, C, theta0 > 0 and the crude-corrected diagram bound hdiag: for every source field hW, t > 0, x and n: ||X_n(t,x)||_L2 <= e^(theta0 t) sqrt((C t^2)^n/n!) (n = 0: ||X_0|| = 1; TeX 911-913). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceExpansion.norm_XL2_le (hM : TerminalMixedMomentTarget.{u} d) (hX : FixedOrderL2Target.{u} d)
    (hH : HomogCovariance d alpha α₀ Γ μ) {C θ₀ : ℝ} (hC : 0 < C) (hθ₀ : 0 < θ₀)
    (hdiag : ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (t : ℝ), 1 ≤ n → 0 < t →
      ∑ D ∈ Pi2 n n, diagram (waveGreen d) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal (Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / (n ! : ℝ)))
    (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t) (x : Rd d) (n : ℕ) :
    ‖XL2 hW t ht.le x n‖ ≤ Real.exp (θ₀ * t) * Real.sqrt ((C * t ^ 2) ^ n / n !) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceExpansion.norm_XL2_le)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceExpansion
