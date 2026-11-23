-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFixedOrder
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open WickInterface (capDom wickF widthFilter posOrthant)
open DiagramModel (Pi2 rev)
open SourceInterface
variable {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
/-- Hypothesis hM : TerminalMixedMomentTarget d (item C); under H:homog, source field hW, t > 0, x, n >= 1: the L^2 norm of Yw(eps^a,delta^a) - Yw(eps^b,delta^b) tends to 0 as all 4n widths -> 0 jointly (TeX 1956-1959). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFixedOrder.tendsto_norm_sub (hM : TerminalMixedMomentTarget.{u} d)
    (hH : HomogCovariance d alpha α₀ Γ μ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : SrcPt d → Ω → ℝ) (hW : SourceField α₀ Γ P W) {t : ℝ}
    (ht : 0 < t) (x : Rd d) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun pq : ((Fin n → ℝ) × (Fin n → ℝ)) × ((Fin n → ℝ) × (Fin n → ℝ)) =>
        ‖Yw hW t ht.le x pq.1.1 pq.1.2 - Yw hW t ht.le x pq.2.1 pq.2.2‖)
      ((widthFilter n ×ˢ widthFilter n) ×ˢ (widthFilter n ×ˢ widthFilter n)) (𝓝 0) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceFixedOrder.tendsto_norm_sub)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFixedOrder
