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
/-- Hypothesis hM : TerminalMixedMomentTarget d (item C); H:homog, source field, t > 0, x, all m, n, common widths p = (eps, delta) > 0: <Ycom m p, Ycom n p> = sum over D in Pi2 m n of toReal wickF (waveGreen d) Gamma alpha0 (capDom delta) eps m D t t. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceMixed.inner_Ycom (hM : TerminalMixedMomentTarget.{u} d) (hH : HomogCovariance d alpha α₀ Γ μ)
    (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t) (x : Rd d) (m n : ℕ) {p : ℝ × ℝ}
    (hp : 0 < p.1 ∧ 0 < p.2) :
    inner ℝ (Ycom hW t ht.le x m p) (Ycom hW t ht.le x n p) =
      ∑ D ∈ Pi2 m n, (wickF (waveGreen d) Γ α₀ (capDom fun _ : Fin (m + n) => p.2)
        (fun _ => p.1) m D t t).toReal := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceMixed.inner_Ycom)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceMixed
