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
/-- Hypotheses hM (item C), hX (item D); H:homog, source field, t > 0, x, all m, n: srcX m * srcX n is integrable and E[srcX m srcX n] = sum over D in Pi2 m n of toReal diagramLim d Gamma alpha0 m n D t (second clause of MixedMoment; TeX 836-843). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceMixed.mixed_moment_srcX (hM : TerminalMixedMomentTarget.{u} d) (hX : FixedOrderL2Target.{u} d)
    (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W) {t : ℝ} (ht : 0 < t)
    (x : Rd d) (m n : ℕ) :
    Integrable (fun ω => srcX hW t ht.le x m ω * srcX hW t ht.le x n ω) P ∧
      ∫ ω, srcX hW t ht.le x m ω * srcX hW t ht.le x n ω ∂P =
        ∑ D ∈ Pi2 m n, (diagramLim d Γ α₀ m n D t).toReal := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceMixed.mixed_moment_srcX)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceMixed
