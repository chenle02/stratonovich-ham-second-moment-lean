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
/-- For every d, with hM, hX (items C, D), discharged in SourceFinal: FirstMomentSeriesTarget d: for every source field, t > 0, x: FirstMomentSeries P srcX srcU: X_0 = 1 pointwise, u integrable, E u = sum_n E X_n (TeX 796, 5856-5857); the named input discharged. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceExpansion.first_moment_series (d : ℕ) (hM : TerminalMixedMomentTarget.{u} d)
    (hX : FixedOrderL2Target.{u} d) : FirstMomentSeriesTarget.{u} d := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceExpansion
