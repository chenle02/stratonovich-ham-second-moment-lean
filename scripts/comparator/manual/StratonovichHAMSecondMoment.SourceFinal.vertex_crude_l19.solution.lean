-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 diagram covEps diagramLim coeffA coeffALim MixedMoment)
open SourceInterface
open HomogeneousEnvelope (BK termBK)
open LowAlphaUpper (FirstMomentSeries C1 C2 Kgen)
open LowAlphaConvolution (specV)
open TwoSimplexTime (Zc)
open D1Spatial (Ksp)
open HigherRieszTwo (riesz)
/-- For every d, nothing supplied: VertexCrudeTarget d: under H:homog some C, theta0 > 0 give ||Y_n^a|| <= q_n(t) (n >= 1, all positive widths), ||X_n|| <= q_n(t) (n >= 0) and sum_n sqrt(n+1) q_n(T) < infinity (TeX 2062-2074). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFinal.vertex_crude_l19 (d : ℕ) : VertexCrudeTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceFinal.vertex_crude_l19)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
