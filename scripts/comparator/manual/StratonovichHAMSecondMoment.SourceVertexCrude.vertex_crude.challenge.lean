-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceVertexCrude
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 rev)
open TerminalWick (Pt prodL2)
open PairingInterface
open PairingBridge (smoothEdge)
open WickInterface
open SourceInterface
open HomogeneousEnvelope (Khom Khom_pos one_le_Khom)
universe u
variable {d : ℕ}
/-- For every d, with hM : TerminalMixedMomentTarget d (item C) and hX : FixedOrderL2Target d (item D), discharged in SourceFinal: VertexCrudeTarget d: ||Y_n^a(t,x)|| <= q_n(t) (n >= 1), ||X_n(t,x)|| <= q_n(t) (n >= 0), E:vertex-summability for every real T (TeX 2062-2074). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceVertexCrude.vertex_crude (d : ℕ) (hM : TerminalMixedMomentTarget.{u} d)
    (hX : FixedOrderL2Target.{u} d) : VertexCrudeTarget.{u} d := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceVertexCrude
