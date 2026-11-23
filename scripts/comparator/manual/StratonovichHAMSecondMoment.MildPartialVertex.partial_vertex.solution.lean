-- Printed type replaced by the source's statement in its scope (the printed type failed lean-pkg's round-trip check: the universe of the .{u} targets is dropped or the printed instance path differs).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildPartialVertex
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open WickInterface (widthFilter)
open SourceInterface
open MildInterface
/-- Given hA (A), hB (B), hC (C), hF (terminal Fubini): PartialVertexTarget d: under H:homog some C, theta0 > 0 give, per source field, |X_n| <= q_n, E:fixed-external-domination, I_(n,a) exists, E:partial-vertex-limit, E:mixed-vertex-bound. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildPartialVertex.partial_vertex (d : ℕ) (hA : OccupiedMultTarget.{u, 0}) (hB : PolyMemTarget.{u} d)
    (hC : FieldMeasTarget.{u} d) (hF : TerminalFubiniTarget.{u} d) : PartialVertexTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildPartialVertex.partial_vertex)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildPartialVertex
