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
/-- For every d, hypothesis hM : TerminalMixedMomentTarget d (item C): FixedOrderL2Target d: under H:homog, source field, t > 0, x, n >= 1: Yw -> stratInt (S_n(g_n)) in L^2 along widthFilter n x widthFilter n, and Ycom -> stratInt at common widths (TeX 1858-1860, 1949-1965). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFixedOrder.fixed_order_l2 (d : ℕ) (hM : TerminalMixedMomentTarget.{u} d) :
    FixedOrderL2Target.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceFixedOrder.fixed_order_l2)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFixedOrder
