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
/-- For every d, nothing supplied: FixedOrderL2Target d: under H:homog, n >= 1, t > 0: Y_n at vertexwise widths converges in L^2 along widthFilter x widthFilter to stratInt = the common-width limit S_n(g_n) (TeX 1858-1860, Step 4 1949-1965). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFinal.fixed_order_l2_l19 (d : ℕ) : FixedOrderL2Target.{u} d := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
