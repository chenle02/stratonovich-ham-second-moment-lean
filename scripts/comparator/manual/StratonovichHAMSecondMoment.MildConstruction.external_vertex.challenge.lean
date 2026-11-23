-- Printed type replaced by the source's statement in its scope (the printed type failed lean-pkg's round-trip check: the universe of the .{u} targets is dropped or the printed instance path differs).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildConstruction
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open WickInterface (widthFilter posOrthant)
open SourceInterface
open MildInterface
/-- With hD : PartialVertexTarget (item D): ExternalVertexTarget d: under H:homog, every source field, t > 0, n >= 1: I_(n,a)(t,x) -> X_n(t,x) in L^2 as a = (eps, delta) -> 0+ at arbitrary rates (E:external-vertex-limit, Step 5, TeX 2290-2303). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildConstruction.external_vertex (d : ℕ) (hD : PartialVertexTarget.{u} d) : ExternalVertexTarget.{u} d := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildConstruction
