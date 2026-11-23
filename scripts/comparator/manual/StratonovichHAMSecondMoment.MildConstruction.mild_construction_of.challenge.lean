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
/-- With hA (item A), hD (item D), hX : ExternalVertexTarget: MildConstructionTarget d: under H:homog, t > 0: W_a u in L^2 pointwise, mild-integrable, I_a(t,x) -> u(t,x) - 1 in L^2 as eps, delta -> 0+ at arbitrary rates (E:mild-construction, TeX 2151-2165). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildConstruction.mild_construction_of (d : ℕ) (hA : OccupiedMultTarget.{u, 0})
    (hD : PartialVertexTarget.{u} d) (hX : ExternalVertexTarget.{u} d) :
    MildConstructionTarget.{u} d := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildConstruction
