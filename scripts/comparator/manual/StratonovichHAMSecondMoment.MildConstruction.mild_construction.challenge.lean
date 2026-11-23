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
/-- Frozen signature: with hA, hB, hC, hD, hX (items A-D and Step 5; hB, hC unused): MildConstructionTarget d (P:mild-construction, E:mild-construction, TeX 2151-2165, Steps 5-6 2290-2339); forwards to mild_construction_of. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildConstruction.mild_construction (d : ℕ) (hA : OccupiedMultTarget.{u, 0}) (_hB : PolyMemTarget.{u} d)
    (_hC : FieldMeasTarget.{u} d) (hD : PartialVertexTarget.{u} d)
    (hX : ExternalVertexTarget.{u} d) : MildConstructionTarget.{u} d := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildConstruction
