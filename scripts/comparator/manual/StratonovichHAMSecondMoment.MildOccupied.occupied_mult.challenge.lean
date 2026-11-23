-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildOccupied
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Real Nat MatrixOrder
universe u v
open FiniteWick (CenteredGaussianField)
open TerminalWick (prodL2)
open TerminalWickInputs (fieldL2)
open MildInterface
/-- L20-A headline, no hypothesis: OccupiedMultTarget. For every centered Gaussian field on a probability space, H in LinG, F in PolyLE n: HF in L2, ||HF|| <= 2 sqrt(n+1) ||H|| ||F|| (TeX 2189-2191); and F_k -> F0, H F_k in L2, H F_k -> G imply H F0 in L2, = G (2199-2201). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildOccupied.occupied_mult : OccupiedMultTarget.{u, v} := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildOccupied
