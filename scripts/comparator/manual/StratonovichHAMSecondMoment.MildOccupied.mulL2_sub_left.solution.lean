-- Printed type replaced by the source's statement in its scope (CheckFidelity: the printed type's instance path differs from the claimed type's, e.g. Lp._proof_4 or the PiLp measurable space).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildOccupied
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Real Nat MatrixOrder
universe u v
open FiniteWick (CenteredGaussianField)
open TerminalWick (prodL2)
open TerminalWickInputs (fieldL2)
open MildInterface
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
/-- If HF and H'F are in L2, then mulL2 (H - H') F = mulL2 H F - mulL2 H' F. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildOccupied.mulL2_sub_left {H H' F : Lp ℝ 2 P} (h₁ : MemLp (fun ω => H ω * F ω) 2 P)
    (h₂ : MemLp (fun ω => H' ω * F ω) 2 P) :
    mulL2 (H - H') F = mulL2 H F - mulL2 H' F := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildOccupied.mulL2_sub_left)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildOccupied
