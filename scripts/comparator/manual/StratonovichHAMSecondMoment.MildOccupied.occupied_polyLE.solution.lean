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
variable {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : X → Ω → ℝ} {K : X → X → ℝ}
/-- E:occupied-multiplication with F approximated (TeX 2197-2200): centered Gaussian field on a probability space, H in span (range (fieldL2 hW)), F in PolyLE hW n: HF in L2 and ||mulL2 H F|| <= 2 sqrt(n+1) ||H|| ||F||. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildOccupied.occupied_polyLE (hW : CenteredGaussianField W K P) (n : ℕ) {H F : Lp ℝ 2 P}
    (hH : H ∈ Submodule.span ℝ (Set.range (fieldL2 hW))) (hF : F ∈ PolyLE hW n) :
    MemLp (fun ω => H ω * F ω) 2 P ∧
      ‖mulL2 H F‖ ≤ 2 * Real.sqrt ((n : ℝ) + 1) * ‖H‖ * ‖F‖ := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildOccupied.occupied_polyLE)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildOccupied
