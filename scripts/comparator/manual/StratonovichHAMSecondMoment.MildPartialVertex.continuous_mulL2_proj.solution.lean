-- Printed type replaced by the source's statement in its scope (CheckFidelity: the printed type's instance path differs from the claimed type's, e.g. Lp._proof_4 or the PiLp measurable space).
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
variable {X : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ}
  {K : X → X → ℝ}
variable {hW : CenteredGaussianField W K P} {n : ℕ}
  (hM : ∀ H ∈ LinG hW, ∀ F ∈ PolyLE hW n,
    MemLp (fun ω => H ω * F ω) 2 P ∧ ‖mulL2 H F‖ ≤ 2 * Real.sqrt ((n : ℝ) + 1) * ‖H‖ * ‖F‖)
include hM
/-- Given hM (as in tendsto_mulL2): (f, g) -> mulL2 (proj_LinG f) (proj_(P_(<=n)) g) is continuous on L^2(P) x L^2(P) (orthogonal projections). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildPartialVertex.continuous_mulL2_proj :
    Continuous fun q : Lp ℝ 2 P × Lp ℝ 2 P =>
      mulL2 ((LinG hW).starProjection q.1) ((PolyLE hW n).starProjection q.2) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildPartialVertex.continuous_mulL2_proj)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildPartialVertex
