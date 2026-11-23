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
/-- Given hM (as in tendsto_mulL2): if f, g : alpha -> L^2(P) are strongly measurable with values in LinG and P_(<=n), then a -> mulL2 (f a) (g a) is strongly measurable. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildPartialVertex.stronglyMeasurable_mulL2 {α : Type*} [MeasurableSpace α] {f g : α → Lp ℝ 2 P}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) (hf' : ∀ a, f a ∈ LinG hW)
    (hg' : ∀ a, g a ∈ PolyLE hW n) : StronglyMeasurable fun a => mulL2 (f a) (g a) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildPartialVertex.stronglyMeasurable_mulL2)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildPartialVertex
