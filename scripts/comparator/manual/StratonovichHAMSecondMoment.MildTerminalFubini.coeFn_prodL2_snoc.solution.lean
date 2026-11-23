-- Printed type replaced by the source's statement in its scope (CheckFidelity: the printed type's instance path differs from the claimed type's, e.g. Lp._proof_4 or the PiLp measurable space).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildTerminalFubini
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2 chainWeightReal)
open TerminalWickInputs
open SourceInterface
open MildInterface
variable {d : ℕ}
variable {X : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ}
  {K : X → X → ℝ}
/-- For a centered Gaussian field W, z : Fin m -> X and p: prodL2 (snoc z p) = W(p) . prodL2 z almost surely (the last factor splits off the product of m+1 field values). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildTerminalFubini.coeFn_prodL2_snoc (hW : CenteredGaussianField W K P) {m : ℕ} (z : Fin m → X) (p : X) :
    (prodL2 hW (Fin.snoc z p : Fin (m + 1) → X) : Ω → ℝ) =ᵐ[P]
      fun ω => fieldL2 hW p ω * prodL2 hW z ω := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildTerminalFubini.coeFn_prodL2_snoc)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildTerminalFubini
