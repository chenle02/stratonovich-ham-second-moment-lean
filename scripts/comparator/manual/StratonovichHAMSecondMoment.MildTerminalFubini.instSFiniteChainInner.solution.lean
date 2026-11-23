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
/-- Instance: Leb^n x G_1^n (waveGreen d 1 on each of the n factors) on (Fin n -> R) x (Fin n -> R^d) is s-finite. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildTerminalFubini.instSFiniteChainInner (n : ℕ) :
    SFinite ((volume : Measure (Fin n → ℝ)).prod (Measure.pi fun _ : Fin n => waveGreen d 1)) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildTerminalFubini.instSFiniteChainInner)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildTerminalFubini
