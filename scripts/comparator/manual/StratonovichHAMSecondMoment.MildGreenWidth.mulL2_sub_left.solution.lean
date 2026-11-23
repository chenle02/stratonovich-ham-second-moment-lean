-- Printed type replaced by the source's statement in its scope (CheckFidelity: the printed type's instance path differs from the claimed type's, e.g. Lp._proof_4 or the PiLp measurable space).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildGreenWidth
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u v
open HomogHypothesis (Rd HomogCovariance)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open TerminalWickRegularization (chainMeasureReg noiseMeasure regPt Noise)
open SourceInterface
open MildInterface
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
/-- If H1 F and H2 F are in L^2: mulL2 (H1 - H2) F = mulL2 H1 F - mulL2 H2 F. Auxiliary algebra of mulL2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildGreenWidth.mulL2_sub_left {H₁ H₂ F : Lp ℝ 2 P} (h₁ : MemLp (fun ω => H₁ ω * F ω) 2 P)
    (h₂ : MemLp (fun ω => H₂ ω * F ω) 2 P) :
    mulL2 (H₁ - H₂) F = mulL2 H₁ F - mulL2 H₂ F := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildGreenWidth.mulL2_sub_left)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildGreenWidth
