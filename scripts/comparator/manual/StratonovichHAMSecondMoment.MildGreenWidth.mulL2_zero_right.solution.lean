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
/-- For H in L^2(P): the pointwise product H * 0 is in L^2 and mulL2 H 0 = 0. Auxiliary algebra of mulL2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildGreenWidth.mulL2_zero_right (H : Lp ℝ 2 P) :
    MemLp (fun ω => H ω * (0 : Lp ℝ 2 P) ω) 2 P ∧ mulL2 H (0 : Lp ℝ 2 P) = 0 := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildGreenWidth.mulL2_zero_right)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildGreenWidth
