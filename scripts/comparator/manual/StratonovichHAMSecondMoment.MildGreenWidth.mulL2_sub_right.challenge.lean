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
/-- If H F1 and H F2 are in L^2: mulL2 H (F1 - F2) = mulL2 H F1 - mulL2 H F2. Auxiliary algebra of mulL2. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildGreenWidth.mulL2_sub_right {H F₁ F₂ : Lp ℝ 2 P} (h₁ : MemLp (fun ω => H ω * F₁ ω) 2 P)
    (h₂ : MemLp (fun ω => H ω * F₂ ω) 2 P) :
    mulL2 H (F₁ - F₂) = mulL2 H F₁ - mulL2 H F₂ := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildGreenWidth
