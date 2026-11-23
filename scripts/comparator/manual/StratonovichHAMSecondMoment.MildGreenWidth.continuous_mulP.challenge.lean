-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
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
variable {X : Type v} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ}
  {K : X → X → ℝ}
/-- With hA : OccupiedMultTarget (item A), P a probability measure, hW a centered Gaussian field and n: (H, F) -> mulP hW n H F is continuous on L^2 x L^2 (E:occupied-multiplication on the two increments, Step 4, TeX 2271-2277). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildGreenWidth.continuous_mulP (hA : OccupiedMultTarget.{u, v}) [IsProbabilityMeasure P]
    (hW : CenteredGaussianField W K P) (n : ℕ) :
    Continuous fun q : Lp ℝ 2 P × Lp ℝ 2 P => mulP hW n q.1 q.2 := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildGreenWidth
