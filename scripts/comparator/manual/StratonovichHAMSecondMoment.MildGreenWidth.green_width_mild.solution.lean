-- Printed type replaced by the source's statement in its scope (the printed type failed lean-pkg's round-trip check: the universe of the .{u} targets is dropped or the printed instance path differs).
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
/-- With hA, hB, hC, hD (items A-D): GreenWidthMildTarget d: under H:homog, t > 0, width a: for n >= 1, W_a X_(n-1) is L^2-continuous in y, mildMeasureReg-integrable, its p_eta*G integrals -> I_(n,a)(t,x) as eta -> 0+; same for W_a u, I_a (TeX 2268-2287). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildGreenWidth.green_width_mild (d : ℕ) (hA : OccupiedMultTarget.{u, 0}) (hB : PolyMemTarget.{u} d)
    (hC : FieldMeasTarget.{u} d) (hD : PartialVertexTarget.{u} d) :
    GreenWidthMildTarget.{u} d := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildGreenWidth.green_width_mild)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildGreenWidth
