-- Printed type replaced by the source's statement in its scope (the printed type failed lean-pkg's round-trip check: the universe of the .{u} targets is dropped or the printed instance path differs).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u v
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open TerminalWickRegularization (chainMeasureReg)
open WickInterface (kerA capSet widthFilter)
open LowAlphaConvolution (gammaEps specV)
open DiagramModel (Pi2 covEps coeffA)
open SourceInterface
open HomogeneousEnvelope (BK)
open LowAlphaUpper (C1 C2 Kgen kappa)
open TwoSimplexTime (Zc)
open D1Spatial (Ksp)
open HigherRieszTwo (riesz)
open WhiteModel (whiteCov)
/-- Unfolding: FieldMeasTarget d iff JointMeasTarget d and FieldContTarget d. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildInterface.fieldMeas_iff (d : ℕ) :
    FieldMeasTarget.{u} d ↔ JointMeasTarget.{u} d ∧ FieldContTarget.{u} d := by
  -- the statement mentions only copies; `FieldMeasTarget` is the conjunction by definition
  exact Iff.rfl
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface
