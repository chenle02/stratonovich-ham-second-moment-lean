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
/-- MildConstructionTarget at Type (hypothesis h) implies MildConstructionM9 d: the mild-equation limit at the constructed M9 model. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildInterface.mildConstructionM9_of {d : ℕ} (h : MildConstructionTarget.{0} d) :
    MildConstructionM9 d := by
  -- the statement mentions only copies; proved in the copies as in the source
  exact fun hH t ht x =>
    (h hH (m9 (SourceFinal.source_field_l19 d) hH).P (m9 (SourceFinal.source_field_l19 d) hH).W
      (m9 (SourceFinal.source_field_l19 d) hH).field t ht x).2.2
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface
