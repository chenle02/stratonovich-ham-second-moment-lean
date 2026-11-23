-- Printed type replaced by the source's statement in its scope (CheckFidelity: the printed type's instance path differs from the claimed type's, e.g. Lp._proof_4 or the PiLp measurable space).
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
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
/-- If the pointwise product F G is in L2, mulL2 F G = F G almost surely. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildInterface.coeFn_mulL2 {F G : Lp ℝ 2 P} (h : MemLp (fun ω => F ω * G ω) 2 P) :
    mulL2 F G =ᵐ[P] fun ω => F ω * G ω := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildInterface.coeFn_mulL2)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildInterface
