-- Printed type replaced by the source's statement in its scope (CheckFidelity: the printed type's instance path differs from the claimed type's, e.g. Lp._proof_4 or the PiLp measurable space).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildPartialVertex
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open WickInterface (widthFilter)
open SourceInterface
open MildInterface
variable {X : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ}
  {K : X → X → ℝ}
/-- For H, H', F in L^2(P) with H F and H' F in L^2: mulL2 (H - H') F = mulL2 H F - mulL2 H' F. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildPartialVertex.mulL2_sub_left {H H' F : Lp ℝ 2 P} (h1 : MemLp (fun ω => H ω * F ω) 2 P)
    (h2 : MemLp (fun ω => H' ω * F ω) 2 P) :
    mulL2 (H - H') F = mulL2 H F - mulL2 H' F := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildPartialVertex
