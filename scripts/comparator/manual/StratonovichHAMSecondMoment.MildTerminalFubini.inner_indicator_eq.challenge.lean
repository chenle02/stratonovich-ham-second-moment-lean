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
variable {Z : Type*} [MeasurableSpace Z] {ν : Measure Z} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsFiniteMeasure P]
omit [IsFiniteMeasure P] in
/-- For H : Omega -> R, measurable S with 1_S H in L^2(P) and f in L^2(P): <(1_S H) as L^2 class, f> = int_S H f dP. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildTerminalFubini.inner_indicator_eq (H : Ω → ℝ) {S : Set Ω} (hS : MeasurableSet S)
    (hφ : MemLp (S.indicator H) 2 P) (f : Lp ℝ 2 P) :
    inner ℝ (hφ.toLp _) f = ∫ ω in S, H ω * f ω ∂P := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildTerminalFubini
