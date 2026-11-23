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
/-- If every H F_k is in L^2, then for every N: H (sum_(k<N) F_k) is in L^2 and mulL2 H (sum_(k<N) F_k) = sum_(k<N) mulL2 H F_k. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildGreenWidth.mulL2_sum_range {H : Lp ℝ 2 P} {F : ℕ → Lp ℝ 2 P}
    (h : ∀ k, MemLp (fun ω => H ω * F k ω) 2 P) (N : ℕ) :
    MemLp (fun ω => H ω * (∑ k ∈ Finset.range N, F k) ω) 2 P ∧
      mulL2 H (∑ k ∈ Finset.range N, F k) = ∑ k ∈ Finset.range N, mulL2 H (F k) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildGreenWidth
