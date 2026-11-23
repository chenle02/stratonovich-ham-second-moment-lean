-- Printed type replaced by the source's statement in its scope (CheckFidelity: the printed type's instance path differs from the claimed type's, e.g. Lp._proof_4 or the PiLp measurable space).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildConstruction
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open WickInterface (widthFilter posOrthant)
open SourceInterface
open MildInterface
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
/-- If every H X_n is in L^2, then for every N: H (sum_(n<N) X_n) is in L^2 and mulL2 H (sum_(n<N) X_n) = sum_(n<N) mulL2 H X_n. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildConstruction.mulL2_sum_range {H : Lp ℝ 2 P} {X : ℕ → Lp ℝ 2 P}
    (hX : ∀ n, MemLp (fun ω => H ω * X n ω) 2 P) (N : ℕ) :
    MemLp (fun ω => H ω * (∑ n ∈ Finset.range N, X n) ω) 2 P ∧
      mulL2 H (∑ n ∈ Finset.range N, X n) = ∑ n ∈ Finset.range N, mulL2 H (X n) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildConstruction.mulL2_sum_range)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildConstruction
