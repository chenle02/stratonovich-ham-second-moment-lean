-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildPolyMem
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open SourceInterface
open MildInterface
variable {d : ℕ} {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {W : SrcPt d → Ω → ℝ}
/-- Given item A (hA : OccupiedMultTarget) and H:homog: for a field value W(z) and the partial sum U_N(t,x), W(z) U_N is in L2 with norm <= 2 sqrt(N+1) norm W(z) norm U_N (TeX 2189-2191, 2318-2320). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildPolyMem.occupied_partialSum (hA : OccupiedMultTarget.{u, 0}) {alpha : ℝ} {μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) (hW : SourceField α₀ Γ P W) (z : SrcPt d) (t : ℝ)
    (ht : 0 ≤ t) (x : Rd d) (N : ℕ) :
    MemLp (fun ω => fieldL2 hW z ω * (∑ n ∈ Finset.range (N + 1), XL2 hW t ht x n) ω) 2 P ∧
      ‖mulL2 (fieldL2 hW z) (∑ n ∈ Finset.range (N + 1), XL2 hW t ht x n)‖ ≤
        2 * Real.sqrt ((N : ℝ) + 1) * ‖fieldL2 hW z‖ *
          ‖∑ n ∈ Finset.range (N + 1), XL2 hW t ht x n‖ := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildPolyMem.occupied_partialSum)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildPolyMem
