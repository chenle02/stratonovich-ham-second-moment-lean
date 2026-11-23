-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
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
/-- With hA : OccupiedMultTarget (item A), hW a centered Gaussian field on a probability space: if sum X_n = U in L^2, every H X_n is in L^2 and sum mulL2 H X_n converges, then H U is in L^2 and sum mulL2 H X_n = mulL2 H U (Step 6, TeX 2318-2320). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildConstruction.hasSum_mulL2 (hA : OccupiedMultTarget.{u, 0}) {X₀ : Type} {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : X₀ → Ω → ℝ}
    {K : X₀ → X₀ → ℝ} (hW : CenteredGaussianField W K P) {H U : Lp ℝ 2 P} {X : ℕ → Lp ℝ 2 P}
    (hXU : HasSum X U) (hX : ∀ n, MemLp (fun ω => H ω * X n ω) 2 P)
    (hS : Summable fun n => mulL2 H (X n)) :
    MemLp (fun ω => H ω * U ω) 2 P ∧ HasSum (fun n => mulL2 H (X n)) (mulL2 H U) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildConstruction
