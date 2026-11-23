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
variable {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} {Ω : Type u} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt d → Ω → ℝ}
/-- With hA (item A), H:homog (hH), C > 0 and hD2 (D's E:fixed-external-domination): for every width a and p, W_a(p) u(p) is in L^2 and sum_n mulL2 W_a(p) X_n(p) = mulL2 W_a(p) u(p) (Step 6, TeX 2310-2320). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildConstruction.prod_hasSum (hA : OccupiedMultTarget.{u, 0}) (hH : HomogCovariance d alpha α₀ Γ μ)
    (hW : SourceField α₀ Γ P W) {C θ₀ : ℝ} (hC : 0 < C)
    (hD2 : ∀ (a : PosW) (n : ℕ), 1 ≤ n → ∀ (T s : ℝ), 0 ≤ s → s ≤ T → ∀ y : Rd d,
      MemLp (fun ω => Wa hW a (s, y) ω * Xf hW (n - 1) (s, y) ω) 2 P ∧
        ‖mulL2 (Wa hW a (s, y)) (Xf hW (n - 1) (s, y))‖ ≤
          2 * Real.sqrt n * Real.sqrt (Va α₀ Γ a) * qn C θ₀ (n - 1) T)
    (a : PosW) (p : ℝ × Rd d) :
    MemLp (fun ω => Wa hW a p ω * uf hW p ω) 2 P ∧
      HasSum (fun n => mulL2 (Wa hW a p) (Xf hW n p)) (mulL2 (Wa hW a p) (uf hW p)) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildConstruction.prod_hasSum)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildConstruction
