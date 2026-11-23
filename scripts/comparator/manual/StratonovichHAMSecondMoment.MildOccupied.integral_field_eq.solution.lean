-- Printed type replaced by the source's statement in its scope (the printed type failed lean-pkg's round-trip check: the universe of the .{u} targets is dropped or the printed instance path differs).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildOccupied
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Real Nat MatrixOrder
universe u v
open FiniteWick (CenteredGaussianField)
open TerminalWick (prodL2)
open TerminalWickInputs (fieldL2)
open MildInterface
variable {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ} {K : X → X → ℝ}
/-- The Fock law transfer: for a centered Gaussian field, points p and continuous Phi, int Phi(W(p_1),...,W(p_m)) dP = int Phi(sqrt(K_p) x) d stdPi m, K_p = (K(p_a,p_b))_(a,b), sqrt the CFC square root (law multivariateGaussian 0 K_p). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildOccupied.integral_field_eq {m : ℕ} (hW : CenteredGaussianField W K P) (p : Fin m → X)
    (Φ : (Fin m → ℝ) → ℝ) (hΦ : Continuous Φ) :
    ∫ ω, Φ (fun i => W (p i) ω) ∂P =
      ∫ x, Φ ((CFC.sqrt (Matrix.of fun a b => K (p a) (p b))).mulVec x)
        ∂GaussianIBP.stdPi m := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto20 _root_.StratonovichHAMSecondMoment.MildOccupied.integral_field_eq)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildOccupied
