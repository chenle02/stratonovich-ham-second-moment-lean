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
/-- The integrability half of the transfer: for a centered Gaussian field and continuous Phi, if x -> Phi(sqrt(K_p) x) is stdPi m-integrable, then omega -> Phi(W(p_1) omega, ..., W(p_m) omega) is P-integrable. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildOccupied.integrable_field_of {m : ℕ} (hW : CenteredGaussianField W K P) (p : Fin m → X)
    (Φ : (Fin m → ℝ) → ℝ) (hΦ : Continuous Φ)
    (h : Integrable (fun x => Φ ((CFC.sqrt (Matrix.of fun a b => K (p a) (p b))).mulVec x))
      (GaussianIBP.stdPi m)) :
    Integrable (fun ω => Φ (fun i => W (p i) ω)) P := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildOccupied
