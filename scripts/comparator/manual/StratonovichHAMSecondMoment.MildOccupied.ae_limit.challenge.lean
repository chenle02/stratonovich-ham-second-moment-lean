-- Printed type replaced by the source's statement in its scope (CheckFidelity: the printed type's instance path differs from the claimed type's, e.g. Lp._proof_4 or the PiLp measurable space).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildOccupied
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Real Nat MatrixOrder
universe u v
open FiniteWick (CenteredGaussianField)
open TerminalWick (prodL2)
open TerminalWickInputs (fieldL2)
open MildInterface
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
/-- Identification of the limit (TeX 2199-2200), any measure P: if H_k -> H, F_k -> F and mulL2 H_k F_k -> G in L2, every H_k F_k in L2, then HF = G P-a.e. (a.s. convergent subsequences of all three). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildOccupied.ae_limit {Hk Fk : ℕ → Lp ℝ 2 P} {H F G : Lp ℝ 2 P} (hH : Tendsto Hk atTop (𝓝 H))
    (hF : Tendsto Fk atTop (𝓝 F)) (hm : ∀ k, MemLp (fun ω => Hk k ω * Fk k ω) 2 P)
    (hG : Tendsto (fun k => mulL2 (Hk k) (Fk k)) atTop (𝓝 G)) :
    (fun ω => H ω * F ω) =ᵐ[P] G := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildOccupied
