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
/-- Closedness of multiplication (TeX 2199-2201; the second clause of OccupiedMultTarget), any measure and any H in L2: if F_k -> F0 in L2, every H F_k in L2 and mulL2 H F_k -> G in L2, then H F0 is in L2 and mulL2 H F0 = G. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildOccupied.mul_closed (H : Lp ℝ 2 P) (F : ℕ → Lp ℝ 2 P) (F₀ G : Lp ℝ 2 P)
    (hm : ∀ k, MemLp (fun ω => H ω * F k ω) 2 P) (hF : Tendsto F atTop (𝓝 F₀))
    (hG : Tendsto (fun k => mulL2 H (F k)) atTop (𝓝 G)) :
    MemLp (fun ω => H ω * F₀ ω) 2 P ∧ mulL2 H F₀ = G := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildOccupied
