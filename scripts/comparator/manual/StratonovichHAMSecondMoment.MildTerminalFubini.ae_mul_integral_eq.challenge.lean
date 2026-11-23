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
/-- For a finite measure P, H in L^2(P) and F, G : Z -> L^2(P) Bochner integrable for nu with G z = H . F z P-a.e. for every z: H . int F dnu = int G dnu P-a.e. (tested against 1_A 1_(|H|<=N) H and 1_A 1_(|H|<=N)). (Context: the terminal-kernel Fubini, TeX 2257-2260.) -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildTerminalFubini.ae_mul_integral_eq (H : Lp ℝ 2 P) {F G : Z → Lp ℝ 2 P} (hF : Integrable F ν)
    (hG : Integrable G ν) (hFG : ∀ z, (G z : Ω → ℝ) =ᵐ[P] fun ω => H ω * F z ω) :
    (fun ω => H ω * (∫ z, F z ∂ν : Lp ℝ 2 P) ω) =ᵐ[P] (∫ z, G z ∂ν : Lp ℝ 2 P) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildTerminalFubini
