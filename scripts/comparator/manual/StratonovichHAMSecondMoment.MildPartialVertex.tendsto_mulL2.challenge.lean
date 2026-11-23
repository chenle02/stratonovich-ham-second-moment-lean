-- Printed type replaced by the source's statement in its scope (CheckFidelity: the printed type's instance path differs from the claimed type's, e.g. Lp._proof_4 or the PiLp measurable space).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildPartialVertex
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open FiniteWick (CenteredGaussianField)
open TerminalWick (Pt prodL2)
open TerminalWickInputs (chainMeasure fieldL2)
open WickInterface (widthFilter)
open SourceInterface
open MildInterface
variable {X : Type*} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : X → Ω → ℝ}
  {K : X → X → ℝ}
variable {hW : CenteredGaussianField W K P} {n : ℕ}
  (hM : ∀ H ∈ LinG hW, ∀ F ∈ PolyLE hW n,
    MemLp (fun ω => H ω * F ω) 2 P ∧ ‖mulL2 H F‖ ≤ 2 * Real.sqrt ((n : ℝ) + 1) * ‖H‖ * ‖F‖)
include hM
/-- Given hM (H F in L^2, |HF| <= 2 sqrt(n+1) |H| |F| on LinG x P_(<=n)): if H_i -> H_0 in LinG and F_i -> F_0 in P_(<=n) in L^2 along any filter, then mulL2 H_i F_i -> mulL2 H_0 F_0. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.MildPartialVertex.tendsto_mulL2 {ι : Type*} {l : Filter ι} {H F : ι → Lp ℝ 2 P} {H₀ F₀ : Lp ℝ 2 P}
    (hH : ∀ i, H i ∈ LinG hW) (hF : ∀ i, F i ∈ PolyLE hW n) (hH₀ : H₀ ∈ LinG hW)
    (hF₀ : F₀ ∈ PolyLE hW n) (h1 : Tendsto H l (𝓝 H₀)) (h2 : Tendsto F l (𝓝 F₀)) :
    Tendsto (fun i => mulL2 (H i) (F i)) l (𝓝 (mulL2 H₀ F₀)) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.MildPartialVertex
