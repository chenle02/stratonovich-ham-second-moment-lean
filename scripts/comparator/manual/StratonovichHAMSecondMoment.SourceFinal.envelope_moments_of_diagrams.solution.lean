-- Printed type replaced by the source's statement in its scope (the printed type drops the universe of the .{u} targets, so it does not elaborate to the claimed type).
namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal Real Nat
universe u
open HomogHypothesis (Rd HomogCovariance)
open WaveGreen (waveGreen)
open DiagramModel (Pi2 diagram covEps diagramLim coeffA coeffALim MixedMoment)
open SourceInterface
open HomogeneousEnvelope (BK termBK)
open LowAlphaUpper (FirstMomentSeries C1 C2 Kgen)
open LowAlphaConvolution (specV)
open TwoSimplexTime (Zc)
open D1Spatial (Ksp)
open HigherRieszTwo (riesz)
variable {d : ℕ} {α₀ : ℝ} {Γ : Measure (Rd d)} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
  {X : ℕ → Ω → ℝ} {v : Ω → ℝ} {t : ℝ}
/-- Any d: from MixedMoment (h), K > 0, beta > 2, t > 0 and sum over Pi2 m n <= #Pi2 m n K^k e^(2 theta t) theta^(-beta k) at every eps: the same bound for E[X_m X_n] (m + n = 2k >= 2, theta > 0) and E v^2 <= BK K beta t. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFinal.envelope_moments_of_diagrams (h : MixedMoment d α₀ Γ P X v t) {K β : ℝ} (hK : 0 < K)
    (hβ : 2 < β) (ht : 0 < t)
    (hdiag : ∀ ε : ℝ, 0 < ε → ∀ (m n k : ℕ), m + n = 2 * k → 1 ≤ k → ∀ θ : ℝ, 0 < θ →
      ∑ D ∈ Pi2 m n, diagram (waveGreen d) (covEps Γ ε) α₀ m n D t ≤
        ENNReal.ofReal ((Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) * θ ^ (-(β * k)))) :
    (∀ m n k : ℕ, m + n = 2 * k → 1 ≤ k → ∀ θ : ℝ, 0 < θ →
      ∫ ω, X m ω * X n ω ∂P ≤ (Pi2 m n).card * K ^ k * Real.exp (2 * θ * t) *
        θ ^ (-(β * k))) ∧
      ∫ ω, v ω ^ 2 ∂P ≤ BK K β t := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceFinal.envelope_moments_of_diagrams)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
