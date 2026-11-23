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
/-- Any d: from MixedMoment d alpha0 Gamma P X v t (h), C, theta0 > 0, t > 0 and the diagram bound sum over Pi2 n n <= e^(2 theta0 t) C^n t^(2n)/n! at every eps > 0: E X_n^2 <= same (n >= 1) and E v^2 <= 2 e^(2 theta0 t + 2 C t^2) (TeX 2036-2053). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFinal.crude_moments_of_diagrams (h : MixedMoment d α₀ Γ P X v t) {C θ₀ : ℝ} (hC : 0 < C)
    (hθ₀ : 0 < θ₀) (ht : 0 < t)
    (hdiag : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, 1 ≤ n →
      ∑ D ∈ Pi2 n n, diagram (waveGreen d) (covEps Γ ε) α₀ n n D t ≤
        ENNReal.ofReal (Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / (n ! : ℝ))) :
    (∀ n : ℕ, 1 ≤ n → ∫ ω, X n ω ^ 2 ∂P ≤ Real.exp (2 * θ₀ * t) * C ^ n * t ^ (2 * n) / n !) ∧
      ∫ ω, v ω ^ 2 ∂P ≤ 2 * Real.exp (2 * θ₀ * t + 2 * C * t ^ 2) := by
  set_option smartUnfolding false in
  set_option linter.unusedSimpArgs false in
  (bridge_revert_all; bridge_auto19 _root_.StratonovichHAMSecondMoment.SourceFinal.crude_moments_of_diagrams)
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
