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
/-- Riesz case of P:d1-upper (TeX 5454-5466), d = 1, Gamma = c|y|^(-alpha) dy, 0 < alpha, alpha0 < 1, c > 0, t > 0, kept hypothesis hH (Riesz H:homog, not formalized): both E:d1-coefficient bounds (each eps; and for sum_m E[X_m X_(2k-m)]) and E srcU^2 <= exp(C_dir t^kappa). -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.SourceFinal.d1_upper_paper_l19 {c α α₀ t : ℝ} {μ : Measure (Rd 1)}
    (hH : HomogCovariance 1 α α₀ (volume.withDensity (riesz c α)) μ) (hα₀0 : 0 < α₀)
    (hα₀1 : α₀ < 1) (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) (ht : 0 < t) {Ω : Type u}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : SrcPt 1 → Ω → ℝ}
    (hW : SourceField α₀ (volume.withDensity (riesz c α)) P W) (x : Rd 1) :
    (∀ ε : ℝ, 0 < ε → ∀ k : ℕ, 1 ≤ k →
      coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! * (k : ℝ) ^ ((2 - α) * k))) ∧
      coeffA (waveGreen 1) (covEps (volume.withDensity (riesz c α)) ε) α₀ k t ≤
        ENNReal.ofReal ((2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! : ℝ) ^ (3 - α))) ∧
    (∀ k : ℕ, 1 ≤ k →
      ∑ m ∈ Finset.range (2 * k + 1),
          ∫ ω, srcX hW t ht.le x m ω * srcX hW t ht.le x (2 * k - m) ω ∂P ≤
        (2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) /
          (k ! * (k : ℝ) ^ ((2 - α) * k)) ∧
      (2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) / (k ! * (k : ℝ) ^ ((2 - α) * k)) ≤
        (2 * Zc α₀ * Ksp c α) ^ k * t ^ ((4 - α - α₀) * k) / (k ! : ℝ) ^ (3 - α)) ∧
    ∫ ω, srcU hW t ht.le x ω ^ 2 ∂P ≤ Real.exp ((3 - α) * (2 * Zc α₀ * Ksp c α) ^ (1 / (3 - α)) *
      t ^ ((4 - α - α₀) / (3 - α))) := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.SourceFinal
