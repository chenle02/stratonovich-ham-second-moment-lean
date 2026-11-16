namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplitCore
open Finset Real MeasureTheory
open scoped Nat
open StratonovichHAMSecondMoment.IntervalScalar
-- Statement copied from the source (the printed type elaborates `0` through `MulZeroClass.toZero`, the declaration through `AddZero.toZero`).
/-- Under H:homog, R = R_alpha > 0, k >= 1, T > 0, V >= 0, delta > 0, h i, sigma i > 0: if every split has |Q p| <= k^2 Mk k^2 V prod beforeFactor (lam = k/T), then every split has |Q p| <= k^2 splitConst delta ^ k R^k V prod splitFactor. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FixedSplitCore.split_explicit_constant_paper {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    {R T δ V : ℝ} {M k : ℕ} (h σ : Fin M → ℝ) (Q : (Fin M → ℕ × ℕ) → ℝ)
    (_hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hRpos : 0 < R) (hk : 1 ≤ k) (hT : 0 < T) (hV : 0 ≤ V) (hδ : 0 < δ)
    (hh : ∀ i, 0 < h i) (hσpos : ∀ i, 0 < σ i)
    (hbefore : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ (k : ℝ) ^ 2 * Mk k ^ 2 * V *
          ∏ i, beforeFactor alpha δ R (σ i) (h i) (k / T) (κ i) (p i)) :
    ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ (k : ℝ) ^ 2 * splitConst δ ^ k * R ^ k * V *
          ∏ i, splitFactor alpha (σ i) (h i) (k / T) (κ i) (p i) := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.FixedSplitCore.split_explicit_constant_paper
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplitCore
