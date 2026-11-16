namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplitCore
open Finset Real MeasureTheory
open scoped Nat
open StratonovichHAMSecondMoment.IntervalScalar
-- Statement copied from the source (the printed type elaborates `0` through `MulZeroClass.toZero`, the declaration through `AddZero.toZero`).
/-- IntervalScalarCompleted.interval_coefficient_assembly_paper_completed with its input hfixed (E:fixed-split-bound) replaced by the before-absorption bound hbefore (E:split-before-absorption) and C_split = splitConst delta; every other hypothesis kept. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.FixedSplitCore.interval_coefficient_of_before_absorption_paper {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    {R T L c δ V coef : ℝ} {M k : ℕ}
    (h σ : Fin M → ℝ) (Q : (Fin M → ℕ × ℕ) → ℝ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (hRpos : 0 < R) (hk : 1 ≤ k) (hT : 0 < T) (hV : 0 ≤ V) (hδ : 0 < δ)
    (hh : ∀ i, 0 < h i) (hσpos : ∀ i, 0 < σ i)
    (hlen : ∀ i : Fin M, h i ≤ L * T / ((i : ℕ) + 1 : ℕ))
    (hσ : ∀ i, σ i ^ 2 ≤ c * h i ^ (-alpha0))
    (hsplits : coef = ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∑ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)), Q p)
    (hbefore : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ (k : ℝ) ^ 2 * Mk k ^ 2 * V *
          ∏ i, beforeFactor alpha δ R (σ i) (h i) (k / T) (κ i) (p i)) :
    |coef| ≤ (12 * max c 0 * max 1 L ^ (4 - alpha - alpha0) * splitConst δ *
        InventoryProduct.inventoryConst alpha alpha0) ^ k * R ^ k *
      T ^ ((4 - alpha - alpha0) * k) / (k ! : ℝ) ^ (3 - alpha) * V := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.FixedSplitCore.interval_coefficient_of_before_absorption_paper
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.FixedSplitCore
