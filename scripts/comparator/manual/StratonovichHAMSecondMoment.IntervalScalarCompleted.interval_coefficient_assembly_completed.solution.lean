namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IntervalScalarCompleted
open Real Finset MeasureTheory
open scoped Nat
open StratonovichHAMSecondMoment.IntervalScalar StratonovichHAMSecondMoment.TypeContinuity
-- Statement copied from the source (the printed type elaborates `MulZeroClass.toZero` where the declaration has `AddZero.toZero`).
/-- alpha < 2, 0 < alpha0 < 1, alpha + alpha0 < 2, k >= 1, T > 0, L >= 1, c, R, V, Cs >= 0, h_j > 0, h_j <= L T/(j+1), sigma_j^2 <= c h_j^(-alpha0), hsplits, hfixed: |coef| <= (12 c L^b Cs C)^k R^k T^(b k)/(k!)^(3-alpha) V, C = inventoryConst, b = 4-alpha-alpha0. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.IntervalScalarCompleted.interval_coefficient_assembly_completed {alpha alpha0 R T L c Cs V coef : ℝ}
    {M k : ℕ} (h σ : Fin M → ℝ) (Q : (Fin M → ℕ × ℕ) → ℝ)
    (hα2 : alpha < 2) (ha0 : 0 < alpha0) (ha01 : alpha0 < 1) (hsum : alpha + alpha0 < 2)
    (hk : 1 ≤ k) (hT : 0 < T) (hL : 1 ≤ L) (hc : 0 ≤ c) (hR : 0 ≤ R) (hV : 0 ≤ V) (hCs : 0 ≤ Cs)
    (hh : ∀ i, 0 < h i) (hlen : ∀ i : Fin M, h i ≤ L * T / ((i : ℕ) + 1 : ℕ))
    (hσ : ∀ i, σ i ^ 2 ≤ c * h i ^ (-alpha0))
    (hsplits : coef = ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∑ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)), Q p)
    (hfixed : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ (k : ℝ) ^ 2 * Cs ^ k * R ^ k * V *
          ∏ i, splitFactor alpha (σ i) (h i) (k / T) (κ i) (p i)) :
    |coef| ≤ (12 * c * L ^ (4 - alpha - alpha0) * Cs *
        InventoryProduct.inventoryConst alpha alpha0) ^ k * R ^ k *
      T ^ ((4 - alpha - alpha0) * k) / (k ! : ℝ) ^ (3 - alpha) * V := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.IntervalScalarCompleted.interval_coefficient_assembly_completed
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IntervalScalarCompleted
