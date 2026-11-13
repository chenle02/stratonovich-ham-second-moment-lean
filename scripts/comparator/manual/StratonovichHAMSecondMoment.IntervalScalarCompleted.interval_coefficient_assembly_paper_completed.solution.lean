namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IntervalScalarCompleted
open Real Finset MeasureTheory
open scoped Nat
open StratonovichHAMSecondMoment.IntervalScalar StratonovichHAMSecondMoment.TypeContinuity
-- Statement copied from the source (the printed type elaborates `MulZeroClass.toZero` where the declaration has `AddZero.toZero`).
/-- H:homog, R = alpha pi mu(B_1)/(2 sin(pi alpha/2)) > 0, sigma_j > 0, k >= 1, T > 0, V, Cs >= 0, h_j > 0, h_j <= L T/(j+1), sigma_j^2 <= c h_j^(-alpha0), hsplits, hfixed: |coef| <= (12 max(c,0) max(1,L)^b Cs C)^k R^k T^(b k)/(k!)^(3-alpha) V, C = inventoryConst. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.IntervalScalarCompleted.interval_coefficient_assembly_paper_completed {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    {R T L c Cs V coef : ℝ} {M k : ℕ}
    (h σ : Fin M → ℝ) (Q : (Fin M → ℕ × ℕ) → ℝ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (_hRpos : 0 < R) (hk : 1 ≤ k) (hT : 0 < T) (hV : 0 ≤ V) (hCs : 0 ≤ Cs)
    (hh : ∀ i, 0 < h i) (_hσpos : ∀ i, 0 < σ i)
    (hlen : ∀ i : Fin M, h i ≤ L * T / ((i : ℕ) + 1 : ℕ))
    (hσ : ∀ i, σ i ^ 2 ≤ c * h i ^ (-alpha0))
    (hsplits : coef = ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∑ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)), Q p)
    (hfixed : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ (k : ℝ) ^ 2 * Cs ^ k * R ^ k * V *
          ∏ i, splitFactor alpha (σ i) (h i) (k / T) (κ i) (p i)) :
    |coef| ≤ (12 * max c 0 * max 1 L ^ (4 - alpha - alpha0) * Cs *
        InventoryProduct.inventoryConst alpha alpha0) ^ k * R ^ k *
      T ^ ((4 - alpha - alpha0) * k) / (k ! : ℝ) ^ (3 - alpha) * V := by
  bridge_revert_all
  bridge_auto _root_.StratonovichHAMSecondMoment.IntervalScalarCompleted.interval_coefficient_assembly_paper_completed
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IntervalScalarCompleted
