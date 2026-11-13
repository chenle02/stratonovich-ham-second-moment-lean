namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IntervalScalar
open Real Finset Filter Topology MeasureTheory
open scoped Nat
-- Statement copied from the source (the printed type elaborates `MulZeroClass.toZero` where the declaration has `AddZero.toZero`).
/-- Under H:homog, R = R_alpha > 0, sigma_i > 0, k >= 1, T > 0, V, Cs >= 0, h_i > 0, h_i <= LT/(i+1), sigma_i^2 <= c h_i^(-alpha0) (real L, c), supplied hinv, hsplits, hfixed: |coef| <= (12 max(c,0) max(1,L)^beta Cs Cinv)^k R^k T^(beta k)/(k!)^(3-alpha) V. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.IntervalScalar.interval_coefficient_assembly_paper {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ)
    {R T L c Cs Cinv V coef : ℝ} {M k : ℕ}
    (h σ : Fin M → ℝ) (Q : (Fin M → ℕ × ℕ) → ℝ)
    (hRdef : R = alpha * π * (μ (Metric.ball 0 1)).toReal / (2 * Real.sin (π * alpha / 2)))
    (_hRpos : 0 < R) (hk : 1 ≤ k) (hT : 0 < T) (hV : 0 ≤ V) (hCs : 0 ≤ Cs)
    (hh : ∀ i, 0 < h i) (_hσpos : ∀ i, 0 < σ i)
    (hlen : ∀ i : Fin M, h i ≤ L * T / ((i : ℕ) + 1 : ℕ))
    (hσ : ∀ i, σ i ^ 2 ≤ c * h i ^ (-alpha0))
    (hinv : InventoryProduct alpha alpha0 Cinv)
    (hsplits : coef = ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∑ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)), Q p)
    (hfixed : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ (k : ℝ) ^ 2 * Cs ^ k * R ^ k * V *
          ∏ i, splitFactor alpha (σ i) (h i) (k / T) (κ i) (p i)) :
    |coef| ≤ (12 * max c 0 * max 1 L ^ (4 - alpha - alpha0) * Cs * Cinv) ^ k * R ^ k *
      T ^ ((4 - alpha - alpha0) * k) / (k ! : ℝ) ^ (3 - alpha) * V := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IntervalScalar
