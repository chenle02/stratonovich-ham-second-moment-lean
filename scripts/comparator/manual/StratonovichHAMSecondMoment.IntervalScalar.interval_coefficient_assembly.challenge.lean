namespace StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IntervalScalar
open Real Finset Filter Topology MeasureTheory
open scoped Nat
-- Statement copied from the source (the printed type elaborates `MulZeroClass.toZero` where the declaration has `AddZero.toZero`).
/-- alpha<2, 0<alpha0<1, alpha+alpha0<2, k>=1, T>0, L>=1, c,R,V,Cs>=0, h_i>0, h_i<=LT/(i+1), sigma_i^2<=c h_i^(-alpha0); supplied InventoryProduct Cinv, coef = split sum of Q, |Q p| <= k^2 Cs^k R^k V prod splitFactor: |coef| <= (12cL^beta Cs Cinv)^k R^k T^(beta k)/(k!)^(3-alpha) V. -/
theorem _root_.StratonovichHamSecondMomentLeanAudit.StratonovichHAMSecondMoment.IntervalScalar.interval_coefficient_assembly {alpha alpha0 R T L c Cs Cinv V coef : ℝ} {M k : ℕ}
    (h σ : Fin M → ℝ) (Q : (Fin M → ℕ × ℕ) → ℝ)
    (hα2 : alpha < 2) (ha0 : 0 < alpha0) (ha01 : alpha0 < 1) (hsum : alpha + alpha0 < 2)
    (hk : 1 ≤ k) (hT : 0 < T) (hL : 1 ≤ L) (hc : 0 ≤ c) (hR : 0 ≤ R) (hV : 0 ≤ V) (hCs : 0 ≤ Cs)
    (hh : ∀ i, 0 < h i) (hlen : ∀ i : Fin M, h i ≤ L * T / ((i : ℕ) + 1 : ℕ))
    (hσ : ∀ i, σ i ^ 2 ≤ c * h i ^ (-alpha0))
    (hinv : InventoryProduct alpha alpha0 Cinv)
    (hsplits : coef = ∑ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∑ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)), Q p)
    (hfixed : ∀ κ ∈ (univ : Finset (Fin M)).finsuppAntidiag k,
      ∀ p ∈ Fintype.piFinset (fun i => antidiagonal (2 * κ i)),
        |Q p| ≤ (k : ℝ) ^ 2 * Cs ^ k * R ^ k * V *
          ∏ i, splitFactor alpha (σ i) (h i) (k / T) (κ i) (p i)) :
    |coef| ≤ (12 * c * L ^ (4 - alpha - alpha0) * Cs * Cinv) ^ k * R ^ k *
      T ^ ((4 - alpha - alpha0) * k) / (k ! : ℝ) ^ (3 - alpha) * V := by
  sorry
end StratonovichHamSecondMomentLeanDefs.StratonovichHAMSecondMoment.IntervalScalar
