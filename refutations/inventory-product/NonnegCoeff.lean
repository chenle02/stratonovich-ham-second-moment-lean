/-
Refutation for the evaluation bound `[z^k]F ≤ F(z)/z^k` (inside the proof of
`L:inventory-product`, `notes/notes_stratonovich_ham_second_moment.tex`
lines 3037-3038 at a284420), package theorem
`StratonovichHAMSecondMoment.InventoryProduct.coeff_prod_le_prod_tsum`.

Wrong variant: the bound without the nonnegativity of the coefficients.
Counterexample: one factor `F = -1 + z`, `z = 1`, `k = 1`: `[z^1]F = 1` but
`F(1)/1 = 0`. `nonneg_coeff_contrast` applies the package theorem to
`F = 1 + z` at the same point (`1 ≤ 2`).
No junk-value reliance (the series has finite support, so it is summable).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.InventoryProduct

set_option autoImplicit false

open PowerSeries Finset
open StratonovichHAMSecondMoment.InventoryProduct

namespace Refutations.InventoryProduct

/-- The coefficients `-1, 1, 0, 0, …`. -/
noncomputable def signedCoeff (n : ℕ) : ℝ := if n = 0 then -1 else if n = 1 then 1 else 0

theorem signed_summable :
    Summable (fun n => coeff n (PowerSeries.mk signedCoeff) * (1 : ℝ) ^ n) := by
  refine summable_of_ne_finset_zero (s := range 2) fun n hn => ?_
  simp only [mem_range, not_lt] at hn
  simp [signedCoeff, show n ≠ 0 by omega, show n ≠ 1 by omega]

theorem signed_tsum :
    ∑' n, coeff n (PowerSeries.mk signedCoeff) * (1 : ℝ) ^ n = 0 := by
  rw [tsum_eq_sum (s := range 2)]
  · simp [Finset.sum_range_succ, signedCoeff]
  · intro n hn
    simp only [mem_range, not_lt] at hn
    simp [signedCoeff, show n ≠ 0 by omega, show n ≠ 1 by omega]

/-- The evaluation bound without nonnegative coefficients is false. -/
theorem nonneg_coeff_refuted :
    ¬ (∀ (s : Finset ℕ) (F : ℕ → PowerSeries ℝ) (z : ℝ), 0 < z →
        (∀ i ∈ s, Summable (fun n => coeff n (F i) * z ^ n)) → ∀ k : ℕ,
          coeff k (∏ i ∈ s, F i) ≤ (∏ i ∈ s, ∑' n, coeff n (F i) * z ^ n) / z ^ k) := by
  intro h
  have := h {0} (fun _ => PowerSeries.mk signedCoeff) 1 one_pos
    (fun _ _ => signed_summable) 1
  rw [prod_singleton, prod_singleton, signed_tsum] at this
  norm_num [signedCoeff] at this

/-- The package theorem at `F = 1 + z`, `z = 1`, `k = 1`. -/
theorem nonneg_coeff_contrast :
    coeff 1 (∏ _i ∈ ({0} : Finset ℕ),
        PowerSeries.mk (fun n : ℕ => if n ≤ 1 then (1 : ℝ) else 0)) ≤
      (∏ _i ∈ ({0} : Finset ℕ), ∑' n, coeff n
        (PowerSeries.mk (fun n : ℕ => if n ≤ 1 then (1 : ℝ) else 0)) * (1 : ℝ) ^ n) /
        (1 : ℝ) ^ 1 := by
  refine coeff_prod_le_prod_tsum {0} _ (fun _ _ n => ?_) one_pos (fun _ _ => ?_) 1
  · rw [coeff_mk]; split_ifs <;> norm_num
  · refine summable_of_ne_finset_zero (s := range 2) fun n hn => ?_
    simp only [mem_range, not_lt] at hn
    simp [show ¬ n ≤ 1 by omega]

end Refutations.InventoryProduct
