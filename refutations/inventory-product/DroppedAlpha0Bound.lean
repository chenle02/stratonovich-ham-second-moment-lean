/-
Refutation for `L:inventory-product` (`notes/notes_stratonovich_ham_second_moment.tex`
lines 2986-2998 at a284420), package theorem
`StratonovichHAMSecondMoment.InventoryProduct.inventory_product`.

Wrong variant: the hypothesis `α₀ < 1` (from `H:homog`, giving `p = 2 - α₀ > 1`)
dropped, keeping `0 < α₀` and `α₀ + α < 2`. Counterexample: `α₀ = 1`,
`α = 1/2`, so `p = 1`. At `k = 1` the coefficient of `z` in the product is
`∑_{i=1}^M v_i ≥ ∑_{i=1}^M 1/i`, which is unbounded in `M` (harmonic series),
so no constant `C` independent of `M` exists. `dropped_alpha0_contrast` is the
package theorem at `α₀ = 1/2`, `α = 1/2`.
No junk-value reliance (`i, k ≥ 1`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.InventoryProduct

set_option autoImplicit false

open PowerSeries Finset Filter
open scoped Nat
open StratonovichHAMSecondMoment.InventoryProduct StratonovichHAMSecondMoment.TypeContinuity

namespace Refutations.InventoryProduct

/-- The coefficient of `z` in a finite product of series with constant term `1`
is the sum of the coefficients of `z`. -/
theorem coeff_one_prod {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℝ)
    (h0 : ∀ i ∈ s, coeff 0 (F i) = 1) :
    coeff 0 (∏ i ∈ s, F i) = 1 ∧ coeff 1 (∏ i ∈ s, F i) = ∑ i ∈ s, coeff 1 (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeff_one]
  | insert j s hj ih =>
    obtain ⟨ih0, ih1⟩ := ih fun i hi => h0 i (mem_insert_of_mem hi)
    have hj0 := h0 j (mem_insert_self j s)
    rw [prod_insert hj, sum_insert hj]
    constructor
    · simp [coeff_mul, hj0, ih0]
    · rw [coeff_mul, Finset.Nat.antidiagonal_succ]
      simp [hj0, ih0, ih1]
      ring

/-- At `α₀ = 1`, `α = 1/2`, `k = 1` the coefficient of `z` is at least the
harmonic sum. -/
theorem harmonic_le_coeff (M : ℕ) :
    ∑ i ∈ range M, (1 : ℝ) / ((i : ℝ) + 1) ≤ coeff 1 (inventoryProduct (1 / 2) 1 M 1) := by
  have h0 : ∀ i ∈ Icc 1 M, coeff 0 (factorSeries (1 / 2) 1 1 i) = 1 := by
    intro i _; simp [factorSeries, factorCoeff]
  rw [inventoryProduct, (coeff_one_prod _ _ h0).2]
  have hv : ∀ i ∈ Icc 1 M, (1 : ℝ) / i ≤ coeff 1 (factorSeries (1 / 2) 1 1 i) := by
    intro i _
    simp only [factorSeries, coeff_mk, factorCoeff, one_ne_zero, ↓reduceIte, vCoef, pOf]
    have h1 : (1 : ℝ) / i = (i : ℝ) ^ (-(2 - 1 : ℝ)) := by
      rw [show -(2 - 1 : ℝ) = -1 by norm_num, Real.rpow_neg_one, one_div]
    rw [h1]
    simp only [Nat.cast_one, inv_one, one_mul, Real.one_rpow]
    have := Real.rpow_nonneg (Nat.cast_nonneg i : (0 : ℝ) ≤ i) (-betaOf (1 / 2) 1)
    have := Real.rpow_nonneg (Nat.cast_nonneg i : (0 : ℝ) ≤ i) (-(betaOf (1 / 2) 1 - 1))
    linarith
  have himg : (range M).image (fun j : ℕ => j + 1) ⊆ Icc 1 M := by
    intro i hi; simp only [mem_image, mem_range] at hi
    obtain ⟨j, hj, rfl⟩ := hi; rw [mem_Icc]; omega
  calc ∑ i ∈ range M, (1 : ℝ) / ((i : ℝ) + 1)
      = ∑ i ∈ (range M).image (fun j : ℕ => j + 1), (1 : ℝ) / (i : ℝ) := by
        rw [sum_image (fun x _ y _ h => by simpa using h)]; push_cast; rfl
    _ ≤ ∑ i ∈ Icc 1 M, (1 : ℝ) / (i : ℝ) :=
        sum_le_sum_of_subset_of_nonneg himg fun i _ _ => by positivity
    _ ≤ _ := sum_le_sum hv

/-- Dropping `α₀ < 1` makes `L:inventory-product` false. -/
theorem dropped_alpha0_refuted :
    ¬ (∀ alpha alpha0 : ℝ, 0 < alpha0 → alpha0 + alpha < 2 →
        ∃ C : ℝ, ∀ M k : ℕ, 1 ≤ k →
          coeff k (inventoryProduct alpha alpha0 M k) ≤ C ^ k / ((k ! : ℕ) : ℝ) ^ nuOf alpha) := by
  intro h
  obtain ⟨C, hC⟩ := h (1 / 2) 1 (by norm_num) (by norm_num)
  have htend := Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨M, hM⟩ := (htend.eventually_gt_atTop C).exists
  have h1 := hC M 1 le_rfl
  have h2 := harmonic_le_coeff M
  simp only [Nat.factorial_one, Nat.cast_one, Real.one_rpow, pow_one, div_one] at h1
  linarith

/-- The package theorem at `α₀ = α = 1/2`. -/
theorem dropped_alpha0_contrast (M k : ℕ) (hk : 1 ≤ k) :
    coeff k (inventoryProduct (1 / 2) (1 / 2) M k) ≤
      inventoryConst (1 / 2) (1 / 2) ^ k / ((k ! : ℕ) : ℝ) ^ nuOf (1 / 2) :=
  inventory_product (by norm_num) (by norm_num) (by norm_num) M k hk

end Refutations.InventoryProduct
