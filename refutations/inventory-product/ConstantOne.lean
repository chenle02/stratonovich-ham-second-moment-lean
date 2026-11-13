/-
Refutation for `L:inventory-product` (`notes/notes_stratonovich_ham_second_moment.tex`
lines 2986-2998 at a284420), package theorem
`StratonovichHAMSecondMoment.InventoryProduct.inventory_product`.

Wrong variant: the constant `C = 1`, i.e.
`[z^k] ∏_{i=1}^M (1 + v_i z + ∑_{l≥2} b_{i,l} z^l) ≤ 1/(k!)^ν` under the same
hypotheses. Counterexample: `α = α₀ = 1/2`, `M = k = 1`: the coefficient is
`v_1 = 1 + 1 + 1 = 3 > 1`. `constant_one_contrast` is the package bound at the
same point (with `C = inventoryConst (1/2) (1/2)`).
No junk-value reliance (`i = k = 1`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.InventoryProduct

set_option autoImplicit false

open PowerSeries
open scoped Nat
open StratonovichHAMSecondMoment.InventoryProduct StratonovichHAMSecondMoment.TypeContinuity

namespace Refutations.InventoryProduct

/-- The coefficient of `z` at `M = k = 1` is `v_1 = 3`. -/
theorem coeff_one_one (alpha alpha0 : ℝ) :
    coeff 1 (inventoryProduct alpha alpha0 1 1) = 3 := by
  simp [inventoryProduct, factorSeries, factorCoeff, vCoef]
  norm_num

/-- The constant `C = 1` in `E:inventory-product` is false. -/
theorem constant_one_refuted :
    ¬ (∀ alpha alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → alpha0 + alpha < 2 →
        ∀ M k : ℕ, 1 ≤ k →
          coeff k (inventoryProduct alpha alpha0 M k) ≤
            (1 : ℝ) ^ k / ((k ! : ℕ) : ℝ) ^ nuOf alpha) := by
  intro h
  have := h (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) 1 1 le_rfl
  rw [coeff_one_one] at this
  norm_num at this

/-- The package bound at the same point. -/
theorem constant_one_contrast :
    coeff 1 (inventoryProduct (1 / 2) (1 / 2) 1 1) ≤
      inventoryConst (1 / 2) (1 / 2) ^ 1 / ((1 ! : ℕ) : ℝ) ^ nuOf (1 / 2) :=
  inventory_product (by norm_num) (by norm_num) (by norm_num) 1 1 le_rfl

end Refutations.InventoryProduct
