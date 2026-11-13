module
import StratonovichHAMSecondMoment.InventoryProduct
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.InventoryProduct.pOf
#print axioms StratonovichHAMSecondMoment.InventoryProduct.pOf
#check @StratonovichHAMSecondMoment.InventoryProduct.vCoef
#print axioms StratonovichHAMSecondMoment.InventoryProduct.vCoef
#check @StratonovichHAMSecondMoment.InventoryProduct.bCoef
#print axioms StratonovichHAMSecondMoment.InventoryProduct.bCoef
#check @StratonovichHAMSecondMoment.InventoryProduct.factorCoeff
#print axioms StratonovichHAMSecondMoment.InventoryProduct.factorCoeff
#check @StratonovichHAMSecondMoment.InventoryProduct.factorSeries
#print axioms StratonovichHAMSecondMoment.InventoryProduct.factorSeries
#check @StratonovichHAMSecondMoment.InventoryProduct.inventoryProduct
#print axioms StratonovichHAMSecondMoment.InventoryProduct.inventoryProduct
#check @StratonovichHAMSecondMoment.InventoryProduct.factorEval
#print axioms StratonovichHAMSecondMoment.InventoryProduct.factorEval
#check @StratonovichHAMSecondMoment.InventoryProduct.expConst
#print axioms StratonovichHAMSecondMoment.InventoryProduct.expConst
#check @StratonovichHAMSecondMoment.InventoryProduct.inventoryConst
#print axioms StratonovichHAMSecondMoment.InventoryProduct.inventoryConst
#check @StratonovichHAMSecondMoment.InventoryProduct.inventoryConst_pos
#print axioms StratonovichHAMSecondMoment.InventoryProduct.inventoryConst_pos
#check @StratonovichHAMSecondMoment.InventoryProduct.partialEval
#print axioms StratonovichHAMSecondMoment.InventoryProduct.partialEval
#check @StratonovichHAMSecondMoment.InventoryProduct.coeff_mul_nonneg
#print axioms StratonovichHAMSecondMoment.InventoryProduct.coeff_mul_nonneg
#check @StratonovichHAMSecondMoment.InventoryProduct.coeff_prod_nonneg
#print axioms StratonovichHAMSecondMoment.InventoryProduct.coeff_prod_nonneg
#check @StratonovichHAMSecondMoment.InventoryProduct.partialEval_mul_le
#print axioms StratonovichHAMSecondMoment.InventoryProduct.partialEval_mul_le
#check @StratonovichHAMSecondMoment.InventoryProduct.partialEval_prod_le
#print axioms StratonovichHAMSecondMoment.InventoryProduct.partialEval_prod_le
#check @StratonovichHAMSecondMoment.InventoryProduct.coeff_mul_pow_le_partialEval
#print axioms StratonovichHAMSecondMoment.InventoryProduct.coeff_mul_pow_le_partialEval
#check @StratonovichHAMSecondMoment.InventoryProduct.coeff_prod_le_prod_tsum
#print axioms StratonovichHAMSecondMoment.InventoryProduct.coeff_prod_le_prod_tsum
#check @StratonovichHAMSecondMoment.InventoryProduct.sum_range_rpow_tail_le
#print axioms StratonovichHAMSecondMoment.InventoryProduct.sum_range_rpow_tail_le
#check @StratonovichHAMSecondMoment.InventoryProduct.sum_rpow_tail_le
#print axioms StratonovichHAMSecondMoment.InventoryProduct.sum_rpow_tail_le
#check @StratonovichHAMSecondMoment.InventoryProduct.sum_rpow_pos_le
#print axioms StratonovichHAMSecondMoment.InventoryProduct.sum_rpow_pos_le
#check @StratonovichHAMSecondMoment.InventoryProduct.tail_scaled_le
#print axioms StratonovichHAMSecondMoment.InventoryProduct.tail_scaled_le
#check @StratonovichHAMSecondMoment.InventoryProduct.one_add_sq_le_four_pow
#print axioms StratonovichHAMSecondMoment.InventoryProduct.one_add_sq_le_four_pow
#check @StratonovichHAMSecondMoment.InventoryProduct.sq_le_two_pow_succ
#print axioms StratonovichHAMSecondMoment.InventoryProduct.sq_le_two_pow_succ
#check @StratonovichHAMSecondMoment.InventoryProduct.factorial_rpow_ge_one
#print axioms StratonovichHAMSecondMoment.InventoryProduct.factorial_rpow_ge_one
#check @StratonovichHAMSecondMoment.InventoryProduct.factor_small
#print axioms StratonovichHAMSecondMoment.InventoryProduct.factor_small
#check @StratonovichHAMSecondMoment.InventoryProduct.factor_large
#print axioms StratonovichHAMSecondMoment.InventoryProduct.factor_large
#check @StratonovichHAMSecondMoment.InventoryProduct.params
#print axioms StratonovichHAMSecondMoment.InventoryProduct.params
#check @StratonovichHAMSecondMoment.InventoryProduct.gExp
#print axioms StratonovichHAMSecondMoment.InventoryProduct.gExp
#check @StratonovichHAMSecondMoment.InventoryProduct.factorCoeff_nonneg
#print axioms StratonovichHAMSecondMoment.InventoryProduct.factorCoeff_nonneg
#check @StratonovichHAMSecondMoment.InventoryProduct.factor_partial_le
#print axioms StratonovichHAMSecondMoment.InventoryProduct.factor_partial_le
#check @StratonovichHAMSecondMoment.InventoryProduct.inventory_product_eval_le
#print axioms StratonovichHAMSecondMoment.InventoryProduct.inventory_product_eval_le
#check @StratonovichHAMSecondMoment.InventoryProduct.inventory_product
#print axioms StratonovichHAMSecondMoment.InventoryProduct.inventory_product
#check @StratonovichHAMSecondMoment.InventoryProduct.inventory_product_paper
#print axioms StratonovichHAMSecondMoment.InventoryProduct.inventory_product_paper

open MeasureTheory PowerSeries StratonovichHAMSecondMoment
open scoped Nat

namespace StratonovichHAMSecondMoment.Audit.InventoryProduct

open StratonovichHAMSecondMoment.InventoryProduct

/-- Consumer of the wrapper: under `H:homog`, the coefficient of `z` in the
product (the sum `∑_{i=1}^M v_i` at `k = 1`) is bounded uniformly in `M`
by the constant `C(α, α₀)`. -/
private theorem audit_consumer {d : ℕ} {alpha alpha0 : ℝ} {Γ μ : Measure (HomogHypothesis.Rd d)}
    (h : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) (M : ℕ) :
    coeff 1 (inventoryProduct alpha alpha0 M 1) ≤ inventoryConst alpha alpha0 := by
  have := (inventory_product_paper h).2 M 1 le_rfl
  simpa using this

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.InventoryProduct
