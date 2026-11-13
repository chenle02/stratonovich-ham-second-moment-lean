module
import StratonovichHAMSecondMoment.IntervalScalarCompleted
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.IntervalScalarCompleted.invV_eq
#print axioms StratonovichHAMSecondMoment.IntervalScalarCompleted.invV_eq
#check @StratonovichHAMSecondMoment.IntervalScalarCompleted.invB_eq
#print axioms StratonovichHAMSecondMoment.IntervalScalarCompleted.invB_eq
#check @StratonovichHAMSecondMoment.IntervalScalarCompleted.invCoeff_eq
#print axioms StratonovichHAMSecondMoment.IntervalScalarCompleted.invCoeff_eq
#check @StratonovichHAMSecondMoment.IntervalScalarCompleted.prod_fin_eq_inventoryProduct
#print axioms StratonovichHAMSecondMoment.IntervalScalarCompleted.prod_fin_eq_inventoryProduct
#check @StratonovichHAMSecondMoment.IntervalScalarCompleted.inventoryProduct_holds
#print axioms StratonovichHAMSecondMoment.IntervalScalarCompleted.inventoryProduct_holds
#check @StratonovichHAMSecondMoment.IntervalScalarCompleted.inventoryProduct_holds_paper
#print axioms StratonovichHAMSecondMoment.IntervalScalarCompleted.inventoryProduct_holds_paper
#check @StratonovichHAMSecondMoment.IntervalScalarCompleted.interval_coefficient_assembly_completed
#print axioms StratonovichHAMSecondMoment.IntervalScalarCompleted.interval_coefficient_assembly_completed
#check @StratonovichHAMSecondMoment.IntervalScalarCompleted.interval_coefficient_assembly_paper_completed
#print axioms StratonovichHAMSecondMoment.IntervalScalarCompleted.interval_coefficient_assembly_paper_completed

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.IntervalScalarCompleted

open StratonovichHAMSecondMoment.IntervalScalarCompleted

/-- Consumer of the wrapper: under `H:homog`, the `L:inventory-product` input of
`IntervalScalar.interval_coefficient_assembly_paper` is available with the explicit
positive constant `InventoryProduct.inventoryConst α α₀`, so the original wrapper
applies with that constant and no `hinv` argument from the caller. -/
private theorem audit_consumer {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (HomogHypothesis.Rd d)}
    (hH : HomogHypothesis.HomogCovariance d alpha alpha0 Γ μ) (M k : ℕ) (hk : 1 ≤ k) :
    0 < InventoryProduct.inventoryConst alpha alpha0 ∧
      PowerSeries.coeff k (∏ j : Fin M,
          PowerSeries.mk (IntervalScalar.invCoeff alpha alpha0 k ((j : ℕ) + 1))) ≤
        InventoryProduct.inventoryConst alpha alpha0 ^ k / (k.factorial : ℝ) ^ (3 - alpha) :=
  ⟨(inventoryProduct_holds_paper hH).1, (inventoryProduct_holds_paper hH).2 M k hk⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.IntervalScalarCompleted
