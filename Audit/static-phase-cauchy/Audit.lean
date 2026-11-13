module
import StratonovichHAMSecondMoment.StaticPhaseCauchy
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.phaseI
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.phaseI
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.phaseI_integrableOn
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.phaseI_integrableOn
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.phaseI_pos
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.phaseI_pos
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.deltaA
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.deltaA
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.deltaA_pos
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.deltaA_pos
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.deltaA_le_quarter
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.deltaA_le_quarter
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.taylorCoeff
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.taylorCoeff
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.taylorCoeff_eq_coeff
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.taylorCoeff_eq_coeff
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.norm_taylorCoeff_le
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.norm_taylorCoeff_le
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.norm_taylorCoeff_le_of_disc
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.norm_taylorCoeff_le_of_disc
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.fockD
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.fockD
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.fockD_nonneg
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.fockD_nonneg
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.fockD_le
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.fockD_le
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.orderConst
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.orderConst
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.allOrdersA
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.allOrdersA
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.allOrdersA_pos
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.allOrdersA_pos
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.phase_weight_le
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.phase_weight_le
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.order_display_eq
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.order_display_eq
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.hundred_mul_le
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.hundred_mul_le
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.rpow_neg_le_factorial
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.rpow_neg_le_factorial
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.order_final_le
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.order_final_le
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.all_orders_arith
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.all_orders_arith
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.static_phase_order_cutoff
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.static_phase_order_cutoff
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.static_phase_all_orders_step
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.static_phase_all_orders_step
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.sum_exponent_eq
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.sum_exponent_eq
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.all_static_phase_sum_step
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.all_static_phase_sum_step
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.static_phase_all_orders_paper
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.static_phase_all_orders_paper
#check @StratonovichHAMSecondMoment.StaticPhaseCauchy.all_static_phase_sum_paper
#print axioms StratonovichHAMSecondMoment.StaticPhaseCauchy.all_static_phase_sum_paper

open MeasureTheory Filter Topology StratonovichHAMSecondMoment
open scoped Nat

namespace StratonovichHAMSecondMoment.Audit.StaticPhaseCauchy

open StratonovichHAMSecondMoment.StaticPhaseCauchy

/-- Consumer of the two wrappers: if the order bounds of
`static_phase_all_orders_paper` hold for every `n ≥ 1` (as norms of the phases `Z n`)
together with the free bound for `Z 0`, then `E:all-static-phase-sum` holds. -/
private theorem audit_consumer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Z : ℕ → E) {alpha R h σ N : ℝ}
    (μ Γ : Measure (HomogHypothesis.Rd 3))
    (hμ : IsLocallyFiniteMeasure μ) (hΓ : IsLocallyFiniteMeasure Γ)
    (hα0 : 0 < alpha) (hα2 : alpha < 2)
    (hRdef : R = alpha * Real.pi * (μ (Metric.ball 0 1)).toReal /
      (2 * Real.sin (Real.pi * alpha / 2)))
    (hh : 0 < h) (hZ0 : ‖Z 0‖ ≤ √(Real.exp 1) * N)
    (hZ : ∀ n, 1 ≤ n → ‖Z n‖ ≤ (allOrdersA alpha * √R) ^ n * h ^ ((4 - alpha) * n / 2) /
      (n ! : ℝ) ^ ((3 - alpha) / 2) * N) :
    ‖∑' n, σ ^ n • Z n‖ ^ 2 ≤ (√(Real.exp 1) + 2) ^ 2 *
        Real.exp (6 * allOrdersA alpha ^ (2 / (3 - alpha)) * (|σ| ^ 2 * R) ^ (1 / (3 - alpha)) *
          h ^ ((4 - alpha) / (3 - alpha))) * N ^ 2 :=
  (all_static_phase_sum_paper Z μ Γ hμ hΓ hα0 hα2 hRdef hh hZ0 hZ).2.2

#print axioms audit_consumer

/-- `δ_a` is a genuine positive number below `1/4` at `a = 1/2` (`α = 1`). -/
example : 0 < deltaA (1 / 2) ∧ deltaA (1 / 2) ≤ 1 / 4 :=
  ⟨deltaA_pos (by norm_num), deltaA_le_quarter _⟩

end StratonovichHAMSecondMoment.Audit.StaticPhaseCauchy
