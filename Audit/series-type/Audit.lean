module

import StratonovichHAMSecondMoment.SeriesType
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.SeriesType.sum_rpow_le_rpow_sum
#print axioms StratonovichHAMSecondMoment.SeriesType.sum_rpow_le_rpow_sum
#check @StratonovichHAMSecondMoment.SeriesType.term_eq_rpow
#print axioms StratonovichHAMSecondMoment.SeriesType.term_eq_rpow
#check @StratonovichHAMSecondMoment.SeriesType.seriesNu_summable_le
#print axioms StratonovichHAMSecondMoment.SeriesType.seriesNu_summable_le
#check @StratonovichHAMSecondMoment.SeriesType.seriesNu_holder_le
#print axioms StratonovichHAMSecondMoment.SeriesType.seriesNu_holder_le
#check @StratonovichHAMSecondMoment.SeriesType.seriesNu_le_two_exp_three
#print axioms StratonovichHAMSecondMoment.SeriesType.seriesNu_le_two_exp_three
#check @StratonovichHAMSecondMoment.SeriesType.factorial_sq_le_mul_factorial
#print axioms StratonovichHAMSecondMoment.SeriesType.factorial_sq_le_mul_factorial
#check @StratonovichHAMSecondMoment.SeriesType.factorial_ge_exp
#print axioms StratonovichHAMSecondMoment.SeriesType.factorial_ge_exp
#check @StratonovichHAMSecondMoment.SeriesType.factorial_le_exp
#print axioms StratonovichHAMSecondMoment.SeriesType.factorial_le_exp
#check @StratonovichHAMSecondMoment.SeriesType.log_factorial_bounds
#print axioms StratonovichHAMSecondMoment.SeriesType.log_factorial_bounds
#check @StratonovichHAMSecondMoment.SeriesType.gamma_mid_sq_le
#print axioms StratonovichHAMSecondMoment.SeriesType.gamma_mid_sq_le

open scoped Nat

namespace StratonovichHAMSecondMoment.Audit.SeriesType

open StratonovichHAMSecondMoment.SeriesType

/-- Consumer of the series bounds: at `β = 3/2` (inside the TeX's range
`(1/2, 3/2)` closure), `∑ x^k/(k!)^{3/2} ≤ 2 e^{3 x^{2/3}}`, and the split
bound `(k!)^2 ≤ (k-1)! (k+1)!`. -/
private theorem audit_consumer (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    ∑' n : ℕ, x ^ n / (n ! : ℝ) ^ ((3 : ℝ) / 2) ≤ 2 * Real.exp (3 * x ^ (1 / ((3 : ℝ) / 2))) ∧
      (k !) ^ 2 ≤ (k - 1) ! * (k + 1) ! :=
  ⟨(seriesNu_le_two_exp_three (by norm_num) (by norm_num) hx).2,
    factorial_sq_le_mul_factorial (by omega)⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.SeriesType
