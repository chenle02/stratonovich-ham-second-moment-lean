module

import StratonovichHAMSecondMoment.FiniteWick

set_option autoImplicit false
set_option pp.all true

#check @StratonovichHAMSecondMoment.FiniteWick.pairings
#print axioms StratonovichHAMSecondMoment.FiniteWick.pairings
#check @StratonovichHAMSecondMoment.FiniteWick.pairWeight
#print axioms StratonovichHAMSecondMoment.FiniteWick.pairWeight
#check @StratonovichHAMSecondMoment.FiniteWick.wickSum
#print axioms StratonovichHAMSecondMoment.FiniteWick.wickSum
#check @StratonovichHAMSecondMoment.FiniteWick.mem_pairings
#print axioms StratonovichHAMSecondMoment.FiniteWick.mem_pairings
#check @StratonovichHAMSecondMoment.FiniteWick.pairings_empty
#print axioms StratonovichHAMSecondMoment.FiniteWick.pairings_empty
#check @StratonovichHAMSecondMoment.FiniteWick.wickSum_empty
#print axioms StratonovichHAMSecondMoment.FiniteWick.wickSum_empty
#check @StratonovichHAMSecondMoment.FiniteWick.unpair
#print axioms StratonovichHAMSecondMoment.FiniteWick.unpair
#check @StratonovichHAMSecondMoment.FiniteWick.pairUp
#print axioms StratonovichHAMSecondMoment.FiniteWick.pairUp
#check @StratonovichHAMSecondMoment.FiniteWick.unpair_a
#print axioms StratonovichHAMSecondMoment.FiniteWick.unpair_a
#check @StratonovichHAMSecondMoment.FiniteWick.unpair_b
#print axioms StratonovichHAMSecondMoment.FiniteWick.unpair_b
#check @StratonovichHAMSecondMoment.FiniteWick.unpair_other
#print axioms StratonovichHAMSecondMoment.FiniteWick.unpair_other
#check @StratonovichHAMSecondMoment.FiniteWick.pairUp_a
#print axioms StratonovichHAMSecondMoment.FiniteWick.pairUp_a
#check @StratonovichHAMSecondMoment.FiniteWick.pairUp_b
#print axioms StratonovichHAMSecondMoment.FiniteWick.pairUp_b
#check @StratonovichHAMSecondMoment.FiniteWick.pairUp_other
#print axioms StratonovichHAMSecondMoment.FiniteWick.pairUp_other
#check @StratonovichHAMSecondMoment.FiniteWick.fiber_sum
#print axioms StratonovichHAMSecondMoment.FiniteWick.fiber_sum
#check @StratonovichHAMSecondMoment.FiniteWick.wickSum_eq_sum_erase
#print axioms StratonovichHAMSecondMoment.FiniteWick.wickSum_eq_sum_erase
#check @StratonovichHAMSecondMoment.FiniteWick.card_erase_erase
#print axioms StratonovichHAMSecondMoment.FiniteWick.card_erase_erase
#check @StratonovichHAMSecondMoment.FiniteWick.wickSum_odd
#print axioms StratonovichHAMSecondMoment.FiniteWick.wickSum_odd
#check @StratonovichHAMSecondMoment.FiniteWick.wickSum_const_one
#print axioms StratonovichHAMSecondMoment.FiniteWick.wickSum_const_one
#check @StratonovichHAMSecondMoment.FiniteWick.wickSum_abs_le
#print axioms StratonovichHAMSecondMoment.FiniteWick.wickSum_abs_le
#check @StratonovichHAMSecondMoment.FiniteWick.card_pairings_even
#print axioms StratonovichHAMSecondMoment.FiniteWick.card_pairings_even
#check @StratonovichHAMSecondMoment.FiniteWick.card_pairings_odd
#print axioms StratonovichHAMSecondMoment.FiniteWick.card_pairings_odd
#check @StratonovichHAMSecondMoment.FiniteWick.wickSum_nonneg
#print axioms StratonovichHAMSecondMoment.FiniteWick.wickSum_nonneg
#check @StratonovichHAMSecondMoment.FiniteWick.wickSum_mono
#print axioms StratonovichHAMSecondMoment.FiniteWick.wickSum_mono
#check @StratonovichHAMSecondMoment.FiniteWick.matBound
#print axioms StratonovichHAMSecondMoment.FiniteWick.matBound
#check @StratonovichHAMSecondMoment.FiniteWick.one_le_matBound
#print axioms StratonovichHAMSecondMoment.FiniteWick.one_le_matBound
#check @StratonovichHAMSecondMoment.FiniteWick.mulVec_apply_eq
#print axioms StratonovichHAMSecondMoment.FiniteWick.mulVec_apply_eq
#check @StratonovichHAMSecondMoment.FiniteWick.abs_mulVec_le
#print axioms StratonovichHAMSecondMoment.FiniteWick.abs_mulVec_le
#check @StratonovichHAMSecondMoment.FiniteWick.abs_prod_mulVec_le
#print axioms StratonovichHAMSecondMoment.FiniteWick.abs_prod_mulVec_le
#check @StratonovichHAMSecondMoment.FiniteWick.continuous_mulVec_apply
#print axioms StratonovichHAMSecondMoment.FiniteWick.continuous_mulVec_apply
#check @StratonovichHAMSecondMoment.FiniteWick.continuous_prod_mulVec
#print axioms StratonovichHAMSecondMoment.FiniteWick.continuous_prod_mulVec
#check @StratonovichHAMSecondMoment.FiniteWick.hasDerivAt_mulVec_update
#print axioms StratonovichHAMSecondMoment.FiniteWick.hasDerivAt_mulVec_update
#check @StratonovichHAMSecondMoment.FiniteWick.monoDeriv
#print axioms StratonovichHAMSecondMoment.FiniteWick.monoDeriv
#check @StratonovichHAMSecondMoment.FiniteWick.hasDerivAt_prod_update
#print axioms StratonovichHAMSecondMoment.FiniteWick.hasDerivAt_prod_update
#check @StratonovichHAMSecondMoment.FiniteWick.abs_monoDeriv_le
#print axioms StratonovichHAMSecondMoment.FiniteWick.abs_monoDeriv_le
#check @StratonovichHAMSecondMoment.FiniteWick.integrable_prod_mulVec
#print axioms StratonovichHAMSecondMoment.FiniteWick.integrable_prod_mulVec
#check @StratonovichHAMSecondMoment.FiniteWick.continuous_monoDeriv
#print axioms StratonovichHAMSecondMoment.FiniteWick.continuous_monoDeriv
#check @StratonovichHAMSecondMoment.FiniteWick.wick_stdPi
#print axioms StratonovichHAMSecondMoment.FiniteWick.wick_stdPi
#check @StratonovichHAMSecondMoment.FiniteWick.sqrt_mul_transpose
#print axioms StratonovichHAMSecondMoment.FiniteWick.sqrt_mul_transpose
#check @StratonovichHAMSecondMoment.FiniteWick.integral_multivariateGaussian_eq
#print axioms StratonovichHAMSecondMoment.FiniteWick.integral_multivariateGaussian_eq
#check @StratonovichHAMSecondMoment.FiniteWick.integrable_multivariateGaussian_iff
#print axioms StratonovichHAMSecondMoment.FiniteWick.integrable_multivariateGaussian_iff
#check @StratonovichHAMSecondMoment.FiniteWick.wick_multivariateGaussian
#print axioms StratonovichHAMSecondMoment.FiniteWick.wick_multivariateGaussian
#check @StratonovichHAMSecondMoment.FiniteWick.wick_hasLaw
#print axioms StratonovichHAMSecondMoment.FiniteWick.wick_hasLaw
#check @StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField
#print axioms StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField
#check @StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField.wick
#print axioms StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField.wick
#check @StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField.wick_univ
#print axioms StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField.wick_univ
#check @StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField.symm
#print axioms StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField.symm
#check @StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField.abs_le
#print axioms StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField.abs_le
#check @StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField.wick_append
#print axioms StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField.wick_append
#check @StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField.sq_moment_le
#print axioms StratonovichHAMSecondMoment.FiniteWick.CenteredGaussianField.sq_moment_le

open MeasureTheory StratonovichHAMSecondMoment

namespace StratonovichHAMSecondMoment.Audit.FiniteWick

open StratonovichHAMSecondMoment.FiniteWick

/-- Consumer of the field Wick formula: odd moments of a centered Gaussian
field vanish (three points), and the product is integrable. -/
private theorem audit_consumer {X Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : X → Ω → ℝ} {K : X → X → ℝ} (hW : CenteredGaussianField W K P) (p : Fin 3 → X) :
    Integrable (fun ω => ∏ a, W (p a) ω) P ∧ ∫ ω, ∏ a, W (p a) ω ∂P = 0 := by
  obtain ⟨hi, he⟩ := hW.wick_univ p
  exact ⟨hi, he.trans (wickSum_odd _ 1 _ (by simp))⟩

#check @audit_consumer
#print axioms audit_consumer

end StratonovichHAMSecondMoment.Audit.FiniteWick
