module
import StratonovichHAMSecondMoment.TimeSchur
import StratonovichHAMSecondMoment.MaskedModulation
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.TimeSchur.kern
#print axioms StratonovichHAMSecondMoment.TimeSchur.kern
#check @StratonovichHAMSecondMoment.TimeSchur.kern_nonneg
#print axioms StratonovichHAMSecondMoment.TimeSchur.kern_nonneg
#check @StratonovichHAMSecondMoment.TimeSchur.kern_neg
#print axioms StratonovichHAMSecondMoment.TimeSchur.kern_neg
#check @StratonovichHAMSecondMoment.TimeSchur.kern_sub_comm
#print axioms StratonovichHAMSecondMoment.TimeSchur.kern_sub_comm
#check @StratonovichHAMSecondMoment.TimeSchur.measurable_kern
#print axioms StratonovichHAMSecondMoment.TimeSchur.measurable_kern
#check @StratonovichHAMSecondMoment.TimeSchur.intervalIntegrable_abs_rpow
#print axioms StratonovichHAMSecondMoment.TimeSchur.intervalIntegrable_abs_rpow
#check @StratonovichHAMSecondMoment.TimeSchur.integral_abs_rpow_zero
#print axioms StratonovichHAMSecondMoment.TimeSchur.integral_abs_rpow_zero
#check @StratonovichHAMSecondMoment.TimeSchur.integral_abs_rpow_neg
#print axioms StratonovichHAMSecondMoment.TimeSchur.integral_abs_rpow_neg
#check @StratonovichHAMSecondMoment.TimeSchur.integral_row
#print axioms StratonovichHAMSecondMoment.TimeSchur.integral_row
#check @StratonovichHAMSecondMoment.TimeSchur.lintegral_row_le
#print axioms StratonovichHAMSecondMoment.TimeSchur.lintegral_row_le
#check @StratonovichHAMSecondMoment.TimeSchur.two_mul_le_add_sq_ennreal
#print axioms StratonovichHAMSecondMoment.TimeSchur.two_mul_le_add_sq_ennreal
#check @StratonovichHAMSecondMoment.TimeSchur.schur_lintegral
#print axioms StratonovichHAMSecondMoment.TimeSchur.schur_lintegral
#check @StratonovichHAMSecondMoment.TimeSchur.integrand
#print axioms StratonovichHAMSecondMoment.TimeSchur.integrand
#check @StratonovichHAMSecondMoment.TimeSchur.time_schur_rclike
#print axioms StratonovichHAMSecondMoment.TimeSchur.time_schur_rclike
#check @StratonovichHAMSecondMoment.TimeSchur.timeForm
#print axioms StratonovichHAMSecondMoment.TimeSchur.timeForm
#check @StratonovichHAMSecondMoment.TimeSchur.time_schur_complex
#print axioms StratonovichHAMSecondMoment.TimeSchur.time_schur_complex
#check @StratonovichHAMSecondMoment.TimeSchur.time_schur_paper
#print axioms StratonovichHAMSecondMoment.TimeSchur.time_schur_paper
#check @StratonovichHAMSecondMoment.MaskedModulation.ii_rpow_shift
#print axioms StratonovichHAMSecondMoment.MaskedModulation.ii_rpow_shift
#check @StratonovichHAMSecondMoment.MaskedModulation.integral_rpow_shift
#print axioms StratonovichHAMSecondMoment.MaskedModulation.integral_rpow_shift
#check @StratonovichHAMSecondMoment.MaskedModulation.integrable_indicator_Ioc
#print axioms StratonovichHAMSecondMoment.MaskedModulation.integrable_indicator_Ioc
#check @StratonovichHAMSecondMoment.MaskedModulation.integral_indicator_Ioc
#print axioms StratonovichHAMSecondMoment.MaskedModulation.integral_indicator_Ioc
#check @StratonovichHAMSecondMoment.MaskedModulation.majorant
#print axioms StratonovichHAMSecondMoment.MaskedModulation.majorant
#check @StratonovichHAMSecondMoment.MaskedModulation.majorant_integrable
#print axioms StratonovichHAMSecondMoment.MaskedModulation.majorant_integrable
#check @StratonovichHAMSecondMoment.MaskedModulation.majorant_integral_le
#print axioms StratonovichHAMSecondMoment.MaskedModulation.majorant_integral_le
#check @StratonovichHAMSecondMoment.MaskedModulation.profile
#print axioms StratonovichHAMSecondMoment.MaskedModulation.profile
#check @StratonovichHAMSecondMoment.MaskedModulation.norm_ofReal_rpow
#print axioms StratonovichHAMSecondMoment.MaskedModulation.norm_ofReal_rpow
#check @StratonovichHAMSecondMoment.MaskedModulation.profile_sub_le
#print axioms StratonovichHAMSecondMoment.MaskedModulation.profile_sub_le
#check @StratonovichHAMSecondMoment.MaskedModulation.phase
#print axioms StratonovichHAMSecondMoment.MaskedModulation.phase
#check @StratonovichHAMSecondMoment.MaskedModulation.norm_phase
#print axioms StratonovichHAMSecondMoment.MaskedModulation.norm_phase
#check @StratonovichHAMSecondMoment.MaskedModulation.continuous_phase
#print axioms StratonovichHAMSecondMoment.MaskedModulation.continuous_phase
#check @StratonovichHAMSecondMoment.MaskedModulation.phase_add
#print axioms StratonovichHAMSecondMoment.MaskedModulation.phase_add
#check @StratonovichHAMSecondMoment.MaskedModulation.osc_bound
#print axioms StratonovichHAMSecondMoment.MaskedModulation.osc_bound
#check @StratonovichHAMSecondMoment.MaskedModulation.acorr
#print axioms StratonovichHAMSecondMoment.MaskedModulation.acorr
#check @StratonovichHAMSecondMoment.MaskedModulation.M_nonneg_of_bound
#print axioms StratonovichHAMSecondMoment.MaskedModulation.M_nonneg_of_bound
#check @StratonovichHAMSecondMoment.MaskedModulation.acorr_integrable
#print axioms StratonovichHAMSecondMoment.MaskedModulation.acorr_integrable
#check @StratonovichHAMSecondMoment.MaskedModulation.acorr_integrand_le
#print axioms StratonovichHAMSecondMoment.MaskedModulation.acorr_integrand_le
#check @StratonovichHAMSecondMoment.MaskedModulation.acorr_bound
#print axioms StratonovichHAMSecondMoment.MaskedModulation.acorr_bound
#check @StratonovichHAMSecondMoment.MaskedModulation.acorr_lip
#print axioms StratonovichHAMSecondMoment.MaskedModulation.acorr_lip
#check @StratonovichHAMSecondMoment.MaskedModulation.acorr_neg
#print axioms StratonovichHAMSecondMoment.MaskedModulation.acorr_neg
#check @StratonovichHAMSecondMoment.MaskedModulation.acorr_bound_abs
#print axioms StratonovichHAMSecondMoment.MaskedModulation.acorr_bound_abs
#check @StratonovichHAMSecondMoment.MaskedModulation.acorr_stronglyMeasurable
#print axioms StratonovichHAMSecondMoment.MaskedModulation.acorr_stronglyMeasurable
#check @StratonovichHAMSecondMoment.MaskedModulation.phase_mul_conj
#print axioms StratonovichHAMSecondMoment.MaskedModulation.phase_mul_conj
#check @StratonovichHAMSecondMoment.MaskedModulation.phase_neg
#print axioms StratonovichHAMSecondMoment.MaskedModulation.phase_neg
#check @StratonovichHAMSecondMoment.MaskedModulation.integrable_kern_indicator
#print axioms StratonovichHAMSecondMoment.MaskedModulation.integrable_kern_indicator
#check @StratonovichHAMSecondMoment.MaskedModulation.shear_integrable
#print axioms StratonovichHAMSecondMoment.MaskedModulation.shear_integrable
#check @StratonovichHAMSecondMoment.MaskedModulation.timeForm_eq_acorr
#print axioms StratonovichHAMSecondMoment.MaskedModulation.timeForm_eq_acorr
#check @StratonovichHAMSecondMoment.MaskedModulation.integral_acorr_split
#print axioms StratonovichHAMSecondMoment.MaskedModulation.integral_acorr_split
#check @StratonovichHAMSecondMoment.MaskedModulation.one_le_bracket
#print axioms StratonovichHAMSecondMoment.MaskedModulation.one_le_bracket
#check @StratonovichHAMSecondMoment.MaskedModulation.constant_small
#print axioms StratonovichHAMSecondMoment.MaskedModulation.constant_small
#check @StratonovichHAMSecondMoment.MaskedModulation.constant_large
#print axioms StratonovichHAMSecondMoment.MaskedModulation.constant_large
#check @StratonovichHAMSecondMoment.MaskedModulation.crude_bound
#print axioms StratonovichHAMSecondMoment.MaskedModulation.crude_bound
#check @StratonovichHAMSecondMoment.MaskedModulation.modeFn_eq_indicator_mul
#print axioms StratonovichHAMSecondMoment.MaskedModulation.modeFn_eq_indicator_mul
#check @StratonovichHAMSecondMoment.MaskedModulation.modulation_bound
#print axioms StratonovichHAMSecondMoment.MaskedModulation.modulation_bound
#check @StratonovichHAMSecondMoment.MaskedModulation.envelope_of_contDiffOn
#print axioms StratonovichHAMSecondMoment.MaskedModulation.envelope_of_contDiffOn
#check @StratonovichHAMSecondMoment.MaskedModulation.memLp_modeFn
#print axioms StratonovichHAMSecondMoment.MaskedModulation.memLp_modeFn
#check @StratonovichHAMSecondMoment.MaskedModulation.masked_temporal_modulation_paper
#print axioms StratonovichHAMSecondMoment.MaskedModulation.masked_temporal_modulation_paper
#check @StratonovichHAMSecondMoment.MaskedModulation.masked_trig_products_bridged_paper
#print axioms StratonovichHAMSecondMoment.MaskedModulation.masked_trig_products_bridged_paper
open MeasureTheory Set in
open scoped ComplexConjugate in
/-- Consumer of `masked_temporal_modulation_paper`: the real part of the
complexified form (the quantity identified with `‖1_I A e^{iωt}‖_a²` by the
complexification clause) obeys the manuscript's modulation bound. -/
theorem modulation_re_consumer (a T s h : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hT : 0 < T)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs : 0 ≤ s) (hsT : s + h ≤ T)
    (A : ℝ → ℂ) (hA : ContDiffOn ℝ 1 A (Icc s (s + h))) (ω : ℝ) :
    (StratonovichHAMSecondMoment.TimeSchur.timeForm a T
        (StratonovichHAMSecondMoment.MaskedTrigProducts.modeFn (Icc s (s + h)) A ω)
        (StratonovichHAMSecondMoment.MaskedTrigProducts.modeFn (Icc s (s + h)) A ω)).re ≤
      StratonovichHAMSecondMoment.MaskedTrigProducts.C₀ a * h ^ (2 - a) *
        (sSup ((fun t => ‖A t‖) '' Icc s (s + h)) +
          h * sSup ((fun t => ‖derivWithin A (Icc s (s + h)) t‖) '' Icc s (s + h))) ^ 2 *
        StratonovichHAMSecondMoment.MaskedTrigProducts.bracket (h * ω) ^ (a - 1) :=
  (Complex.re_le_norm _).trans
    (StratonovichHAMSecondMoment.MaskedModulation.masked_temporal_modulation_paper a T s h
      ha0 ha1 hT hh0 hh1 hs hsT A hA _ _ rfl rfl ω).2
#check @modulation_re_consumer
#print axioms modulation_re_consumer
open MeasureTheory Set in
example : ∫ t in Icc (0 : ℝ) 1, ∫ s in Icc (0 : ℝ) 1,
      (1 : ℝ) * 1 * |t - s| ^ (-(1 / 2 : ℝ)) ≤
    2 * (1 : ℝ) ^ (1 - (1 / 2 : ℝ)) / (1 - 1 / 2) * ∫ _ in Icc (0 : ℝ) 1, (1 : ℝ) ^ 2 :=
  (StratonovichHAMSecondMoment.TimeSchur.time_schur_paper (f := fun _ => (1 : ℝ))
    (by norm_num) (by norm_num) one_pos (memLp_const 1)).2
