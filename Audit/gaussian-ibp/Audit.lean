module
import StratonovichHAMSecondMoment.GaussianIBP
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.GaussianIBP.hasDerivAt_stdPDF
#print axioms StratonovichHAMSecondMoment.GaussianIBP.hasDerivAt_stdPDF
#check @StratonovichHAMSecondMoment.GaussianIBP.integrable_gaussian_iff
#print axioms StratonovichHAMSecondMoment.GaussianIBP.integrable_gaussian_iff
#check @StratonovichHAMSecondMoment.GaussianIBP.integral_gaussian_eq
#print axioms StratonovichHAMSecondMoment.GaussianIBP.integral_gaussian_eq
#check @StratonovichHAMSecondMoment.GaussianIBP.integral_mul_eq_integral_deriv
#print axioms StratonovichHAMSecondMoment.GaussianIBP.integral_mul_eq_integral_deriv
#check @StratonovichHAMSecondMoment.GaussianIBP.stdPi
#print axioms StratonovichHAMSecondMoment.GaussianIBP.stdPi
#check @StratonovichHAMSecondMoment.GaussianIBP.isProbabilityMeasure_stdPi
#print axioms StratonovichHAMSecondMoment.GaussianIBP.isProbabilityMeasure_stdPi
#check @StratonovichHAMSecondMoment.GaussianIBP.integral_coord_mul_eq_integral_partial
#print axioms StratonovichHAMSecondMoment.GaussianIBP.integral_coord_mul_eq_integral_partial
#check @StratonovichHAMSecondMoment.GaussianIBP.integrable_one_add_abs_pow
#print axioms StratonovichHAMSecondMoment.GaussianIBP.integrable_one_add_abs_pow
#check @StratonovichHAMSecondMoment.GaussianIBP.one_add_norm_le_prod
#print axioms StratonovichHAMSecondMoment.GaussianIBP.one_add_norm_le_prod
#check @StratonovichHAMSecondMoment.GaussianIBP.integrable_one_add_norm_pow
#print axioms StratonovichHAMSecondMoment.GaussianIBP.integrable_one_add_norm_pow
#check @StratonovichHAMSecondMoment.GaussianIBP.integrable_of_growth
#print axioms StratonovichHAMSecondMoment.GaussianIBP.integrable_of_growth
#check @StratonovichHAMSecondMoment.GaussianIBP.integrable_coord_mul_of_growth
#print axioms StratonovichHAMSecondMoment.GaussianIBP.integrable_coord_mul_of_growth
#check @StratonovichHAMSecondMoment.GaussianIBP.integral_coord_mul_eq_of_growth
#print axioms StratonovichHAMSecondMoment.GaussianIBP.integral_coord_mul_eq_of_growth
#check @StratonovichHAMSecondMoment.GaussianIBP.integrable_pow_gaussian
#print axioms StratonovichHAMSecondMoment.GaussianIBP.integrable_pow_gaussian
#check @StratonovichHAMSecondMoment.GaussianIBP.moment_recursion
#print axioms StratonovichHAMSecondMoment.GaussianIBP.moment_recursion
#check @StratonovichHAMSecondMoment.GaussianIBP.moment_two
#print axioms StratonovichHAMSecondMoment.GaussianIBP.moment_two
#check @StratonovichHAMSecondMoment.GaussianIBP.moment_four
#print axioms StratonovichHAMSecondMoment.GaussianIBP.moment_four
#check @StratonovichHAMSecondMoment.GaussianIBP.map_eq_stdPi
#print axioms StratonovichHAMSecondMoment.GaussianIBP.map_eq_stdPi
#check @StratonovichHAMSecondMoment.GaussianIBP.integral_comp_eq_stdPi
#print axioms StratonovichHAMSecondMoment.GaussianIBP.integral_comp_eq_stdPi
#check @StratonovichHAMSecondMoment.GaussianIBP.integrable_comp_iff_stdPi
#print axioms StratonovichHAMSecondMoment.GaussianIBP.integrable_comp_iff_stdPi
#check @StratonovichHAMSecondMoment.GaussianIBP.integral_coord_mul_eq_of_growth_paper
#print axioms StratonovichHAMSecondMoment.GaussianIBP.integral_coord_mul_eq_of_growth_paper
open MeasureTheory ProbabilityTheory in
/-- Consumer: on a probability space with independent standard Gaussians, the
integration by parts with `f(x) = x_k`, `∂_k f = 1` gives `E g_k^2 = 1`. -/
private theorem second_moment_consumer {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (g : Fin N → Ω → ℝ) (hind : iIndepFun g P)
    (hlaw : ∀ k, HasLaw (g k) (gaussianReal 0 1) P) (k : Fin N) :
    ∫ ω, g k ω * g k ω ∂P = 1 := by
  obtain ⟨-, -, h⟩ :=
    StratonovichHAMSecondMoment.GaussianIBP.integral_coord_mul_eq_of_growth_paper g hind hlaw k
      (fun x => x k) (fun _ => 1)
      (fun x t => by simpa using hasDerivAt_id' t) (continuous_apply k) continuous_const
      (C := 1) (d := 1) (C' := 1) (d' := 0)
      (fun x => by
        have := norm_le_pi_norm x k
        rw [Real.norm_eq_abs] at this
        simp only [pow_one, one_mul]; linarith [norm_nonneg x])
      (fun x => by simp)
  simpa using h
#check @second_moment_consumer
#print axioms second_moment_consumer
open MeasureTheory ProbabilityTheory in
example : ∫ x, x ^ 4 ∂gaussianReal 0 1 = 3 * ∫ x, x ^ 2 ∂gaussianReal 0 1 := by
  rw [StratonovichHAMSecondMoment.GaussianIBP.moment_four,
    StratonovichHAMSecondMoment.GaussianIBP.moment_two]; norm_num
