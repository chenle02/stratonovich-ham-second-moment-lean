module
import StratonovichHAMSecondMoment.GaussianScalarPowers
set_option autoImplicit false
set_option pp.all true
#check @StratonovichHAMSecondMoment.GaussianScalarPowers.weighted_power
#print axioms StratonovichHAMSecondMoment.GaussianScalarPowers.weighted_power
#check @StratonovichHAMSecondMoment.GaussianScalarPowers.integer_power
#print axioms StratonovichHAMSecondMoment.GaussianScalarPowers.integer_power
#check @StratonovichHAMSecondMoment.GaussianScalarPowers.finite_holder
#print axioms StratonovichHAMSecondMoment.GaussianScalarPowers.finite_holder
#check @StratonovichHAMSecondMoment.GaussianScalarPowers.expectation_rpow_le
#print axioms StratonovichHAMSecondMoment.GaussianScalarPowers.expectation_rpow_le
open MeasureTheory in
/-- Consumer: part (4) at `r = 1/2`, the usual downstream form
`𝔼 √Z ≤ √(𝔼 Z)` for an integrable `Z ≥ 0` on a probability space. -/
private theorem sqrt_moment_consumer {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : Integrable Z μ) (hZnn : 0 ≤ᵐ[μ] Z) :
    ∫ ω, Z ω ^ (1 / 2 : ℝ) ∂μ ≤ Real.sqrt (∫ ω, Z ω ∂μ) := by
  rw [Real.sqrt_eq_rpow]
  exact (StratonovichHAMSecondMoment.GaussianScalarPowers.expectation_rpow_le μ Z hZ hZnn
    (1 / 2) (by norm_num) (by norm_num)).2
#check @sqrt_moment_consumer
#print axioms sqrt_moment_consumer
open MeasureTheory in
example : ∫ _ω, (4 : ℝ) ^ (1 / 2 : ℝ) ∂(Measure.dirac ()) ≤
    Real.sqrt (∫ _ω, (4 : ℝ) ∂(Measure.dirac ())) :=
  sqrt_moment_consumer (Ω := Unit) (Measure.dirac ()) (fun _ => 4) (integrable_const _)
    (Filter.Eventually.of_forall fun _ => by simp)
example : |(1 : ℝ)| ^ 1 * |(2 : ℝ)| ^ (2 - 1) ≤
    ((1 : ℕ) : ℝ) / (2 : ℕ) * |(1 : ℝ)| ^ 2 + (((2 : ℕ) : ℝ) - (1 : ℕ)) / (2 : ℕ) * |(2 : ℝ)| ^ 2 :=
  StratonovichHAMSecondMoment.GaussianScalarPowers.integer_power 2 1 (by norm_num) (by norm_num) 1 2
