/-
Refutation for the mass part of `L:temporal-equilibrium` (TeX lines 46--48
and "Its time mass has not been renormalized", line 93), package definition
`StratonovichHAMSecondMoment.TemporalEquilibrium.mass` and package theorem
`StratonovichHAMSecondMoment.TemporalEquilibrium.mass_eq`.

Wrong variant: "`M_a = 1`", i.e. `f_a` is a probability density. The package
mass `mass a = ∫_0^1 f_a` is not 1. Witness: a = 1/2, where `mass_eq` gives
M = Γ(3/4)/(Γ(3/2)Γ(1/4)). Proof: Γ(3/4) ≤ 4/3 (convexity of Γ on [1,2]),
while M = 1 would force Γ(3/4)² = Γ(3/2)·Γ(1/4)Γ(3/4) ≥ (√3/2)·π > 16/9.
This is strictly more faithful than the earlier version, which refuted only
the closed-form value `Γ(3/4)/(Γ(3/2)Γ(1/4)) = 1`; that statement is kept as
`mass_formula_half_ne_one`. `mass_not_identically_one` is the universal
variant `∀ a ∈ (0,1), mass a = 1`.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TemporalEquilibrium

set_option autoImplicit false

open Real

namespace Refutations.TemporalEquilibrium

/-- `Γ(7/4) ≤ 1` by convexity of `Γ` between `1` and `2`. -/
theorem gamma_seven_fourths_le_one : Gamma (7 / 4) ≤ 1 := by
  have h := (convexOn_Gamma).2 (show (1:ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (2:ℝ) ∈ Set.Ioi 0 by norm_num) (show (0:ℝ) ≤ 1 / 4 by norm_num)
    (show (0:ℝ) ≤ 3 / 4 by norm_num) (by norm_num)
  simp only [smul_eq_mul, Gamma_one, Gamma_two] at h
  norm_num at h
  exact h

/-- The closed-form mass at `a = 1/2` is not `1`. -/
theorem mass_formula_half_ne_one :
    ¬ (Gamma ((1 + 1 / 2) / 2) / (Gamma (1 + 1 / 2) * Gamma ((1 - 1 / 2) / 2)) = 1) := by
  intro h
  have e1 : (1 + 1 / 2 : ℝ) / 2 = 3 / 4 := by norm_num
  have e2 : (1 - 1 / 2 : ℝ) / 2 = 1 / 4 := by norm_num
  have e3 : (1 + 1 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
  rw [e1, e2, e3, Gamma_add_one (by norm_num), Gamma_one_half_eq] at h
  have hA : 0 < Gamma (3 / 4) := Gamma_pos_of_pos (by norm_num)
  have hB : 0 < Gamma (1 / 4) := Gamma_pos_of_pos (by norm_num)
  have hrec : Gamma (3 / 4 + 1) = 3 / 4 * Gamma (3 / 4) := Gamma_add_one (by norm_num)
  have hle : Gamma (3 / 4) ≤ 4 / 3 := by
    have := gamma_seven_fourths_le_one
    norm_num at hrec
    nlinarith
  have hrefl := Gamma_mul_Gamma_one_sub (1 / 4)
  have e4 : (1 : ℝ) - 1 / 4 = 3 / 4 := by norm_num
  rw [e4] at hrefl
  have hsin_pos : 0 < sin (π * (1 / 4)) :=
    sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])
  have hsin_le : sin (π * (1 / 4)) ≤ 1 := sin_le_one _
  have hAB : π ≤ Gamma (1 / 4) * Gamma (3 / 4) := by
    rw [hrefl, le_div_iff₀ hsin_pos]; nlinarith [pi_pos]
  have hsq : √3 ≤ √π := sqrt_le_sqrt (by linarith [pi_gt_three])
  have h3 : (1.7 : ℝ) ≤ √3 := by
    rw [le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : 0 < 1 / 2 * √π := by positivity
  rw [div_eq_one_iff_eq (by positivity)] at h
  -- h : Γ(3/4) = (1/2 √π) Γ(1/4)
  have : Gamma (3 / 4) ^ 2 = 1 / 2 * √π * (Gamma (1 / 4) * Gamma (3 / 4)) := by
    rw [sq]; nth_rewrite 1 [h]; ring
  nlinarith [pi_gt_three, mul_le_mul_of_nonneg_left hAB hC.le]

/-- The package mass `M_{1/2} = ∫_0^1 f_{1/2}` is not `1`. -/
theorem mass_half_ne_one :
    ¬ (StratonovichHAMSecondMoment.TemporalEquilibrium.mass (1 / 2) = 1) := by
  intro h
  rw [(StratonovichHAMSecondMoment.TemporalEquilibrium.mass_eq
    (by norm_num) (by norm_num)).2] at h
  exact mass_formula_half_ne_one h

/-- `f_a` is not a probability density for every `a ∈ (0,1)`. -/
theorem mass_not_identically_one :
    ¬ ∀ a : ℝ, 0 < a → a < 1 → StratonovichHAMSecondMoment.TemporalEquilibrium.mass a = 1 :=
  fun h => mass_half_ne_one (h (1 / 2) (by norm_num) (by norm_num))

end Refutations.TemporalEquilibrium
