/-
Refutation for the potential identity of `L:temporal-equilibrium` (TeX lines
40 and 44--45), package theorem
`StratonovichHAMSecondMoment.TemporalEquilibrium.potential_eq_one` and
package definition `StratonovichHAMSecondMoment.TemporalEquilibrium.density`.

Wrong variant: the normalizer Γ(r)Γ(1-r) of `density` replaced by Γ(r)². At
a = 1/2 (r = 1/4) and s = 0 the potential of the wrongly normalized density is
∫_0^1 t^{-1/2}[t(1-t)]^{-1/4} dt / Γ(1/4)² = Beta(1/4,3/4)/Γ(1/4)²
= Γ(3/4)/Γ(1/4) ≠ 1 (Γ(3/4) ≤ 4/3 < 9/4 ≤ Γ(1/4)). The wrongly normalized
density is not a package definition, so it is written out; the Beta integral
uses the package's `betaKernel` and `Beta_eq_Gamma` (earlier local copies
removed). The contrast theorem applies `potential_eq_one` at the same point
`a = 1/2`, `s = 0`, where the correctly normalized package density has
potential 1.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TemporalEquilibrium

set_option autoImplicit false

open MeasureTheory Set Real

namespace Refutations.TemporalEquilibrium

/-- `Γ(7/4) ≤ 1` by convexity of `Γ` between `1` and `2`. -/
theorem gamma_seven_fourths_le_one_aux : Gamma (7 / 4) ≤ 1 := by
  have h := (convexOn_Gamma).2 (show (1:ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (2:ℝ) ∈ Set.Ioi 0 by norm_num) (show (0:ℝ) ≤ 1 / 4 by norm_num)
    (show (0:ℝ) ≤ 3 / 4 by norm_num) (by norm_num)
  simp only [smul_eq_mul, Gamma_one, Gamma_two] at h
  norm_num at h
  exact h

/-- With normalizer `Γ(r)²` instead of `Γ(r)Γ(1-r)`, the potential at
`a = 1/2`, `s = 0` is not `1`. -/
theorem wrong_normalization :
    ¬ (∫ t in Ioo (0:ℝ) 1, |0 - t| ^ (-(1 / 2 : ℝ)) *
      ((t * (1 - t)) ^ (-((1 - 1 / 2) / 2 : ℝ)) /
        (Gamma ((1 - 1 / 2) / 2) * Gamma ((1 - 1 / 2) / 2))) = 1) := by
  intro h
  have hcongr : ∀ t ∈ Ioo (0:ℝ) 1, |0 - t| ^ (-(1 / 2 : ℝ)) *
      ((t * (1 - t)) ^ (-((1 - 1 / 2) / 2 : ℝ)) /
        (Gamma ((1 - 1 / 2) / 2) * Gamma ((1 - 1 / 2) / 2)))
      = StratonovichHAMSecondMoment.TemporalEquilibrium.betaKernel (1 / 4) (3 / 4) t /
          (Gamma (1 / 4) * Gamma (1 / 4)) := by
    intro t ht
    have ht0 := ht.1
    have ht1 : 0 < 1 - t := by linarith [ht.2]
    rw [zero_sub, abs_neg, abs_of_pos ht0, mul_rpow ht0.le ht1.le,
      StratonovichHAMSecondMoment.TemporalEquilibrium.betaKernel]
    have e : (1 - 1 / 2 : ℝ) / 2 = 1 / 4 := by norm_num
    rw [e, mul_div_assoc', ← mul_assoc, ← rpow_add ht0]
    norm_num
  have hBeta : ∫ t in Ioo (0:ℝ) 1,
      StratonovichHAMSecondMoment.TemporalEquilibrium.betaKernel (1 / 4) (3 / 4) t
        = Gamma (1 / 4) * Gamma (3 / 4) / Gamma (1 / 4 + 3 / 4) :=
    StratonovichHAMSecondMoment.TemporalEquilibrium.Beta_eq_Gamma (by norm_num) (by norm_num)
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr, integral_div, hBeta] at h
  norm_num [Gamma_one] at h
  have hA : 0 < Gamma (3 / 4) := Gamma_pos_of_pos (by norm_num)
  have hB : 0 < Gamma (1 / 4) := Gamma_pos_of_pos (by norm_num)
  have hrec : Gamma (3 / 4 + 1) = 3 / 4 * Gamma (3 / 4) := Gamma_add_one (by norm_num)
  have hle : Gamma (3 / 4) ≤ 4 / 3 := by
    have := gamma_seven_fourths_le_one_aux
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
  field_simp at h
  nlinarith [pi_gt_three]

/-- Contrast: with the package normalizer `Γ(r)Γ(1-r)` (the package
`density`), `potential_eq_one` gives potential `1` at `a = 1/2`, `s = 0`. -/
theorem wrong_normalization_contrast :
    ∫ t in Ioo (0:ℝ) 1, |0 - t| ^ (-(1 / 2 : ℝ)) *
      StratonovichHAMSecondMoment.TemporalEquilibrium.density (1 / 2) t = 1 :=
  (StratonovichHAMSecondMoment.TemporalEquilibrium.potential_eq_one (a := 1 / 2)
    (by norm_num) (by norm_num) 0 ⟨le_rfl, zero_le_one⟩).2

end Refutations.TemporalEquilibrium
