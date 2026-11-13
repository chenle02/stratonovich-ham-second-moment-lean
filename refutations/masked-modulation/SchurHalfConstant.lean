/-
Refutation for `StratonovichHAMSecondMoment.TimeSchur.time_schur_paper`
(`E:masked-time-schur`, TeX lines 150-152).

Wrong variant: the Schur bound with half the constant,
`∫∫ f(t) f(s) |t-s|^{-a} ≤ (T^{1-a}/(1-a)) ∫ f²`, in the binder shape of
`time_schur_paper`. Witness `a = 1/2`, `T = 1`, `f = 1`: the double integral
is `2/((1-a)(2-a)) = 8/3` (computed below from `integral_row`), the variant's
right side is `2`. No junk value is involved: `integral_row` proves the inner
integrability, and the outer integrand is continuous on `[0,1]`. The contrast
theorem applies `time_schur_paper` at the same point (right side `4`).

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.TimeSchur

set_option autoImplicit false

namespace Refutations.TimeSchur

open MeasureTheory Set StratonovichHAMSecondMoment.TimeSchur

/-- Helper (refutation-local): `∫_0^1 ∫_0^1 |t-s|^{-a} ds dt = 2/((1-a)(2-a))`. -/
theorem double_kern_unit {a : ℝ} (ha1 : a < 1) :
    ∫ t in Icc (0 : ℝ) 1, ∫ s in Icc (0 : ℝ) 1, kern a (t - s) = 2 / ((1 - a) * (2 - a)) := by
  have hr : -1 < 1 - a := by linarith
  have h1a : 0 < 1 - a := by linarith
  rw [setIntegral_congr_fun measurableSet_Icc (fun t ht => (integral_row ha1 ht).2),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_div,
    intervalIntegral.integral_add (intervalIntegral.intervalIntegrable_rpow' hr)
      (by simpa using (intervalIntegral.intervalIntegrable_rpow' (a := 1) (b := 0) hr).comp_sub_left 1),
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (1 - a)), integral_rpow (Or.inl hr)]
  simp only [sub_zero, sub_self, Real.one_rpow, Real.zero_rpow (by linarith : 1 - a + 1 ≠ 0)]
  rw [intervalIntegral.integral_symm, integral_rpow (Or.inl hr)]
  simp only [Real.one_rpow, Real.zero_rpow (by linarith : 1 - a + 1 ≠ 0)]
  have : 1 - a + 1 = 2 - a := by ring
  rw [this]
  field_simp
  ring

/-- The Schur bound with half the constant is false. -/
theorem schur_half_constant :
    ¬ ∀ (a T : ℝ) (f : ℝ → ℝ), 0 < a → a < 1 → 0 < T →
      MemLp f 2 (volume.restrict (Icc 0 T)) →
      ∫ t in Icc 0 T, ∫ s in Icc 0 T, f t * f s * |t - s| ^ (-a) ≤
        T ^ (1 - a) / (1 - a) * ∫ t in Icc 0 T, f t ^ 2 := by
  intro h
  have h1 := h (1 / 2) 1 (fun _ => 1) (by norm_num) (by norm_num) one_pos (memLp_const 1)
  have e := double_kern_unit (a := 1 / 2) (by norm_num)
  simp only [kern] at e
  simp only [one_mul, one_pow, integral_const, smul_eq_mul, mul_one, Real.one_rpow,
    measureReal_restrict_apply_univ, Real.volume_real_Icc] at h1
  rw [e] at h1
  norm_num at h1

/-- Contrast: `time_schur_paper` at the counterexample point. -/
theorem schur_half_constant_contrast :
    Integrable (fun p : ℝ × ℝ => (fun _ => (1 : ℝ)) p.1 * (fun _ => (1 : ℝ)) p.2 *
        |p.1 - p.2| ^ (-(1 / 2 : ℝ)))
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1))) ∧
      ∫ t in Icc (0 : ℝ) 1, ∫ s in Icc (0 : ℝ) 1,
          (fun _ => (1 : ℝ)) t * (fun _ => (1 : ℝ)) s * |t - s| ^ (-(1 / 2 : ℝ)) ≤
        2 * (1 : ℝ) ^ (1 - (1 / 2 : ℝ)) / (1 - 1 / 2) *
          ∫ t in Icc (0 : ℝ) 1, (fun _ => (1 : ℝ)) t ^ 2 :=
  time_schur_paper (by norm_num) (by norm_num) one_pos _ (memLp_const 1)

end Refutations.TimeSchur
