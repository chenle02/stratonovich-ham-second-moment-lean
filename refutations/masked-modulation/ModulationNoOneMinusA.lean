/-
Refutation for `StratonovichHAMSecondMoment.MaskedModulation.modulation_bound`
(`L:masked-temporal-modulation`, TeX lines 300-309).

Wrong variant: the modulation bound with the `a`-free constant `16` in place
of `C₀(a) = 16/(1-a)`, in the binder shape of `modulation_bound`. Witness
`a = 19/20`, `T = 1`, `s = 0`, `h = 1`, `A = 1`, `M = 1`, `D = 0`, `ω = 0`: the
double integral is `∫_0^1 ∫_0^1 |t-s|^{-a} = 2/((1-a)(2-a)) = 800/21 > 16`
(computed below from `TimeSchur.integral_row`). So the factor `1/(1-a)` is
necessary. No junk value is involved: the inner integrand is integrable by
`integral_row`, and the outer one is continuous on `[0,1]`. The contrast
theorem applies `modulation_bound` at the same point.

Expected outcome: compiles (refuted).
-/
import StratonovichHAMSecondMoment.MaskedModulation

set_option autoImplicit false

namespace Refutations.MaskedModulation

open MeasureTheory Set StratonovichHAMSecondMoment.TimeSchur
  StratonovichHAMSecondMoment.MaskedTrigProducts StratonovichHAMSecondMoment.MaskedModulation
open scoped ComplexConjugate

/-- Helper (refutation-local): `∫_0^1 ∫_0^1 |t-s|^{-a} ds dt = 2/((1-a)(2-a))`. -/
theorem double_kern_unit' {a : ℝ} (ha1 : a < 1) :
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

/-- Helper: the form of the unit mode on `[0,1]` is the real double integral. -/
theorem timeForm_unit (a : ℝ) :
    timeForm a 1 (modeFn (Icc 0 (0 + 1)) (fun _ => (1 : ℂ)) 0)
        (modeFn (Icc 0 (0 + 1)) (fun _ => (1 : ℂ)) 0) =
      ((∫ t in Icc (0 : ℝ) 1, ∫ s in Icc (0 : ℝ) 1, kern a (t - s) : ℝ) : ℂ) := by
  have hm : ∀ t ∈ Icc (0 : ℝ) 1, modeFn (Icc 0 (0 + 1)) (fun _ => (1 : ℂ)) 0 t = 1 := by
    intro t ht
    rw [zero_add]
    simp [modeFn, indicator_of_mem ht]
  unfold timeForm
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Icc (fun s hs => ?_)
  simp only [hm t ht, hm s hs, map_one, one_mul]

/-- The modulation bound with the `a`-free constant `16` is false. -/
theorem modulation_no_one_minus_a :
    ¬ ∀ (a T s h : ℝ) (A : ℝ → ℂ) (M D ω : ℝ), 0 < a → a < 1 → 0 < h → 0 ≤ s →
      s + h ≤ T → ContinuousOn A (Icc s (s + h)) → (∀ u ∈ Icc s (s + h), ‖A u‖ ≤ M) →
      (∀ x ∈ Icc s (s + h), ∀ y ∈ Icc s (s + h), ‖A x - A y‖ ≤ D * |x - y|) →
      ‖timeForm a T (modeFn (Icc s (s + h)) A ω) (modeFn (Icc s (s + h)) A ω)‖ ≤
        16 * h ^ (2 - a) * (M + h * D) ^ 2 * bracket (h * ω) ^ (a - 1) := by
  intro hv
  have h1 := hv (19 / 20) 1 0 1 (fun _ => 1) 1 0 0 (by norm_num) (by norm_num) one_pos le_rfl
    (by norm_num) continuousOn_const (fun _ _ => by simp) (fun _ _ _ _ => by simp)
  rw [timeForm_unit, double_kern_unit' (by norm_num)] at h1
  simp only [bracket, mul_zero, Real.one_rpow] at h1
  norm_num at h1

/-- Contrast: `modulation_bound` at the counterexample point (constant
`C₀(19/20) = 320`). -/
theorem modulation_no_one_minus_a_contrast :
    ‖timeForm (19 / 20) 1 (modeFn (Icc 0 (0 + 1)) (fun _ => (1 : ℂ)) 0)
        (modeFn (Icc 0 (0 + 1)) (fun _ => (1 : ℂ)) 0)‖ ≤
      C₀ (19 / 20) * 1 ^ (2 - (19 / 20 : ℝ)) * (1 + 1 * 0) ^ 2 * bracket (1 * 0) ^ ((19 / 20 : ℝ) - 1) :=
  (modulation_bound (T := 1) (by norm_num) (by norm_num) one_pos le_rfl (by norm_num)
    (fun _ => (1 : ℂ)) continuousOn_const 1 0 (fun _ _ => by simp) (fun _ _ _ _ => by simp) 0).2

end Refutations.MaskedModulation
