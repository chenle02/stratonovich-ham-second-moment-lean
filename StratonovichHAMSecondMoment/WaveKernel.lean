module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The Fourier transform of the wave kernel, from the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` (revision a284420),
Section "Recovering the quadratic-exponential bound" (lines 775-796) and the
proof of `L:damped-homogeneous-norms` (lines 803-919).

`Ĝ_s(ξ) = sin(s|ξ|)/|ξ|` with value `s` at `ξ = 0` (lines 777-778) is defined as
`waveHat s ξ = s · sinc(s|ξ|)`, which is that function for every `ξ`
(`waveHat_of_ne_zero`, `waveHat_zero`); it is real, so the complex conjugate
in `E:damped-norm-definitions` acts trivially.

Formalized (all proved, no supplied input):
* the bounds `|Ĝ_s(ξ)| ≤ |s|` and `|Ĝ_s(ξ)| ≤ |ξ|⁻¹` (`ξ ≠ 0`), i.e. the
  bound `|Ĝ_s(ξ)| ≤ min(s, |ξ|⁻¹)` used at line 866;
* the scaling `Ĝ_{u/θ}(θη) = θ⁻¹ Ĝ_u(η)` (line 884);
* the elementary wave Laplace transform
  `∫_0^∞ e^{-as} Ĝ_s(ξ) ds = (a²+|ξ|²)⁻¹`, `a > 0` (lines 794-795), with
  integrability of the integrand.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.TimeFractional

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter

namespace StratonovichHAMSecondMoment.WaveKernel

open HomogHypothesis TimeFractional

variable {d : ℕ}

/-- `Ĝ_s(ξ) = sin(s|ξ|)/|ξ|`, with value `s` at `ξ = 0` (lines 777-778). -/
def waveHat (s : ℝ) (ξ : Rd d) : ℝ := s * Real.sinc (s * ‖ξ‖)

/-- Auxiliary to the Lean proof route. -/
theorem waveHat_continuous : Continuous fun z : ℝ × Rd d => waveHat z.1 z.2 := by
  unfold waveHat
  have := Real.continuous_sinc
  fun_prop

/-- Auxiliary to the Lean proof route. -/
theorem waveHat_zero (s : ℝ) : waveHat s (0 : Rd d) = s := by
  simp [waveHat]

/-- Auxiliary to the Lean proof route. -/
theorem waveHat_of_ne_zero (s : ℝ) (ξ : Rd d) (hξ : ξ ≠ 0) :
    waveHat s ξ = Real.sin (s * ‖ξ‖) / ‖ξ‖ := by
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
  by_cases hs : s = 0
  · simp [waveHat, hs]
  · rw [waveHat, Real.sinc_of_ne_zero (mul_ne_zero hs hn)]
    field_simp

/-- `|Ĝ_s(ξ)| ≤ |s|`. -/
theorem abs_waveHat_le (s : ℝ) (ξ : Rd d) : |waveHat s ξ| ≤ |s| := by
  rw [waveHat, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sinc_le_one _)

/-- `|Ĝ_s(ξ)| ≤ |ξ|⁻¹` for `ξ ≠ 0`. -/
theorem abs_waveHat_le_inv (s : ℝ) (ξ : Rd d) (hξ : ξ ≠ 0) :
    |waveHat s ξ| ≤ 1 / ‖ξ‖ := by
  rw [waveHat_of_ne_zero s ξ hξ, abs_div, abs_norm]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (norm_nonneg _)

/-- `|Ĝ_s(ξ)| ≤ min(s, |ξ|⁻¹)` for `s ≥ 0`, `ξ ≠ 0` (line 866). -/
theorem abs_waveHat_le_min (s : ℝ) (hs : 0 ≤ s) (ξ : Rd d) (hξ : ξ ≠ 0) :
    |waveHat s ξ| ≤ min s (1 / ‖ξ‖) :=
  le_min ((abs_waveHat_le s ξ).trans (abs_of_nonneg hs).le) (abs_waveHat_le_inv s ξ hξ)

/-- The scaling `Ĝ_{u/θ}(θη) = θ⁻¹ Ĝ_u(η)` for `θ > 0` (line 884). -/
theorem waveHat_scaling (u θ : ℝ) (hθ : 0 < θ) (η : Rd d) :
    waveHat (u / θ) (θ • η) = θ⁻¹ * waveHat u η := by
  simp only [waveHat, norm_smul, Real.norm_eq_abs, abs_of_pos hθ]
  have : u / θ * (θ * ‖η‖) = u * ‖η‖ := by field_simp
  rw [this]
  ring

/-- Auxiliary to the Lean proof route. A product bound used for absolute integrability:
`|Ĝ_s(ξ) Ĝ_t(ξ)| ≤ 2 (1+|s|)(1+|t|) (1+|ξ|²)⁻¹`. -/
theorem abs_waveHat_mul_le (s t : ℝ) (ξ : Rd d) :
    |waveHat s ξ * waveHat t ξ| ≤ 2 * (1 + |s|) * (1 + |t|) * (1 / (1 + ‖ξ‖ ^ 2)) := by
  rw [abs_mul]
  have hs := abs_waveHat_le s ξ
  have ht := abs_waveHat_le t ξ
  have hp : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hA : 1 ≤ (1 + |s|) * (1 + |t|) := by
    nlinarith [abs_nonneg s, abs_nonneg t]
  rw [mul_one_div, le_div_iff₀ hp]
  rcases le_or_gt ‖ξ‖ 1 with h1 | h1
  · have h2 : |waveHat s ξ| * |waveHat t ξ| ≤ (1 + |s|) * (1 + |t|) := by
      have := mul_le_mul hs ht (abs_nonneg _) (abs_nonneg _)
      nlinarith [abs_nonneg s, abs_nonneg t]
    have h3 : ‖ξ‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg ξ]
    nlinarith [mul_nonneg (abs_nonneg (waveHat s ξ)) (abs_nonneg (waveHat t ξ))]
  · have hξ : ξ ≠ 0 := by
      intro h; rw [h, norm_zero] at h1; linarith
    have hs' := abs_waveHat_le_inv s ξ hξ
    have ht' := abs_waveHat_le_inv t ξ hξ
    have hn : 0 < ‖ξ‖ := by linarith
    have h2 : |waveHat s ξ| * |waveHat t ξ| * ‖ξ‖ ^ 2 ≤ 1 := by
      have e1 : |waveHat s ξ| * ‖ξ‖ ≤ 1 := by
        rw [le_div_iff₀ hn] at hs'; linarith
      have e2 : |waveHat t ξ| * ‖ξ‖ ≤ 1 := by
        rw [le_div_iff₀ hn] at ht'; linarith
      have := mul_le_mul e1 e2 (by positivity) zero_le_one
      nlinarith
    have h3 : |waveHat s ξ| * |waveHat t ξ| ≤ 1 := by
      have := mul_le_mul hs' ht' (abs_nonneg _) (by positivity)
      have h4 : 1 / ‖ξ‖ * (1 / ‖ξ‖) ≤ 1 := by
        rw [div_mul_div_comm, one_mul, div_le_one (by positivity)]; nlinarith
      linarith
    nlinarith [mul_nonneg (abs_nonneg (waveHat s ξ)) (abs_nonneg (waveHat t ξ))]

/-- The elementary wave Laplace transform (lines 794-795): for `a > 0`,
`s ↦ e^{-as} Ĝ_s(ξ)` is integrable on `(0,∞)` and
`∫_0^∞ e^{-as} Ĝ_s(ξ) ds = (a²+|ξ|²)⁻¹`. -/
theorem waveHat_laplace (a : ℝ) (ha : 0 < a) (ξ : Rd d) :
    Integrable (fun s => Real.exp (-(a * s)) * waveHat s ξ) L0 ∧
      ∫ s in Ioi (0 : ℝ), Real.exp (-(a * s)) * waveHat s ξ = 1 / (a ^ 2 + ‖ξ‖ ^ 2) := by
  have hdom : Integrable (subKernel 2 a) L0 := subKernel_integrable 2 a two_pos ha
  have hmeas : AEStronglyMeasurable (fun s => Real.exp (-(a * s)) * waveHat s ξ) L0 := by
    have : Continuous fun s : ℝ => waveHat s ξ :=
      waveHat_continuous.comp (continuous_id.prodMk continuous_const)
    exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-(a * s)) * waveHat s ξ)
      |>.aestronglyMeasurable
  have hI : Integrable (fun s => Real.exp (-(a * s)) * waveHat s ξ) L0 := by
    refine Integrable.mono' hdom hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
    have hs0 : 0 < s := hs
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs, subKernel,
      show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm s]
    exact mul_le_mul_of_nonneg_left ((abs_waveHat_le s ξ).trans (abs_of_pos hs0).le)
      (Real.exp_pos _).le
  refine ⟨hI, ?_⟩
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [waveHat_zero, norm_zero]
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := a) two_pos ha
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.Gamma_two] at h
    simp only [Real.rpow_one] at h
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun s => s * Real.exp (-(a * s)))
      (fun s _ => mul_comm _ _), h]
    norm_num [Real.rpow_two]
  · set r := ‖ξ‖ with hr
    have hr0 : 0 < r := norm_pos_iff.2 hξ
    have hpt : ∀ s : ℝ, Real.exp (-(a * s)) * waveHat s ξ =
        (Complex.exp ((-(a : ℂ) + (r : ℂ) * Complex.I) * s)).im / r := by
      intro s
      rw [waveHat_of_ne_zero s ξ hξ, Complex.exp_im]
      have h1 : ((-(a : ℂ) + (r : ℂ) * Complex.I) * s).re = -(a * s) := by simp
      have h2 : ((-(a : ℂ) + (r : ℂ) * Complex.I) * s).im = s * r := by simp; ring
      rw [h1, h2, ← hr]
      ring
    simp_rw [hpt]
    have hre : (-(a : ℂ) + (r : ℂ) * Complex.I).re < 0 := by simp; linarith
    have hci : Integrable (fun s : ℝ => Complex.exp ((-(a : ℂ) + (r : ℂ) * Complex.I) * s))
        L0 := integrableOn_exp_mul_complex_Ioi hre 0
    rw [integral_div]
    have him := integral_im hci
    simp only [RCLike.im_to_complex] at him
    rw [him, integral_exp_mul_complex_Ioi hre 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have hden : (-(a : ℂ) + (r : ℂ) * Complex.I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    rw [neg_div, Complex.neg_im, Complex.div_im]
    simp [Complex.normSq_apply]
    field_simp

end StratonovichHAMSecondMoment.WaveKernel
