module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, item L17-E3 (approved by Le on 2026-11-20 as a time-boxed item), part 1: a density for
the Green-smoothed `d = 3` wave kernel `G_{s,η} = p_η * G_s` (`LowAlphaConvolution.smoothedGreen
(waveGreen 3) s η`, `p_η = gaussKernel η = N(0, ηI)`), main TeX lines 2023-2026 (the Green
smoothing in Step 1 of `L:crude-corrected`) and 2397-2403 (the `d = 3` limit `η ↓ 0` in Step 1
of the proof of `P:envelope`) at revision edf7085f (book 1.1.3).

Formalized (all proved, nothing supplied):
* `gaussKernel_eq_withDensity`: for `η > 0`, `gaussKernel η = p_η(x) dx` with the heat density
  `LowAlphaConvolution.heatDens η` (Fourier uniqueness, `Measure.ext_of_charFun`, and the
  Gaussian Fourier integral `integral_cexp_neg_mul_sq_norm_add`), in every dimension;
* `withDensity_conv`: `(p dx) * ν = (∫ p(z - y) ν(dy)) dz` for a measurable `p` and s-finite `ν`;
* `green3s η s z = ∫ p_η(z - y) G_s(dy)`, the density of `G_{s,η}` (`smoothedGreen_three_eq`),
  jointly measurable in `(s, z)` (`measurable_green3s`, through the sphere form of `waveGreen 3`)
  and finite (`green3s_ne_top`: `p_η ≤ (2πη)^{-3/2}` and `G_s` is finite);
* the mass `G_{s,η}(ℝ³) = s` (`smoothedGreen_three_mass`) and the transform
  `Ĝ_{s,η}(ξ) = e^{-η|ξ|²/2} sin(s|ξ|)/|ξ|` (`charFun_smoothedGreen_three`).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.PairingDampedNorms

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal Real

namespace StratonovichHAMSecondMoment.GreenSmoothed3

open HomogHypothesis (Rd)
open LowAlphaConvolution (heatDens smoothedGreen gaussFactor)
open DampedMultiplier (gaussKernel)
open WaveGreen (waveGreen)
open WaveKernel (waveHat)

variable {d : ℕ}

/-! ### The heat density of `gaussKernel` -/

theorem heatDens_eq {η : ℝ} (x : Rd d) :
    heatDens η x = (2 * π * η) ^ (-((d : ℝ) / 2)) * Real.exp (-(1 / (2 * η)) * ‖x‖ ^ 2) := by
  unfold heatDens; congr 2; ring

theorem heatDens_le {η : ℝ} (hη : 0 < η) (x : Rd d) :
    heatDens η x ≤ (2 * π * η) ^ (-((d : ℝ) / 2)) := by
  rw [heatDens_eq]
  have h1 : Real.exp (-(1 / (2 * η)) * ‖x‖ ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have : 0 ≤ 1 / (2 * η) * ‖x‖ ^ 2 := by positivity
                              linarith)
  calc (2 * π * η) ^ (-((d : ℝ) / 2)) * Real.exp (-(1 / (2 * η)) * ‖x‖ ^ 2)
      ≤ (2 * π * η) ^ (-((d : ℝ) / 2)) * 1 :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (by positivity) _)
    _ = _ := mul_one _

theorem measurable_heatDens (η : ℝ) : Measurable (heatDens (d := d) η) := by
  unfold heatDens; fun_prop

theorem integrable_heatDens {η : ℝ} (hη : 0 < η) : Integrable (heatDens (d := d) η) := by
  have hb : 0 < ((1 / (2 * η) : ℝ) : ℂ).re := by simp; positivity
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : Rd d)).norm.const_mul
    ((2 * π * η) ^ (-((d : ℝ) / 2)))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [zero_mul, add_zero]
  rw [heatDens_eq, Complex.norm_exp]
  congr 2
  simp [← Complex.ofReal_pow]

/-- **`p_η` is the density of `gaussKernel η`** for `η > 0`. -/
theorem gaussKernel_eq_withDensity {η : ℝ} (hη : 0 < η) :
    gaussKernel (d := d) η = volume.withDensity fun x => ENNReal.ofReal (heatDens η x) := by
  have hI := integrable_heatDens (d := d) hη
  have : IsFiniteMeasure (volume.withDensity fun x : Rd d => ENNReal.ofReal (heatDens η x)) :=
    isFiniteMeasure_withDensity_ofReal hI.2
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  rw [DampedMultiplier.charFun_gaussKernel η hη.le, charFun_apply,
    integral_withDensity_eq_integral_toReal_smul (measurable_heatDens η).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  set B : ℂ := ((1 / (2 * η) : ℝ) : ℂ) with hB
  have hb : 0 < B.re := by simp [hB]; positivity
  have hpt : ∀ x : Rd d, (ENNReal.ofReal (heatDens η x)).toReal •
      Complex.exp ((inner ℝ x ξ : ℝ) * Complex.I) =
      (((2 * π * η) ^ (-((d : ℝ) / 2)) : ℝ) : ℂ) *
        Complex.exp (-B * (‖x‖ : ℂ) ^ 2 + Complex.I * (inner ℝ ξ x : ℝ)) := by
    intro x
    rw [ENNReal.toReal_ofReal (LowAlphaConvolution.heatDens_nonneg hη.le x), heatDens_eq,
      Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc, ← Complex.exp_add,
      real_inner_comm]
    congr 2
    rw [hB]; push_cast; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb Complex.I ξ, finrank_euclideanSpace_fin]
  have hπB : (π : ℂ) / B = ((2 * π * η : ℝ) : ℂ) := by
    rw [hB]; push_cast; field_simp
  have hcp : ((π : ℂ) / B) ^ ((d : ℂ) / 2) = (((2 * π * η) ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [hπB, Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  rw [hcp, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (by positivity), neg_add_cancel,
    Real.rpow_zero, Complex.ofReal_one, one_mul]
  congr 1
  rw [hB, Complex.I_sq]
  push_cast
  field_simp
  ring

/-! ### Convolution with a density -/

/-- `(p dx) * ν = (∫ p(z - y) ν(dy)) dz`. -/
theorem withDensity_conv {p : Rd d → ℝ≥0∞} (hp : Measurable p) (ν : Measure (Rd d))
    [SFinite ν] :
    (volume.withDensity p) ∗ ν = volume.withDensity fun z => ∫⁻ y, p (z - y) ∂ν := by
  have hm2 : Measurable fun q : Rd d × Rd d => p (q.1 - q.2) := hp.comp (by fun_prop)
  ext A hA
  have hin : Measurable fun q : Rd d × Rd d => ((fun x : Rd d × Rd d => x.1 + x.2) ⁻¹' A).indicator
      (1 : Rd d × Rd d → ℝ≥0∞) q := measurable_const.indicator (measurable_add hA)
  rw [Measure.conv, Measure.map_apply measurable_add hA, withDensity_apply _ hA,
    ← lintegral_indicator_one (measurable_add hA), lintegral_prod _ hin.aemeasurable]
  rw [lintegral_lintegral_swap hin.aemeasurable]
  have step : ∀ y : Rd d,
      ∫⁻ x, ((fun x : Rd d × Rd d => x.1 + x.2) ⁻¹' A).indicator 1 (x, y) ∂volume.withDensity p =
        ∫⁻ z, A.indicator 1 z * p (z - y) := by
    intro y
    have hy : Measurable fun x : Rd d =>
        ((fun x : Rd d × Rd d => x.1 + x.2) ⁻¹' A).indicator 1 (x, y) :=
      hin.comp (f := fun x : Rd d => (x, y)) (by fun_prop)
    rw [lintegral_withDensity_eq_lintegral_mul _ hp hy]
    refine (lintegral_sub_right_eq_self (μ := (volume : Measure (Rd d)))
      (fun x : Rd d => p x * ((fun x : Rd d × Rd d => x.1 + x.2) ⁻¹' A).indicator 1 (x, y))
      y).symm.trans ?_
    refine lintegral_congr fun z => ?_
    show p (z - y) * ((fun x : Rd d × Rd d => x.1 + x.2) ⁻¹' A).indicator 1 (z - y, y) =
      A.indicator 1 z * p (z - y)
    rw [mul_comm]
    congr 1
    by_cases hz : z ∈ A <;> simp [hz]
  simp_rw [step]
  rw [lintegral_lintegral_swap ((((measurable_const.indicator hA).comp measurable_snd).mul
    (hp.comp (measurable_snd.sub measurable_fst))).aemeasurable)]
  rw [← lintegral_indicator hA]
  refine lintegral_congr fun z => ?_
  have hz : Measurable fun x : Rd d => p (z - x) := hp.comp (f := fun x => z - x) (by fun_prop)
  rw [lintegral_const_mul _ hz]
  by_cases hz : z ∈ A
  · simp [hz]
  · simp [hz]

/-! ### The smoothed `d = 3` Green density -/

/-- The density of the Green-smoothed `d = 3` wave kernel: `∫ p_η(z - y) G_s(dy)`. -/
def green3s (η s : ℝ) (z : Rd 3) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (heatDens η (z - y)) ∂waveGreen 3 s

theorem green3s_eq_sphere (η s : ℝ) (z : Rd 3) :
    green3s η s z = ENNReal.ofReal (s / (4 * π)) *
      ∫⁻ ω, ENNReal.ofReal (heatDens η (z - s • (ω : Rd 3)))
        ∂(volume : Measure (Rd 3)).toSphere := by
  unfold green3s
  show ∫⁻ y, _ ∂(ENNReal.ofReal (s / (4 * π)) •
      ((volume : Measure (Rd 3)).toSphere.map fun ω : Metric.sphere (0 : Rd 3) 1 =>
        s • (ω : Rd 3))) = _
  have hf : Measurable fun y : Rd 3 => ENNReal.ofReal (heatDens η (z - y)) :=
    ((measurable_heatDens η).comp (measurable_const.sub measurable_id)).ennreal_ofReal
  rw [lintegral_smul_measure, lintegral_map hf (by fun_prop), smul_eq_mul]

theorem measurable_green3s (η : ℝ) : Measurable (Function.uncurry (green3s η)) := by
  have h : Measurable fun q : (ℝ × Rd 3) × Metric.sphere (0 : Rd 3) 1 =>
      ENNReal.ofReal (heatDens η (q.1.2 - q.1.1 • (q.2 : Rd 3))) :=
    ((measurable_heatDens η).comp (by fun_prop)).ennreal_ofReal
  have h2 := h.lintegral_prod_right' (ν := (volume : Measure (Rd 3)).toSphere)
  have e : Function.uncurry (green3s η) = fun q : ℝ × Rd 3 =>
      ENNReal.ofReal (q.1 / (4 * π)) * ∫⁻ ω, ENNReal.ofReal (heatDens η (q.2 - q.1 • (ω : Rd 3)))
        ∂(volume : Measure (Rd 3)).toSphere := by
    funext q; exact green3s_eq_sphere η q.1 q.2
  rw [e]
  exact (ENNReal.measurable_ofReal.comp (by fun_prop)).mul h2

theorem green3s_ne_top {η : ℝ} (hη : 0 < η) (s : ℝ) (z : Rd 3) : green3s η s z ≠ ∞ := by
  have := WaveGreen.isFiniteMeasure_waveGreen 3 s
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal ((2 * π * η) ^ (-((3 : ℕ) : ℝ) / 2)) *
    waveGreen 3 s univ) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (measure_ne_top (waveGreen 3 s) univ)) ?_
  unfold green3s
  calc ∫⁻ y, ENNReal.ofReal (heatDens η (z - y)) ∂waveGreen 3 s
      ≤ ∫⁻ _y, ENNReal.ofReal ((2 * π * η) ^ (-((3 : ℕ) : ℝ) / 2)) ∂waveGreen 3 s := by
        refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
        have := heatDens_le (d := 3) hη (z - y)
        simpa [neg_div] using this
    _ = _ := lintegral_const _

/-- **The density of the Green-smoothed `d = 3` kernel**: `G_{s,η} = green3s η s (z) dz`. -/
theorem smoothedGreen_three_eq {η : ℝ} (hη : 0 < η) (s : ℝ) :
    smoothedGreen (waveGreen 3) s η = volume.withDensity (green3s η s) := by
  have := WaveGreen.isFiniteMeasure_waveGreen 3 s
  unfold smoothedGreen
  rw [gaussKernel_eq_withDensity hη, withDensity_conv (measurable_heatDens η).ennreal_ofReal]
  rfl

/-- `G_{s,η}(ℝ³) = s` for `s ≥ 0` (Gaussian smoothing preserves the mass). -/
theorem smoothedGreen_three_mass (η : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    smoothedGreen (waveGreen 3) s η univ = ENNReal.ofReal s := by
  have := WaveGreen.isFiniteMeasure_waveGreen 3 s
  unfold smoothedGreen
  rw [DampedMultiplier.conv_univ, WaveGreen.waveGreen_mass 3 (Or.inr (Or.inr rfl)) s hs]

/-- `Ĝ_{s,η}(ξ) = e^{-η|ξ|²/2} Ĝ_s(ξ)` for `s > 0`, `η ≥ 0`. -/
theorem charFun_smoothedGreen_three {η : ℝ} (hη : 0 ≤ η) {s : ℝ} (hs : 0 < s) (ξ : Rd 3) :
    charFun (smoothedGreen (waveGreen 3) s η) ξ = (gaussFactor η ξ : ℂ) * (waveHat s ξ : ℂ) := by
  rw [((LowAlphaConvolution.smoothedGreen_fourier
    (WaveGreenFourier.greenFourier 3 (Or.inr (Or.inr rfl))) hs hη).2 ξ).1, gaussFactor,
    Complex.ofReal_exp]
  push_cast
  ring_nf

end StratonovichHAMSecondMoment.GreenSmoothed3
