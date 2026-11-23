module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, item L17-E3, part 2: the norms `N_0`, `N_{1,e}`, `N_{2,e}` of `PairingInterface` for
damped Green densities whose transforms carry a Gaussian multiplier `e^{-η|ξ|²/2}` (the
Green-smoothed kernels `G_{s,η} = p_η * G_s`, main TeX lines 2023-2026), with the M4 edge datum
(`A = (0,∞)`, `μ_e = e^{-ε|ξ|²/2} μ`), bounded by the damped norms of
`L:damped-homogeneous-norms` uniformly in `η ≥ 0` (TeX 2016-2022: "the Gaussian multipliers can
be removed in the upper bounds"; `E:crude-norms` 1970-1976, `E:homogeneous-norms` 2380-2391) at
revision edf7085f (book 1.1.3).

This is item E's `PairingDampedNorms` with the extra multiplier: the structure `SmoothDensity`
replaces `GreenDensity` (`G_s` is any measure family with a finite jointly measurable density,
mass `s` and transform `e^{-η|ξ|²/2} Ĝ_s`); `lapFour_damp` acquires the factor
`e^{-η|ξ|²/2} ≤ 1`; the spatial pairing becomes the spectral pairing against
`e^{-ε|ξ|²/2} e^{-η|ξ|²} μ(dξ)` (`multNN`), a multiplier in `[0,1]`, which
`DampedNormsHomog.N2onSq_smoothed_mono` removes.  Proved: `N0_damp`, `N1_damp_le`,
`N2_damp_sq_le` (all with bounds independent of `η`).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.PairingDampedNorms

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal Real

namespace StratonovichHAMSecondMoment.PairingSmoothedNorms

open HomogHypothesis (Rd HomogCovariance)
open LowAlphaConvolution (gaussFactor gammaEps)
open WaveGreen (waveGreen)
open WaveKernel (waveHat)
open PairingInterface
open PairingBridge
open PairingDampedNorms (kappaCap_nuE lintegral_four measurable_kappaCap gammaEps_props
  inner_spatial_nonneg gaussMultNN)

variable {d : ℕ}

/-- The smoothed transform `e^{-η|ξ|²/2} Ĝ_s(ξ)`. -/
def wh (η s : ℝ) (ξ : Rd d) : ℝ := gaussFactor η ξ * waveHat s ξ

theorem continuous_wh (η s : ℝ) : Continuous (wh (d := d) η s) := by
  unfold wh
  exact (by unfold gaussFactor; fun_prop : Continuous fun ξ : Rd d => gaussFactor η ξ).mul
    (WaveKernel.waveHat_continuous.comp (continuous_const.prodMk continuous_id))

theorem abs_wh_le {η : ℝ} (hη : 0 ≤ η) (s : ℝ) (ξ : Rd d) : |wh η s ξ| ≤ |s| := by
  unfold wh
  rw [abs_mul, abs_of_pos (LowAlphaConvolution.gaussFactor_pos η ξ)]
  calc gaussFactor η ξ * |waveHat s ξ| ≤ 1 * |s| :=
        mul_le_mul (LowAlphaConvolution.gaussFactor_le_one hη ξ) (WaveKernel.abs_waveHat_le s ξ)
          (abs_nonneg _) zero_le_one
    _ = |s| := one_mul _

/-- A smoothed Green density: a jointly measurable finite density `g` of a measure family `G`
with mass `s` and transform `e^{-η|ξ|²/2} Ĝ_s` (`G_{s,η} = p_η * G_s`, TeX 2023-2026). -/
structure SmoothDensity (d : ℕ) (G : ℝ → Measure (Rd d)) (η : ℝ) (g : Kernel d) : Prop where
  dim : d = 1 ∨ d = 2 ∨ d = 3
  nonneg : 0 ≤ η
  meas : Measurable (Function.uncurry g)
  fin : ∀ s x, g s x ≠ ∞
  eq : ∀ s, G s = volume.withDensity (g s)
  mass : ∀ s, 0 ≤ s → G s univ = ENNReal.ofReal s
  fourier : ∀ s, 0 < s → ∀ ξ, charFun (G s) ξ = (gaussFactor η ξ : ℂ) * (waveHat s ξ : ℂ)

section Density

variable {G : ℝ → Measure (Rd d)} {η : ℝ} {g : Kernel d} (hgd : SmoothDensity d G η g)
include hgd

theorem SmoothDensity.meas_slice (s : ℝ) : Measurable (g s) :=
  hgd.meas.comp (measurable_const.prodMk measurable_id)

theorem SmoothDensity.lintegral_eq {s : ℝ} (hs : 0 ≤ s) : ∫⁻ y, g s y = ENNReal.ofReal s := by
  rw [← hgd.mass s hs, hgd.eq s, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

theorem SmoothDensity.isFiniteMeasure {s : ℝ} (hs : 0 ≤ s) : IsFiniteMeasure (G s) :=
  ⟨by rw [hgd.mass s hs]; exact ENNReal.ofReal_lt_top⟩

theorem SmoothDensity.measurable_damp (θ : ℝ) : Measurable (Function.uncurry (damp θ g)) :=
  (ENNReal.measurable_ofReal.comp (by fun_prop)).mul hgd.meas

theorem SmoothDensity.integrable_toReal {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun y => (g s y).toReal) := by
  refine integrable_toReal_of_lintegral_ne_top (hgd.meas_slice s).aemeasurable ?_
  rw [hgd.lintegral_eq hs]; exact ENNReal.ofReal_ne_top

theorem SmoothDensity.integral_toReal {s : ℝ} (hs : 0 ≤ s) : ∫ y, (g s y).toReal = s := by
  rw [MeasureTheory.integral_toReal (hgd.meas_slice s).aemeasurable
    (Filter.Eventually.of_forall fun y => lt_top_iff_ne_top.2 (hgd.fin s y)),
    hgd.lintegral_eq hs, ENNReal.toReal_ofReal hs]

theorem SmoothDensity.integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℝ) (f : Rd d → E) : ∫ y, f y ∂G s = ∫ y, (g s y).toReal • f y := by
  rw [hgd.eq s, integral_withDensity_eq_integral_toReal_smul (hgd.meas_slice s)
    (Filter.Eventually.of_forall fun y => lt_top_iff_ne_top.2 (hgd.fin s y))]

theorem SmoothDensity.charFun_eq {s : ℝ} (hs : 0 < s) (ξ : Rd d) :
    charFun (G s) ξ = ((wh η s ξ : ℝ) : ℂ) := by
  rw [hgd.fourier s hs ξ, wh, Complex.ofReal_mul]

/-- The transform of the density: `∫ e^{iξ·y} g(s,y) dy = e^{-η|ξ|²/2} Ĝ_s(ξ)`. -/
theorem SmoothDensity.fourier' {s : ℝ} (hs : 0 < s) (ξ : Rd d) :
    ∫ y, Complex.exp (Complex.I * (inner ℝ ξ y : ℝ)) * ((g s y).toReal : ℂ) =
      ((wh η s ξ : ℝ) : ℂ) := by
  rw [← hgd.charFun_eq hs ξ, charFun_apply, hgd.integral_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Complex.real_smul]
  rw [real_inner_comm]
  ring_nf

/-- **`N_0` of the damped kernel**: `θ^{-2}`. -/
theorem N0_damp {θ : ℝ} (hθ : 0 < θ) : N0 (damp θ g) = ENNReal.ofReal (θ ^ (-(2 : ℝ))) := by
  obtain ⟨hI, hN⟩ := WaveGreen.N0_waveGreen d hgd.dim θ hθ
  unfold N0 damp
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ∫⁻ x, ENNReal.ofReal (Real.exp (-(θ * t))) * g t x =
      ENNReal.ofReal (Real.exp (-(θ * t)) * (waveGreen d t univ).toReal) := by
    intro t ht
    rw [lintegral_const_mul _ (hgd.meas_slice t), hgd.lintegral_eq (le_of_lt ht),
      WaveGreen.waveGreen_mass d hgd.dim t (le_of_lt ht), ENNReal.toReal_ofReal (le_of_lt ht),
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, ← ofReal_integral_eq_lintegral_ofReal hI]
  · rw [← hN]; rfl
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    exact mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg

/-- **The Laplace-Fourier transform of the damped kernel**: for `θ ≥ 0` and `λ > 0`,
`e^{-η|ξ|²/2} ((θ+λ)² + |ξ|²)⁻¹`. -/
theorem lapFour_damp {θ l : ℝ} (hθ : 0 ≤ θ) (hl : 0 < l) (ξ : Rd d) :
    lapFour (damp θ g) l ξ = ((gaussFactor η ξ * (1 / ((θ + l) ^ 2 + ‖ξ‖ ^ 2)) : ℝ) : ℂ) := by
  have hq : 0 < θ + l := by linarith
  have hdamp : ∀ s y, (damp θ g s y).toReal = Real.exp (-(θ * s)) * (g s y).toReal := by
    intro s y
    unfold damp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hform : ∀ s y, Complex.exp ((-(l * s) : ℝ) + Complex.I * (inner ℝ ξ y : ℝ)) *
      ((damp θ g s y).toReal : ℂ) = ((Real.exp (-((θ + l) * s)) : ℝ) : ℂ) *
        (Complex.exp (Complex.I * (inner ℝ ξ y : ℝ)) * ((g s y).toReal : ℂ)) := by
    intro s y
    rw [hdamp, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_exp, Complex.exp_add]
    have e : Complex.exp ((-((θ + l) * s) : ℝ) : ℂ) =
        Complex.exp ((-(l * s) : ℝ) : ℂ) * Complex.exp ((-(θ * s) : ℝ) : ℂ) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [e]; ring
  set F : ℝ × Rd d → ℂ := fun p => Complex.exp ((-(l * p.1) : ℝ) +
    Complex.I * (inner ℝ ξ p.2 : ℝ)) * ((damp θ g p.1 p.2).toReal : ℂ) with hF
  have hFm : Measurable F := by
    refine Measurable.mul (by fun_prop) ?_
    exact Complex.measurable_ofReal.comp (ENNReal.measurable_toReal.comp (hgd.measurable_damp θ))
  have hnorm : ∀ s y, ‖F (s, y)‖ = Real.exp (-((θ + l) * s)) * (g s y).toReal := by
    intro s y
    simp only [hF]
    rw [hform, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg ENNReal.toReal_nonneg,
      mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hmeasure : (volume : Measure (ℝ × Rd d)).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d))) =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure (Rd d)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hInt : Integrable F ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure (Rd d))) := by
    refine (integrable_prod_iff hFm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      refine Integrable.mono' ((hgd.integrable_toReal (le_of_lt hs)).const_mul
        (Real.exp (-((θ + l) * s)))) (hFm.comp measurable_prodMk_left).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => (hnorm s y).le)
    · have hI := (WaveGreen.N0_waveGreen d hgd.dim (θ + l) hq).1
      refine (hI.congr_fun (fun s hs => ?_) measurableSet_Ioi)
      simp only
      rw [show (fun y => ‖F (s, y)‖) = fun y => Real.exp (-((θ + l) * s)) * (g s y).toReal from
        funext (hnorm s), integral_const_mul, hgd.integral_toReal (le_of_lt hs),
        WaveGreen.waveGreen_mass d hgd.dim s (le_of_lt hs), ENNReal.toReal_ofReal (le_of_lt hs)]
  unfold lapFour
  change ∫ p, F p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (Rd d)))) = _
  rw [hmeasure, integral_prod F hInt]
  have hin : ∀ s ∈ Ioi (0 : ℝ), ∫ y, F (s, y) =
      ((gaussFactor η ξ * (Real.exp (-((θ + l) * s)) * waveHat s ξ) : ℝ) : ℂ) := by
    intro s hs
    simp only [hF]
    simp_rw [hform]
    rw [integral_const_mul, hgd.fourier' hs ξ, wh]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_complex_ofReal, integral_const_mul,
    (WaveKernel.waveHat_laplace (θ + l) hq ξ).2]

theorem enorm_lapFour_damp {θ l : ℝ} (hθ : 0 ≤ θ) (hl : 0 < l) (ξ : Rd d) :
    ‖lapFour (damp θ g) l ξ‖ₑ =
      ENNReal.ofReal (gaussFactor η ξ * (1 / ((θ + l) ^ 2 + ‖ξ‖ ^ 2))) := by
  have := LowAlphaConvolution.gaussFactor_pos η ξ
  rw [lapFour_damp hgd hθ hl ξ, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

end Density

/-! ### The first norm -/

section First

variable {G : ℝ → Measure (Rd d)} {η : ℝ} {g : Kernel d} (hgd : SmoothDensity d G η g)
include hgd

/-- **`N_{1,e}` of the damped smoothed kernel** is at most `N₁(θ)`, uniformly in `η`. -/
theorem N1_damp_le {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
    {ε : ℝ} (hε : 0 < ε) {θ : ℝ} (hθ : 0 < θ) :
    N1 α₀ (smoothEdge hH hε) (damp θ g) ≤ ENNReal.ofReal (DampedNorms.N1 α₀ θ μ) := by
  have := hH.μ_radon
  obtain ⟨hR, -⟩ := DampedNormsHomog.homog_spectral_facts hH
  have hG : 0 < (Real.Gamma α₀)⁻¹ := inv_pos.2 (Real.Gamma_pos_of_pos hH.alpha0_pos)
  set B : ℝ → ℝ≥0∞ := fun l => ∫⁻ ξ, ENNReal.ofReal (1 / ((θ + l) ^ 2 + ‖ξ‖ ^ 2)) ∂μ with hB
  have hBm : Measurable B :=
    Measurable.lintegral_prod_right' (f := fun p : ℝ × Rd d =>
      ENNReal.ofReal (1 / ((θ + p.1) ^ 2 + ‖p.2‖ ^ 2))) (ENNReal.measurable_ofReal.comp
        (by fun_prop))
  have hae : ∀ᵐ l ∂nuE α₀ (Ioi 0), 0 < l := by
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    exact ae_restrict_mem measurableSet_Ioi
  unfold N1
  change ∫⁻ l, ∫⁻ ξ, ‖lapFour (damp θ g) l ξ‖ₑ ∂(smoothSpec μ ε) ∂nuE α₀ (Ioi 0) ≤ _
  calc ∫⁻ l, ∫⁻ ξ, ‖lapFour (damp θ g) l ξ‖ₑ ∂(smoothSpec μ ε) ∂nuE α₀ (Ioi 0)
      ≤ ∫⁻ l, B l ∂nuE α₀ (Ioi 0) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with l hl
        have hdrop : ∀ ξ, ‖lapFour (damp θ g) l ξ‖ₑ ≤
            ENNReal.ofReal (1 / ((θ + l) ^ 2 + ‖ξ‖ ^ 2)) := fun ξ => by
          rw [enorm_lapFour_damp hgd hθ.le hl]
          exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_left (by positivity)
            (LowAlphaConvolution.gaussFactor_le_one hgd.nonneg ξ))
        refine (lintegral_mono hdrop).trans ?_
        unfold smoothSpec
        have hm : Measurable fun ξ : Rd d => ENNReal.ofReal (1 / ((θ + l) ^ 2 + ‖ξ‖ ^ 2)) :=
          ENNReal.measurable_ofReal.comp (by fun_prop)
        have hgm : Measurable fun ξ : Rd d => ENNReal.ofReal (gaussFactor ε ξ) :=
          ENNReal.measurable_ofReal.comp (by unfold gaussFactor; fun_prop)
        rw [lintegral_withDensity_eq_lintegral_mul _ hgm hm]
        refine lintegral_mono fun ξ => ?_
        simp only [Pi.mul_apply]
        calc ENNReal.ofReal (gaussFactor ε ξ) * ENNReal.ofReal (1 / ((θ + l) ^ 2 + ‖ξ‖ ^ 2))
            ≤ 1 * ENNReal.ofReal (1 / ((θ + l) ^ 2 + ‖ξ‖ ^ 2)) := by
              gcongr
              exact ENNReal.ofReal_le_one.2 (LowAlphaConvolution.gaussFactor_le_one hε.le ξ)
          _ = _ := one_mul _
    _ = ∫⁻ l in Ioi 0, ENNReal.ofReal ((Real.Gamma α₀)⁻¹ *
          (l ^ (α₀ - 1) * SpectralHomog.resolvent μ (θ + l))) := by
        unfold nuE
        rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hBm]
        refine setLIntegral_congr_fun measurableSet_Ioi fun l hl => ?_
        have hl0 : (0 : ℝ) < l := hl
        simp only [Pi.mul_apply, hB]
        rw [← ofReal_integral_eq_lintegral_ofReal
          (SpectralHomog.resolvent_integrable hR (θ + l) (by linarith))
          (Filter.Eventually.of_forall fun ξ => by positivity),
          ← ENNReal.ofReal_mul (mul_nonneg hG.le (Real.rpow_nonneg hl0.le _)), mul_assoc]
        rfl
    _ = ENNReal.ofReal (DampedNorms.N1 α₀ θ μ) := by
        rw [← ofReal_integral_eq_lintegral_ofReal, integral_const_mul]
        · rfl
        · exact (ClockCopyHomog.damped_norms_finite_paper hH θ hθ).2.2.const_mul _
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with l hl
          exact mul_nonneg hG.le (mul_nonneg (Real.rpow_nonneg (le_of_lt hl) _)
            (ClockCopy.resolvent_nonneg μ _))

end First

/-! ### The second norm -/

/-- The combined multiplier `e^{-ε|ξ|²/2} e^{-η|ξ|²}` as an `ℝ≥0`-valued function. -/
def multNN (ε η : ℝ) (ξ : Rd d) : NNReal := (gaussFactor ε ξ * gaussFactor η ξ ^ 2).toNNReal

theorem measurable_multNN (ε η : ℝ) : Measurable (multNN (d := d) ε η) := by
  unfold multNN gaussFactor; fun_prop

theorem multNN_le_one {ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η) (ξ : Rd d) : multNN ε η ξ ≤ 1 := by
  unfold multNN
  rw [Real.toNNReal_le_one]
  have h1 := LowAlphaConvolution.gaussFactor_le_one hε ξ
  have h2 := LowAlphaConvolution.gaussFactor_le_one hη ξ
  have h3 := (LowAlphaConvolution.gaussFactor_pos η ξ).le
  have h4 := (LowAlphaConvolution.gaussFactor_pos ε ξ).le
  calc gaussFactor ε ξ * gaussFactor η ξ ^ 2 ≤ 1 * 1 ^ 2 := by gcongr
    _ = 1 := by norm_num

/-- The spectral pairing of the smoothed transforms against `μ_e` is the pairing of the
unsmoothed transforms against the doubly smoothed spectral measure. -/
theorem integral_wh_smoothSpec {μ : Measure (Rd d)} (ε η s r : ℝ) :
    ∫ ξ, wh η s ξ * wh η r ξ ∂(smoothSpec μ ε) =
      ∫ ξ, waveHat s ξ * waveHat r ξ ∂(DampedNormsHomog.smoothed μ (multNN ε η)) := by
  unfold smoothSpec DampedNormsHomog.smoothed
  have hm : Measurable fun ξ : Rd d => ENNReal.ofReal (gaussFactor ε ξ) :=
    ENNReal.measurable_ofReal.comp (by unfold gaussFactor; fun_prop)
  rw [integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_smul (measurable_multNN ε η)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  have h1 := (LowAlphaConvolution.gaussFactor_pos ε ξ).le
  have h2 := (LowAlphaConvolution.gaussFactor_pos η ξ).le
  simp only [smul_eq_mul, NNReal.smul_def, multNN, wh,
    ENNReal.toReal_ofReal h1, Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤
      gaussFactor ε ξ * gaussFactor η ξ ^ 2)]
  ring

section Second

variable {G : ℝ → Measure (Rd d)} {η : ℝ} {g : Kernel d} (hgd : SmoothDensity d G η g)
include hgd

theorem integral_cos {s : ℝ} (hs : 0 < s) (ξ : Rd d) :
    ∫ x, (g s x).toReal * Real.cos (inner ℝ ξ x) = wh η s ξ := by
  have hI : Integrable fun x => Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) *
      ((g s x).toReal : ℂ) := by
    refine Integrable.mono' (hgd.integrable_toReal hs.le).norm
      ((by fun_prop : Continuous fun x : Rd d =>
        Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))).aestronglyMeasurable.mul
        (Complex.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
          (hgd.meas_slice s))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real]
  have hre := integral_re hI
  rw [hgd.fourier' hs ξ] at hre
  have hr : RCLike.re ((wh η s ξ : ℝ) : ℂ) = wh η s ξ := Complex.ofReal_re _
  rw [hr] at hre
  rw [← hre]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [RCLike.re_to_complex, Complex.re_mul_ofReal]
  rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_re, mul_comm]

section Spatial

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
  {ε : ℝ} (hε : 0 < ε)
include hH hε

theorem inner_spatial {r : ℝ} (hr : 0 < r) (x : Rd d) :
    ∫ y, (g r y).toReal * gammaEps Γ ε (x - y) =
      ∫ ξ, wh η r ξ * Real.cos (inner ℝ ξ x) * gaussFactor ε ξ ∂μ := by
  have := hH.μ_radon
  have hfin := hgd.isFiniteMeasure hr.le
  obtain ⟨-, -, hint2, hrep⟩ := LowAlphaConvolution.smoothed_pairing_spectral hH.Γ_tempered
    hH.μ_tempered hH.spectral hε (G r) (-x)
  have hL : ∫ y, gammaEps Γ ε (y + -x) ∂(G r) =
      ∫ y, (g r y).toReal * gammaEps Γ ε (x - y) := by
    rw [hgd.integral_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    rw [← LowAlphaUpper.gammaEps_neg hH.Γ_even ε (x - y)]
    congr 2
    abel
  have hre := congrArg Complex.re hrep
  rw [Complex.ofReal_re, hL] at hre
  have hre2 := integral_re hint2
  simp only [RCLike.re_to_complex] at hre2
  rw [hre, ← hre2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [hgd.charFun_eq hr ξ]
  rw [Complex.re_mul_ofReal, Complex.re_ofReal_mul, mul_comm Complex.I,
    Complex.exp_ofReal_mul_I_re, inner_neg_right, Real.cos_neg]

theorem double_spatial {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ∫ x, (g s x).toReal * ∫ y, (g r y).toReal * gammaEps Γ ε (x - y) =
      ∫ ξ, wh η s ξ * wh η r ξ ∂(smoothSpec μ ε) := by
  have := hH.μ_radon
  have hgauss := LowAlphaConvolution.integrable_gaussFactor hH.μ_tempered hε
  simp_rw [inner_spatial hgd hH hε hr]
  have hF : Integrable (Function.uncurry fun (x : Rd d) (ξ : Rd d) =>
      (g s x).toReal * (wh η r ξ * Real.cos (inner ℝ ξ x) * gaussFactor ε ξ))
      ((volume : Measure (Rd d)).prod μ) := by
    refine Integrable.mono' ((hgd.integrable_toReal hs.le).mul_prod (hgauss.const_mul |r|)) ?_
      (Filter.Eventually.of_forall fun p => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      refine Measurable.mul ((ENNReal.measurable_toReal.comp (hgd.meas_slice s)).comp
        measurable_fst) ?_
      exact (((continuous_wh η r).measurable.comp measurable_snd).mul (by fun_prop)).mul
        ((by unfold gaussFactor; fun_prop : Measurable fun ξ : Rd d => gaussFactor ε ξ).comp
          measurable_snd)
    · show |(g s p.1).toReal * (wh η r p.2 * Real.cos (inner ℝ p.2 p.1) *
          gaussFactor ε p.2)| ≤ (g s p.1).toReal * (|r| * gaussFactor ε p.2)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
        abs_of_pos (LowAlphaConvolution.gaussFactor_pos ε p.2)]
      have h1 := abs_wh_le hgd.nonneg r p.2
      have h2 := Real.abs_cos_le_one (inner ℝ p.2 p.1)
      have h3 := (LowAlphaConvolution.gaussFactor_pos ε p.2).le
      have h4 : (0 : ℝ) ≤ (g s p.1).toReal := ENNReal.toReal_nonneg
      calc (g s p.1).toReal * (|wh η r p.2| * |Real.cos (inner ℝ p.2 p.1)| *
            gaussFactor ε p.2)
          ≤ (g s p.1).toReal * (|r| * 1 * gaussFactor ε p.2) := by gcongr
        _ = (g s p.1).toReal * (|r| * gaussFactor ε p.2) := by ring
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hF, integral_smoothSpec]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  have : ∀ x, (g s x).toReal * (wh η r ξ * Real.cos (inner ℝ ξ x) * gaussFactor ε ξ) =
      (wh η r ξ * gaussFactor ε ξ) * ((g s x).toReal * Real.cos (inner ℝ ξ x)) :=
    fun x => by ring
  simp_rw [this]
  rw [integral_const_mul, integral_cos hgd hs ξ]
  ring

theorem lintegral_double_spatial {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ∫⁻ x, ∫⁻ y, g s x * g r y * gammaOf (smoothSpec μ ε) (x - y) =
        ENNReal.ofReal (∫ ξ, wh η s ξ * wh η r ξ ∂(smoothSpec μ ε)) ∧
      0 ≤ ∫ ξ, wh η s ξ * wh η r ξ ∂(smoothSpec μ ε) := by
  obtain ⟨hc, hb⟩ := gammaEps_props hH hε
  set C := ∫ ξ, gaussFactor ε ξ ∂μ with hC
  have hγ : ∀ z, gammaOf (smoothSpec μ ε) z = ENNReal.ofReal (gammaEps Γ ε z) := fun z => by
    rw [gammaOf_smoothSpec hH hε, LowAlphaUpper.covEps_eq_ofReal hε.le
      (LowAlphaConvolution.integrable_heatDens hH.Γ_tempered hε)]
  have hgr : ∀ t y, g t y = ENNReal.ofReal (g t y).toReal := fun t y =>
    (ENNReal.ofReal_toReal (hgd.fin t y)).symm
  have hinI : ∀ x, Integrable fun y => (g r y).toReal * gammaEps Γ ε (x - y) := by
    intro x
    refine Integrable.mono' ((hgd.integrable_toReal hr.le).mul_const C)
      (((ENNReal.measurable_toReal.comp (hgd.meas_slice r)).aestronglyMeasurable).mul
        (hc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (LowAlphaConvolution.gammaEps_nonneg Γ hε.le _))]
    exact mul_le_mul_of_nonneg_left (hb _) ENNReal.toReal_nonneg
  have hinner : ∀ x, ∫⁻ y, g r y * ENNReal.ofReal (gammaEps Γ ε (x - y)) =
      ENNReal.ofReal (∫ y, (g r y).toReal * gammaEps Γ ε (x - y)) := by
    intro x
    rw [ofReal_integral_eq_lintegral_ofReal (hinI x) (Filter.Eventually.of_forall fun y =>
      mul_nonneg ENNReal.toReal_nonneg (LowAlphaConvolution.gammaEps_nonneg Γ hε.le _))]
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← hgr]
  have hIm : StronglyMeasurable fun x : Rd d => ∫ y, (g r y).toReal * gammaEps Γ ε (x - y) := by
    have hm : StronglyMeasurable fun p : Rd d × Rd d =>
        (g r p.2).toReal * gammaEps Γ ε (p.1 - p.2) :=
      (((ENNReal.measurable_toReal.comp (hgd.meas_slice r)).comp measurable_snd).mul
        (hc.measurable.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
    exact hm.integral_prod_right'
  have hIb : ∀ x, ∫ y, (g r y).toReal * gammaEps Γ ε (x - y) ≤ r * C := by
    intro x
    calc ∫ y, (g r y).toReal * gammaEps Γ ε (x - y) ≤ ∫ y, (g r y).toReal * C :=
          integral_mono (hinI x) ((hgd.integrable_toReal hr.le).mul_const C)
            fun y => mul_le_mul_of_nonneg_left (hb _) ENNReal.toReal_nonneg
      _ = r * C := by rw [integral_mul_const, hgd.integral_toReal hr.le]
  have houtI : Integrable fun x => (g s x).toReal * ∫ y, (g r y).toReal * gammaEps Γ ε (x - y) := by
    refine Integrable.mono' ((hgd.integrable_toReal hs.le).mul_const (r * C))
      (((ENNReal.measurable_toReal.comp (hgd.meas_slice s)).aestronglyMeasurable).mul
        hIm.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (inner_spatial_nonneg hε r x))]
    exact mul_le_mul_of_nonneg_left (hIb x) ENNReal.toReal_nonneg
  have hnn : 0 ≤ ∫ x, (g s x).toReal * ∫ y, (g r y).toReal * gammaEps Γ ε (x - y) :=
    integral_nonneg fun x => mul_nonneg ENNReal.toReal_nonneg (inner_spatial_nonneg hε r x)
  rw [← double_spatial hgd hH hε hs hr]
  refine ⟨?_, hnn⟩
  simp_rw [hγ, mul_assoc]
  have hc' : ∀ x, ∫⁻ y, g s x * (g r y * ENNReal.ofReal (gammaEps Γ ε (x - y))) =
      g s x * ENNReal.ofReal (∫ y, (g r y).toReal * gammaEps Γ ε (x - y)) := by
    intro x
    rw [lintegral_const_mul' _ _ (hgd.fin s x), hinner x]
  simp_rw [hc']
  rw [ofReal_integral_eq_lintegral_ofReal houtI (Filter.Eventually.of_forall fun x =>
    mul_nonneg ENNReal.toReal_nonneg (inner_spatial_nonneg hε r x))]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ← hgr]

end Spatial

end Second

/-! ### Assembly of the second norm -/

section Assembly

variable {G : ℝ → Measure (Rd d)} {η : ℝ} {g : Kernel d} (hgd : SmoothDensity d G η g)
  {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
  {ε : ℝ} (hε : 0 < ε)
include hgd hH hε

theorem QL_damp_eq {θ : ℝ} (hθ : 0 < θ) (L : ℝ) :
    QL (nuE α₀ (Ioi 0)) (smoothSpec μ ε) L (zeroExt (damp θ g)) (zeroExt (damp θ g)) =
      ENNReal.ofReal (DampedNormsHomog.N2onSq α₀ θ (Ioc 0 L)
        (DampedNormsHomog.smoothed μ (multNN ε η))) := by
  have := hH.μ_radon
  obtain ⟨hR, hμ0⟩ := DampedNormsHomog.homog_spectral_facts hH
  obtain ⟨hI, -, -⟩ := DampedNormsHomog.N2onSq_smoothed_mono μ hR hμ0 α₀ θ hH.alpha0_pos
    hH.alpha0_lt_one hθ (multNN ε η) (measurable_multNN ε η)
    (multNN_le_one hε.le hgd.nonneg)
    (Ioc 0 L) univ measurableSet_Ioc MeasurableSet.univ (subset_univ _)
  obtain ⟨hc, -⟩ := gammaEps_props hH hε
  have hγ : ∀ z, gammaOf (smoothSpec μ ε) z = ENNReal.ofReal (gammaEps Γ ε z) := fun z => by
    rw [gammaOf_smoothSpec hH hε, LowAlphaUpper.covEps_eq_ofReal hε.le
      (LowAlphaConvolution.integrable_heatDens hH.Γ_tempered hε)]
  have hzm : Measurable fun p : ℝ × Rd d => zeroExt (damp θ g) p.1 p.2 := by
    have e : (fun p : ℝ × Rd d => zeroExt (damp θ g) p.1 p.2) =
        {p : ℝ × Rd d | 0 < p.1}.indicator (Function.uncurry (damp θ g)) := by
      funext p
      by_cases hp : 0 < p.1
      · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × Rd d | 0 < p.1} from hp)]
        exact Set.indicator_of_mem (show p.1 ∈ Ioi (0 : ℝ) from hp) _
      · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × Rd d | 0 < p.1} from hp)]
        exact Set.indicator_of_notMem (show p.1 ∉ Ioi (0 : ℝ) from hp) _
    rw [e]
    exact (hgd.measurable_damp θ).indicator (measurableSet_lt measurable_const measurable_fst)
  have hΦ : Measurable fun w : (ℝ × Rd d) × (ℝ × Rd d) =>
      zeroExt (damp θ g) w.1.1 w.1.2 * zeroExt (damp θ g) w.2.1 w.2.2 *
        kappaCap (nuE α₀ (Ioi 0)) L (w.1.1 - w.2.1) * gammaOf (smoothSpec μ ε) (w.1.2 - w.2.2) := by
    have hνs : SFinite (nuE α₀ (Ioi 0)) := by unfold nuE; infer_instance
    have hγm : Measurable fun w : (ℝ × Rd d) × (ℝ × Rd d) =>
        gammaOf (smoothSpec μ ε) (w.1.2 - w.2.2) := by
      simp_rw [hγ]
      exact ENNReal.measurable_ofReal.comp (hc.measurable.comp
        ((measurable_snd.comp measurable_fst).sub (measurable_snd.comp measurable_snd)))
    exact (((hzm.comp measurable_fst).mul (hzm.comp measurable_snd)).mul
      ((measurable_kappaCap _ L).comp ((measurable_fst.comp measurable_fst).sub
        (measurable_fst.comp measurable_snd)))).mul hγm
  unfold QL
  rw [lintegral_four (fun s x r y => zeroExt (damp θ g) s x * zeroExt (damp θ g) r y *
    kappaCap (nuE α₀ (Ioi 0)) L (s - r) * gammaOf (smoothSpec μ ε) (x - y)) hΦ]
  have hpt : ∀ s r : ℝ, ∫⁻ x, ∫⁻ y, zeroExt (damp θ g) s x * zeroExt (damp θ g) r y *
      kappaCap (nuE α₀ (Ioi 0)) L (s - r) * gammaOf (smoothSpec μ ε) (x - y) =
      (Ioi (0 : ℝ)).indicator (fun s => (Ioi (0 : ℝ)).indicator (fun r =>
        ENNReal.ofReal (DampedNormsHomog.N2onOuter α₀ θ (Ioc 0 L)
          (DampedNormsHomog.smoothed μ (multNN ε η)) (s, r))) r) s := by
    intro s r
    by_cases hs : s ∈ Ioi (0 : ℝ)
    · by_cases hr : r ∈ Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hr]
        have hs0 : 0 < s := hs
        have hr0 : 0 < r := hr
        have hzs : ∀ x, zeroExt (damp θ g) s x = ENNReal.ofReal (Real.exp (-(θ * s))) * g s x :=
          fun x => Set.indicator_of_mem hs _
        have hzr : ∀ y, zeroExt (damp θ g) r y = ENNReal.ofReal (Real.exp (-(θ * r))) * g r y :=
          fun y => Set.indicator_of_mem hr _
        set c := ENNReal.ofReal (Real.exp (-(θ * s))) * ENNReal.ofReal (Real.exp (-(θ * r))) *
          kappaCap (nuE α₀ (Ioi 0)) L (s - r) with hcdef
        have hct : c ≠ ∞ := by
          rw [hcdef, kappaCap_nuE hH.alpha0_pos]
          exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
            ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
        have hre : ∀ x y, zeroExt (damp θ g) s x * zeroExt (damp θ g) r y *
            kappaCap (nuE α₀ (Ioi 0)) L (s - r) * gammaOf (smoothSpec μ ε) (x - y) =
            c * (g s x * g r y * gammaOf (smoothSpec μ ε) (x - y)) := by
          intro x y
          rw [hzs, hzr, hcdef]
          ring
        simp_rw [hre, lintegral_const_mul' _ _ hct]
        rw [(lintegral_double_spatial hgd hH hε hs0 hr0).1, integral_wh_smoothSpec, hcdef,
          kappaCap_nuE hH.alpha0_pos,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (mul_nonneg (by positivity)
            (DampedNormsHomog.KS_nonneg _ _ _ hH.alpha0_pos))]
        unfold DampedNormsHomog.N2onOuter
        congr 1
        rw [show -(θ * (s + r)) = -(θ * s) + -(θ * r) by ring, Real.exp_add]
      · rw [Set.indicator_of_mem hs, Set.indicator_of_notMem hr]
        have hzr : ∀ y, zeroExt (damp θ g) r y = 0 := fun y => Set.indicator_of_notMem hr _
        simp [hzr]
    · rw [Set.indicator_of_notMem hs]
      have hzs : ∀ x, zeroExt (damp θ g) s x = 0 := fun x => Set.indicator_of_notMem hs _
      simp [hzs]
  simp_rw [hpt]
  have hnn : 0 ≤ᵐ[TimeFractional.P2] DampedNormsHomog.N2onOuter α₀ θ (Ioc 0 L)
      (DampedNormsHomog.smoothed μ (multNN ε η)) := by
    filter_upwards [DampedNorms.ae_P2] with p hp
    unfold DampedNormsHomog.N2onOuter
    rw [← integral_wh_smoothSpec]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (DampedNormsHomog.KS_nonneg _ _ _ hH.alpha0_pos))
      (lintegral_double_spatial hgd hH hε hp.1 hp.2.1).2
  rw [DampedNormsHomog.N2onSq, ofReal_integral_eq_lintegral_ofReal hI hnn,
    TimeFractional.P2, lintegral_prod _ hI.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  rw [← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun s => ?_
  by_cases hs : s ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hs]
    simp only [Set.indicator_of_mem hs]
    rw [lintegral_indicator measurableSet_Ioi]
  · rw [Set.indicator_of_notMem hs]
    simp [Set.indicator_of_notMem hs]

/-- **`N_{2,e}` of the damped smoothed kernel**: `N_{2,e}(θ)² ≤ N₂(θ)²`, uniformly in `η`. -/
theorem N2_damp_sq_le {θ : ℝ} (hθ : 0 < θ) :
    N2 α₀ (smoothEdge hH hε) (damp θ g) ^ 2 ≤ ENNReal.ofReal (DampedNorms.N2sq α₀ θ μ) := by
  have := hH.μ_radon
  obtain ⟨hR, hμ0⟩ := DampedNormsHomog.homog_spectral_facts hH
  unfold N2
  rw [NC_sq]
  refine iSup_le fun L => ?_
  change QL (nuE α₀ (Ioi 0)) (smoothSpec μ ε) (L : ℝ) (zeroExt (damp θ g))
    (zeroExt (damp θ g)) ≤ _
  rw [QL_damp_eq hgd hH hε hθ, ← DampedNormsHomog.N2onSq_univ α₀ θ μ hH.alpha0_pos]
  refine ENNReal.ofReal_le_ofReal ?_
  exact (DampedNormsHomog.N2onSq_smoothed_mono μ hR hμ0 α₀ θ hH.alpha0_pos
    hH.alpha0_lt_one hθ (multNN ε η) (measurable_multNN ε η) (multNN_le_one hε.le hgd.nonneg)
    (Ioc 0 (L : ℝ)) univ measurableSet_Ioc MeasurableSet.univ (subset_univ _)).2.2

end Assembly

end StratonovichHAMSecondMoment.PairingSmoothedNorms
