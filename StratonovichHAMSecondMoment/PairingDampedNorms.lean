module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L17, item L17-E, part 2: the norms `N_0`, `N_{1,e}`, `N_{2,e}` of `PairingInterface`
(`E:pairing-edge-norms`, TeX 1445-1458) for the damped wave Green densities `e^{-θs} g(s,y)`
with the M4 edge datum (`A = (0,∞)`, `μ_e = e^{-ε|ξ|²/2} μ`), bounded by the damped norms of
`L:damped-homogeneous-norms` (`DampedNorms.N1`, `DampedNorms.N2sq`).  TeX lines 1970-1976
(`E:crude-norms`), 2016-2022 (the Gaussian multipliers "can be removed in the upper bounds")
and 2380-2391 (`E:homogeneous-norms`) at revision edf7085f (book 1.1.3).

Formalized (all proved, nothing supplied):
* `GreenDensity d g`: a jointly measurable finite density of the wave Green measures;
  `greenDensity_one` (`green1`) and `greenDensity_two` (`green2`, with the joint
  measurability of `uncurry green2` that INTERFACE §4.10 assigns to E);
* `N0_damp`: `N_0 = θ^{-2}`;
* `lapFour_damp`: `𝓛(e^{-θ·}g)(λ,ξ) = ((θ+λ)² + |ξ|²)⁻¹` for `λ > 0` (Fubini,
  `WaveGreenFourier.waveGreen_fourier`, `WaveKernel.waveHat_laplace`); `N1_damp_le`:
  `N_{1,e} ≤ N₁(θ)`;
* `kappaCap_nuE`: the capped Gamma mixture is `K_{(0,L]}`; `lintegral_double_spatial`:
  `∫∫ g_s g_r γ_ε(x-y) = ∫ Ĝ_s Ĝ_r dμ_e ≥ 0` (via
  `LowAlphaConvolution.smoothed_pairing_spectral`); `QL_damp_eq`:
  `Q_L(G^0,G^0) = N_{2,e^{-ε|·|²/2},(0,L]}(θ)²`; `N2_damp_sq_le`: `N_{2,e}² ≤ N₂(θ)²`
  (`DampedNormsHomog.N2onSq_smoothed_mono`).

Not in this module: `d = 3`.  The `d = 3` wave Green measure is a sphere measure without a
density.  `d = 3` is formalized at the diagram level for the Green-smoothed kernel
`G_{s,η} = p_η * G_s` (TeX 2023-2026), uniformly in `η > 0`, in the modules `GreenSmoothed3`
(its density, joint measurability and finiteness), `PairingSmoothedNorms` (these norms with the
multiplier `e^{-η|ξ|²/2}`), `EnvelopeD3` and `EnvelopeD3Final`.  The limit `η → 0` and the
`d = 3` moment (`_paper`) versions are not formalized (decision 5 of wave L17).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.PairingBridge
public import StratonovichHAMSecondMoment.DampedNormsHomog
public import StratonovichHAMSecondMoment.WaveGreenFourier

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal Real

namespace StratonovichHAMSecondMoment.PairingDampedNorms

open HomogHypothesis (Rd HomogCovariance)
open LowAlphaConvolution (gaussFactor gammaEps)
open WaveGreen (waveGreen)
open WaveKernel (waveHat)
open PairingInterface
open PairingBridge

variable {d : ℕ}

/-! ### Green densities -/

/-- A Green density: a jointly measurable finite kernel `g` with `G_s = g(s,·) dy` for the wave
Green measures of `d ∈ {1,2,3}` (`d = 1`: `green1`; `d = 2`: `green2`).  Instances exist only in
`d = 1, 2`: in `d = 3` the Green measure has no density (see `SmoothDensity` for the
Green-smoothed `d = 3` kernel). -/
structure GreenDensity (d : ℕ) (g : Kernel d) : Prop where
  dim : d = 1 ∨ d = 2 ∨ d = 3
  meas : Measurable (Function.uncurry g)
  fin : ∀ s x, g s x ≠ ∞
  eq : ∀ s, waveGreen d s = volume.withDensity (g s)

/-- **`green1` is a Green density** (`G_s(dy) = ½ 1_{|y|<s} dy`). -/
theorem greenDensity_one : GreenDensity 1 DiagramModel.green1 := by
  refine ⟨Or.inl rfl, ?_, fun s x => ?_, DiagramModel.waveGreen_one_eq⟩
  · have hS : MeasurableSet {p : ℝ × Rd 1 | ‖p.2‖ < p.1} :=
      measurableSet_lt (by fun_prop) measurable_fst
    have : Function.uncurry DiagramModel.green1 =
        {p : ℝ × Rd 1 | ‖p.2‖ < p.1}.indicator fun _ => ENNReal.ofReal (1 / 2) := by
      funext p
      obtain ⟨s, y⟩ := p
      have hm : y ∈ Metric.ball (0 : Rd 1) s ↔ (s, y) ∈ {p : ℝ × Rd 1 | ‖p.2‖ < p.1} := by
        rw [Metric.mem_ball, dist_zero_right]; rfl
      show DiagramModel.green1 s y = _
      unfold DiagramModel.green1
      by_cases h : y ∈ Metric.ball (0 : Rd 1) s
      · rw [Set.indicator_of_mem (hm.1 h), Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem (mt hm.2 h), Set.indicator_of_notMem h]
    rw [this]
    exact measurable_const.indicator hS
  · unfold DiagramModel.green1
    by_cases h : x ∈ Metric.ball (0 : Rd 1) s
    · rw [Set.indicator_of_mem h]; exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem h]; exact ENNReal.zero_ne_top

/-- **`green2` is a Green density** (`G_s(dy) = (2π)^{-1}(s²-|y|²)_+^{-1/2} dy`); its joint
measurability is item E's (INTERFACE §4.10). -/
theorem greenDensity_two : GreenDensity 2 green2 := by
  refine ⟨Or.inr (Or.inl rfl), ?_, fun s x => ?_, waveGreen_two_eq⟩
  · have hS : MeasurableSet {p : ℝ × Rd 2 | ‖p.2‖ < p.1} :=
      measurableSet_lt (by fun_prop) measurable_fst
    have : Function.uncurry green2 =
        {p : ℝ × Rd 2 | ‖p.2‖ < p.1}.indicator
          fun p => ENNReal.ofReal ((2 * π * Real.sqrt (p.1 ^ 2 - ‖p.2‖ ^ 2))⁻¹) := by
      funext p
      obtain ⟨s, y⟩ := p
      have hm : y ∈ Metric.ball (0 : Rd 2) s ↔ (s, y) ∈ {p : ℝ × Rd 2 | ‖p.2‖ < p.1} := by
        rw [Metric.mem_ball, dist_zero_right]; rfl
      show green2 s y = _
      unfold green2
      by_cases h : y ∈ Metric.ball (0 : Rd 2) s
      · rw [Set.indicator_of_mem (hm.1 h), Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem (mt hm.2 h), Set.indicator_of_notMem h]
    rw [this]
    exact (ENNReal.measurable_ofReal.comp (by fun_prop)).indicator hS
  · unfold green2
    by_cases h : x ∈ Metric.ball (0 : Rd 2) s
    · rw [Set.indicator_of_mem h]; exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem h]; exact ENNReal.zero_ne_top

section Density

variable {g : Kernel d} (hgd : GreenDensity d g)
include hgd

theorem GreenDensity.meas_slice (s : ℝ) : Measurable (g s) :=
  hgd.meas.comp (measurable_const.prodMk measurable_id)

/-- The mass of a Green density: `∫ g(s,y) dy = G_s(ℝ^d) = s` for `s ≥ 0`. -/
theorem GreenDensity.lintegral_eq {s : ℝ} (hs : 0 ≤ s) : ∫⁻ y, g s y = ENNReal.ofReal s := by
  rw [← WaveGreen.waveGreen_mass d hgd.dim s hs, hgd.eq s, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

/-- The damped kernel is jointly measurable. -/
theorem GreenDensity.measurable_damp (θ : ℝ) : Measurable (Function.uncurry (damp θ g)) :=
  (ENNReal.measurable_ofReal.comp (by fun_prop)).mul hgd.meas

/-- The real density is integrable for `s ≥ 0`. -/
theorem GreenDensity.integrable_toReal {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun y => (g s y).toReal) := by
  refine integrable_toReal_of_lintegral_ne_top (hgd.meas_slice s).aemeasurable ?_
  rw [hgd.lintegral_eq hs]; exact ENNReal.ofReal_ne_top

/-- The real mass: `∫ g(s,y) dy = s` for `s ≥ 0`. -/
theorem GreenDensity.integral_toReal {s : ℝ} (hs : 0 ≤ s) : ∫ y, (g s y).toReal = s := by
  rw [MeasureTheory.integral_toReal (hgd.meas_slice s).aemeasurable
    (Filter.Eventually.of_forall fun y => lt_top_iff_ne_top.2 (hgd.fin s y)),
    hgd.lintegral_eq hs, ENNReal.toReal_ofReal hs]

/-- Integrals against `G_s` are integrals against the density. -/
theorem GreenDensity.integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℝ) (f : Rd d → E) : ∫ y, f y ∂waveGreen d s = ∫ y, (g s y).toReal • f y := by
  rw [hgd.eq s, integral_withDensity_eq_integral_toReal_smul (hgd.meas_slice s)
    (Filter.Eventually.of_forall fun y => lt_top_iff_ne_top.2 (hgd.fin s y))]

/-- The Fourier transform of a Green density is `waveHat`: `∫ e^{iξ·y} g(s,y) dy = Ĝ_s(ξ)`
(`WaveGreenFourier.waveGreen_fourier`, main TeX lines 983-984). -/
theorem GreenDensity.fourier {s : ℝ} (hs : 0 < s) (ξ : Rd d) :
    ∫ y, Complex.exp (Complex.I * (inner ℝ ξ y : ℝ)) * ((g s y).toReal : ℂ) =
      (waveHat s ξ : ℂ) := by
  rw [← (WaveGreenFourier.waveGreen_fourier d hgd.dim s hs ξ).2, hgd.integral_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Complex.real_smul]
  ring

/-- **`N_0` of the damped kernel**: `N_0(θ) = ∫_0^∞ e^{-θs} s ds = θ^{-2}` (`E:crude-norms`,
`E:homogeneous-norms`, TeX 1974 and 2387). -/
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

end Density

/-! ### The first norm -/

section First

variable {g : Kernel d} (hgd : GreenDensity d g)
include hgd

/-- **The Laplace-Fourier transform of the damped kernel**: for `θ ≥ 0` and `λ > 0`,
`∫_0^∞ ∫ e^{-λs + iξ·y} e^{-θs} g(s,y) dy ds = ((θ+λ)² + |ξ|²)⁻¹` (TeX 1000-1001, 1445-1450;
`WaveKernel.waveHat_laplace`). -/
theorem lapFour_damp {θ l : ℝ} (hθ : 0 ≤ θ) (hl : 0 < l) (ξ : Rd d) :
    lapFour (damp θ g) l ξ = ((1 / ((θ + l) ^ 2 + ‖ξ‖ ^ 2) : ℝ) : ℂ) := by
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
      (((Real.exp (-((θ + l) * s)) * waveHat s ξ) : ℝ) : ℂ) := by
    intro s hs
    simp only [hF]
    simp_rw [hform]
    rw [integral_const_mul, hgd.fourier hs ξ, Complex.ofReal_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_complex_ofReal,
    (WaveKernel.waveHat_laplace (θ + l) hq ξ).2]

/-- `‖((θ+λ)² + |ξ|²)⁻¹‖ₑ` for `λ > 0` (auxiliary). -/
theorem enorm_lapFour_damp {θ l : ℝ} (hθ : 0 ≤ θ) (hl : 0 < l) (ξ : Rd d) :
    ‖lapFour (damp θ g) l ξ‖ₑ = ENNReal.ofReal (1 / ((θ + l) ^ 2 + ‖ξ‖ ^ 2)) := by
  rw [lapFour_damp hgd hθ hl ξ, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]

/-- **`N_{1,e}` of the damped kernel with the M4 edge datum** is at most the damped norm
`N₁(θ) = Γ(α₀)⁻¹ ∫_0^∞ λ^{α₀-1} R_μ(θ+λ) dλ` of `L:damped-homogeneous-norms` (TeX 2018-2022: the
Gaussian multiplier is removed in the upper bound; `E:crude-norms`, `E:homogeneous-norms`). -/
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
        simp_rw [enorm_lapFour_damp hgd hθ.le hl]
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

/-- Auxiliary: the Gaussian multiplier as an `ℝ≥0`-valued function, so that
`DampedNormsHomog.smoothed μ (gaussMultNN ε) = smoothSpec μ ε` (definitionally). -/
def gaussMultNN (ε : ℝ) (ξ : Rd d) : NNReal := (gaussFactor ε ξ).toNNReal

theorem smoothed_gaussMultNN (μ : Measure (Rd d)) (ε : ℝ) :
    DampedNormsHomog.smoothed μ (gaussMultNN ε) = smoothSpec μ ε := rfl

theorem measurable_gaussMultNN (ε : ℝ) : Measurable (gaussMultNN (d := d) ε) := by
  unfold gaussMultNN gaussFactor; fun_prop

theorem gaussMultNN_le_one {ε : ℝ} (hε : 0 ≤ ε) (ξ : Rd d) : gaussMultNN ε ξ ≤ 1 := by
  unfold gaussMultNN
  rw [Real.toNNReal_le_one]
  exact LowAlphaConvolution.gaussFactor_le_one hε ξ

/-- **The capped Gamma mixture is the restricted kernel `K_S`** of `DampedNormsHomog` with
`S = (0, L]`: `κ_L(t) = Γ(a)⁻¹ ∫_{(0,L]} e^{-λ|t|} λ^{a-1} dλ`, finite also on the diagonal. -/
theorem kappaCap_nuE {a : ℝ} (ha : 0 < a) (L t : ℝ) :
    kappaCap (nuE a (Ioi 0)) L t = ENNReal.ofReal (DampedNormsHomog.KS a (Ioc 0 L) t) := by
  have hG : 0 < (Real.Gamma a)⁻¹ := inv_pos.2 (Real.Gamma_pos_of_pos ha)
  unfold kappaCap nuE DampedNormsHomog.KS
  rw [restrict_withDensity measurableSet_Ioc, lintegral_withDensity_eq_lintegral_mul _
    (by fun_prop) (by fun_prop), Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.2 Set.Ioc_subset_Ioi_self]
  have hcongr : ∀ l ∈ Ioc 0 L, ((fun l => ENNReal.ofReal ((Real.Gamma a)⁻¹ * l ^ (a - 1))) *
      fun l => ENNReal.ofReal (Real.exp (-(l * |t|)))) l =
      ENNReal.ofReal ((Real.Gamma a)⁻¹ * TimeFractional.subKernel a |t| l) := by
    intro l hl
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (mul_nonneg hG.le (Real.rpow_nonneg (le_of_lt hl.1) _)),
      TimeFractional.subKernel, mul_comm l |t|]
    ring_nf
  have hInt : IntegrableOn (fun l => TimeFractional.subKernel a |t| l) (Ioc 0 L) := by
    rcases le_or_gt L 0 with hL | hL
    · rw [Set.Ioc_eq_empty (not_lt.2 hL)]; exact integrableOn_empty
    · have hr : IntegrableOn (fun l : ℝ => l ^ (a - 1)) (Ioc 0 L) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).1
          (intervalIntegral.intervalIntegrable_rpow' (by linarith))
      refine hr.mono' ((by unfold TimeFractional.subKernel; fun_prop : Measurable fun l : ℝ =>
        TimeFractional.subKernel a |t| l).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
      rw [Real.norm_eq_abs, abs_of_nonneg (TimeFractional.subKernel_nonneg a |t| l
        (le_of_lt hl.1)), TimeFractional.subKernel]
      calc l ^ (a - 1) * Real.exp (-(|t| * l)) ≤ l ^ (a - 1) * 1 := by
            gcongr
            · exact Real.rpow_nonneg (le_of_lt hl.1) _
            · exact Real.exp_le_one_iff.2 (by nlinarith [abs_nonneg t, hl.1])
        _ = l ^ (a - 1) := mul_one _
  rw [setLIntegral_congr_fun measurableSet_Ioc hcongr, ← ofReal_integral_eq_lintegral_ofReal
    (hInt.const_mul _), integral_const_mul]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
  exact mul_nonneg hG.le (TimeFractional.subKernel_nonneg a |t| l (le_of_lt hl.1))

section Second

variable {g : Kernel d} (hgd : GreenDensity d g)
include hgd

/-- Auxiliary: `∫ g(s,x) cos(ξ·x) dx = Ĝ_s(ξ)` for `s > 0`. -/
theorem integral_cos {s : ℝ} (hs : 0 < s) (ξ : Rd d) :
    ∫ x, (g s x).toReal * Real.cos (inner ℝ ξ x) = waveHat s ξ := by
  have hI : Integrable fun x => Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) *
      ((g s x).toReal : ℂ) := by
    refine Integrable.mono' (hgd.integrable_toReal hs.le).norm
      ((by fun_prop : Continuous fun x : Rd d => Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))).aestronglyMeasurable.mul
        (Complex.measurable_ofReal.comp (ENNReal.measurable_toReal.comp
          (hgd.meas_slice s))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real]
  have hre := integral_re hI
  rw [hgd.fourier hs ξ] at hre
  have hr : RCLike.re ((waveHat s ξ : ℝ) : ℂ) = waveHat s ξ := Complex.ofReal_re _
  rw [hr] at hre
  rw [← hre]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [RCLike.re_to_complex, Complex.re_mul_ofReal]
  rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_re, mul_comm]

section Spatial

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
  {ε : ℝ} (hε : 0 < ε)
include hH hε

/-- Auxiliary: the inner spatial integral against the smoothed covariance,
`∫ g(r,y) γ_ε(x-y) dy = ∫ Ĝ_r(ξ) cos(ξ·x) e^{-ε|ξ|²/2} μ(dξ)`
(`LowAlphaConvolution.smoothed_pairing_spectral`). -/
theorem inner_spatial {r : ℝ} (hr : 0 < r) (x : Rd d) :
    ∫ y, (g r y).toReal * gammaEps Γ ε (x - y) =
      ∫ ξ, waveHat r ξ * Real.cos (inner ℝ ξ x) * gaussFactor ε ξ ∂μ := by
  have := hH.μ_radon
  have hfin := (WaveGreenFourier.greenFourier d hgd.dim).finite r hr
  obtain ⟨-, -, hint2, hrep⟩ := LowAlphaConvolution.smoothed_pairing_spectral hH.Γ_tempered
    hH.μ_tempered hH.spectral hε (waveGreen d r) (-x)
  have hL : ∫ y, gammaEps Γ ε (y + -x) ∂(waveGreen d r) =
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
  rw [(WaveGreenFourier.greenFourier d hgd.dim).fourier r hr ξ]
  rw [Complex.re_mul_ofReal, Complex.re_ofReal_mul, mul_comm Complex.I,
    Complex.exp_ofReal_mul_I_re, inner_neg_right, Real.cos_neg]

/-- Auxiliary: the spatial double integral is the smoothed spectral pairing,
`∫∫ g(s,x) g(r,y) γ_ε(x-y) dx dy = ∫ Ĝ_s Ĝ_r e^{-ε|ξ|²/2} dμ` (TeX 2018-2022, the "Fourier
Fubini" step). -/
theorem double_spatial {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ∫ x, (g s x).toReal * ∫ y, (g r y).toReal * gammaEps Γ ε (x - y) =
      ∫ ξ, waveHat s ξ * waveHat r ξ ∂(smoothSpec μ ε) := by
  have := hH.μ_radon
  have hgauss := LowAlphaConvolution.integrable_gaussFactor hH.μ_tempered hε
  simp_rw [inner_spatial hgd hH hε hr]
  have hF : Integrable (Function.uncurry fun (x : Rd d) (ξ : Rd d) =>
      (g s x).toReal * (waveHat r ξ * Real.cos (inner ℝ ξ x) * gaussFactor ε ξ))
      ((volume : Measure (Rd d)).prod μ) := by
    refine Integrable.mono' ((hgd.integrable_toReal hs.le).mul_prod (hgauss.const_mul |r|)) ?_
      (Filter.Eventually.of_forall fun p => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      refine Measurable.mul ((ENNReal.measurable_toReal.comp (hgd.meas_slice s)).comp
        measurable_fst) ?_
      have hw : Continuous fun ξ : Rd d => waveHat r ξ :=
        WaveKernel.waveHat_continuous.comp (continuous_const.prodMk continuous_id)
      exact ((hw.measurable.comp measurable_snd).mul (by fun_prop)).mul
        ((by unfold gaussFactor; fun_prop : Measurable fun ξ : Rd d => gaussFactor ε ξ).comp
          measurable_snd)
    · show |(g s p.1).toReal * (waveHat r p.2 * Real.cos (inner ℝ p.2 p.1) *
          gaussFactor ε p.2)| ≤ (g s p.1).toReal * (|r| * gaussFactor ε p.2)
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
        abs_of_pos (LowAlphaConvolution.gaussFactor_pos ε p.2)]
      have h1 := WaveKernel.abs_waveHat_le r p.2
      have h2 := Real.abs_cos_le_one (inner ℝ p.2 p.1)
      have h3 := (LowAlphaConvolution.gaussFactor_pos ε p.2).le
      have h4 : (0 : ℝ) ≤ (g s p.1).toReal := ENNReal.toReal_nonneg
      calc (g s p.1).toReal * (|waveHat r p.2| * |Real.cos (inner ℝ p.2 p.1)| *
            gaussFactor ε p.2)
          ≤ (g s p.1).toReal * (|r| * 1 * gaussFactor ε p.2) := by gcongr
        _ = (g s p.1).toReal * (|r| * gaussFactor ε p.2) := by ring
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hF, integral_smoothSpec]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  have : ∀ x, (g s x).toReal * (waveHat r ξ * Real.cos (inner ℝ ξ x) * gaussFactor ε ξ) =
      (waveHat r ξ * gaussFactor ε ξ) * ((g s x).toReal * Real.cos (inner ℝ ξ x)) :=
    fun x => by ring
  simp_rw [this]
  rw [integral_const_mul, integral_cos hgd hs ξ]
  ring

omit hgd hH in
/-- Auxiliary: the inner spatial integral is nonnegative. -/
theorem inner_spatial_nonneg (r : ℝ) (x : Rd d) :
    0 ≤ ∫ y, (g r y).toReal * gammaEps Γ ε (x - y) :=
  integral_nonneg fun _ => mul_nonneg ENNReal.toReal_nonneg
    (LowAlphaConvolution.gammaEps_nonneg Γ hε.le _)

omit hgd in
/-- Auxiliary: `γ_ε` is continuous and bounded by `∫ e^{-ε|ξ|²/2} dμ`. -/
theorem gammaEps_props : Continuous (gammaEps Γ ε) ∧
    ∀ z, gammaEps Γ ε z ≤ ∫ ξ, gaussFactor ε ξ ∂μ := by
  have := hH.μ_radon
  obtain ⟨hc, hb⟩ := LowAlphaConvolution.gammaEps_continuous_bounded hH.μ_tempered hH.spectral hε
  exact ⟨hc, fun z => (Real.le_norm_self _).trans (hb z)⟩

/-- **The spatial double lintegral** (`ℝ≥0∞` form): for `s, r > 0`,
`∫∫ g(s,x) g(r,y) γ_e(x-y) dx dy = ∫ Ĝ_s Ĝ_r dμ_e`, and the latter is nonnegative. -/
theorem lintegral_double_spatial {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    ∫⁻ x, ∫⁻ y, g s x * g r y * gammaOf (smoothSpec μ ε) (x - y) =
        ENNReal.ofReal (∫ ξ, waveHat s ξ * waveHat r ξ ∂(smoothSpec μ ε)) ∧
      0 ≤ ∫ ξ, waveHat s ξ * waveHat r ξ ∂(smoothSpec μ ε) := by
  obtain ⟨hc, hb⟩ := gammaEps_props hH hε
  set C := ∫ ξ, gaussFactor ε ξ ∂μ with hC
  have hγ : ∀ z, gammaOf (smoothSpec μ ε) z = ENNReal.ofReal (gammaEps Γ ε z) := fun z => by
    rw [gammaOf_smoothSpec hH hε, LowAlphaUpper.covEps_eq_ofReal hε.le
      (LowAlphaConvolution.integrable_heatDens hH.Γ_tempered hε)]
  have hgr : ∀ t y, g t y = ENNReal.ofReal (g t y).toReal := fun t y =>
    (ENNReal.ofReal_toReal (hgd.fin t y)).symm
  -- the inner integrand is integrable
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
  -- the outer integrand is integrable
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

/-- Auxiliary: Tonelli for the covariance quadratic form, `∫∫ dp dq = ∫ds ∫dr ∫dx ∫dy` with
`p = (s,x)`, `q = (r,y)`. -/
theorem lintegral_four (Φ : ℝ → Rd d → ℝ → Rd d → ℝ≥0∞)
    (hΦ : Measurable fun w : (ℝ × Rd d) × (ℝ × Rd d) => Φ w.1.1 w.1.2 w.2.1 w.2.2) :
    ∫⁻ p : ℝ × Rd d, ∫⁻ q : ℝ × Rd d, Φ p.1 p.2 q.1 q.2 =
      ∫⁻ s, ∫⁻ r, ∫⁻ x, ∫⁻ y, Φ s x r y := by
  have h1 : ∀ p : ℝ × Rd d, ∫⁻ q : ℝ × Rd d, Φ p.1 p.2 q.1 q.2 =
      ∫⁻ r, ∫⁻ y, Φ p.1 p.2 r y := by
    intro p
    rw [Measure.volume_eq_prod]
    exact lintegral_prod _ (hΦ.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hm0 := hΦ.lintegral_prod_right' (ν := (volume : Measure (ℝ × Rd d)))
  have hm : Measurable fun p : ℝ × Rd d => ∫⁻ r, ∫⁻ y, Φ p.1 p.2 r y := by
    have e : (fun p : ℝ × Rd d => ∫⁻ q : ℝ × Rd d, Φ p.1 p.2 q.1 q.2) =
        fun p => ∫⁻ r, ∫⁻ y, Φ p.1 p.2 r y := funext h1
    rw [← e]; exact hm0
  simp_rw [h1]
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun s => ?_
  refine lintegral_lintegral_swap ?_
  have hz : Measurable fun z : (Rd d × ℝ) × Rd d => Φ s z.1.1 z.1.2 z.2 :=
    hΦ.comp ((measurable_const.prodMk (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  exact (hz.lintegral_prod_right' (ν := (volume : Measure (Rd d)))).aemeasurable

/-- Auxiliary: the capped Gamma mixture is measurable in the time difference. -/
theorem measurable_kappaCap (ν : Measure ℝ) [SFinite ν] (L : ℝ) : Measurable (kappaCap ν L) := by
  unfold kappaCap
  exact (ENNReal.measurable_ofReal.comp (by fun_prop :
    Measurable fun p : ℝ × ℝ => Real.exp (-(p.2 * |p.1|)))).lintegral_prod_right'

section Assembly

variable {g : Kernel d} (hgd : GreenDensity d g)
  {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)} (hH : HomogCovariance d alpha α₀ Γ μ)
  {ε : ℝ} (hε : 0 < ε)
include hgd hH hε

/-- **The capped covariance quadratic form of the damped kernel** with the M4 edge datum is
the restricted damped norm of `DampedNormsHomog` with `S = (0, L]` and the Gaussian multiplier:
`Q_L(G^0, G^0) = N_{2, e^{-ε|·|²/2}, (0,L]}(θ)²`. -/
theorem QL_damp_eq {θ : ℝ} (hθ : 0 < θ) (L : ℝ) :
    QL (nuE α₀ (Ioi 0)) (smoothSpec μ ε) L (zeroExt (damp θ g)) (zeroExt (damp θ g)) =
      ENNReal.ofReal (DampedNormsHomog.N2onSq α₀ θ (Ioc 0 L) (smoothSpec μ ε)) := by
  have := hH.μ_radon
  obtain ⟨hR, hμ0⟩ := DampedNormsHomog.homog_spectral_facts hH
  obtain ⟨hI, -, -⟩ := DampedNormsHomog.N2onSq_smoothed_mono μ hR hμ0 α₀ θ hH.alpha0_pos
    hH.alpha0_lt_one hθ (gaussMultNN ε) (measurable_gaussMultNN ε) (gaussMultNN_le_one hε.le)
    (Ioc 0 L) univ measurableSet_Ioc MeasurableSet.univ (subset_univ _)
  rw [smoothed_gaussMultNN] at hI
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
        ENNReal.ofReal (DampedNormsHomog.N2onOuter α₀ θ (Ioc 0 L) (smoothSpec μ ε) (s, r))) r) s := by
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
        rw [(lintegral_double_spatial hgd hH hε hs0 hr0).1, hcdef, kappaCap_nuE hH.alpha0_pos,
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
  have hnn : 0 ≤ᵐ[TimeFractional.P2] DampedNormsHomog.N2onOuter α₀ θ (Ioc 0 L) (smoothSpec μ ε) := by
    filter_upwards [DampedNorms.ae_P2] with p hp
    unfold DampedNormsHomog.N2onOuter
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

/-- **`N_{2,e}` of the damped kernel with the M4 edge datum**: `N_{2,e}(θ)² ≤ N₂(θ)²` of
`L:damped-homogeneous-norms` (TeX 2018-2022: the Gaussian multiplier and the temporal cap are
removed in the upper bounds, `E:damped-multiplier-comparison`). -/
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
  have h := (DampedNormsHomog.N2onSq_smoothed_mono μ hR hμ0 α₀ θ hH.alpha0_pos
    hH.alpha0_lt_one hθ (gaussMultNN ε) (measurable_gaussMultNN ε) (gaussMultNN_le_one hε.le)
    (Ioc 0 (L : ℝ)) univ measurableSet_Ioc MeasurableSet.univ (subset_univ _)).2.2
  rwa [smoothed_gaussMultNN] at h

end Assembly

end StratonovichHAMSecondMoment.PairingDampedNorms
