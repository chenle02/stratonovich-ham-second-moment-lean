module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The covariance-smoothing assertion of `L:damped-homogeneous-norms` (Homogeneous
damped norms and temporal tails) of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` (revision 39f2597a): statement at
main TeX lines 1010-1055, proof at lines 1057-1154.  The sentence "Spatial Gaussian
smoothing and Gaussian smoothing of the Green kernel give multipliers in this
class" (lines 1052-1053) and its proof "Gaussian spatial and Green smoothing
contribute products of multipliers in `[0,1]` depending only on `ξ`" (lines
1150-1151).

Before this module the package proved only that the Gaussian factor
`e^{-η|ξ|²}` is a multiplier (`DampedMultiplier.isMultiplier_gaussMult`); the
spectral identification of the smoothed covariance `p_ε * Γ` was not stated
(`DampedMultiplier`, module docstring, "Narrower than the TeX").  It is proved
here.

Objects.
* `p_ε` is the centered Gaussian density with covariance `ε I`
  (`LowAlphaConvolution.heatDens ε`, `(2πε)^{-d/2} e^{-|w|²/(2ε)}`; the TeX fixes
  this normalization at lines 5346-5348 and 5915-5916, not in this lemma, which
  leaves the constant open).  Its Fourier multiplier is `e^{-ε|ξ|²/2}`, which is
  `DampedMultiplier.gaussMult (ε/2)`.  A normalization `p_ε = N(0, cεI)` is the
  case `ε ↦ cε` of the statements below, which hold for every `ε > 0`.
* The smoothed covariance `p_ε * Γ` is the measure `smoothedCov Γ ε` with
  Lebesgue density `γ_ε = LowAlphaConvolution.gammaEps Γ ε`,
  `γ_ε(x) = ∫ p_ε(x - y) Γ(dy)`.
* "Multipliers in this class" are `DampedMultiplier.IsMultiplier` (measurable,
  values in `[0,1]`, TeX lines 1033-1036); the spectral measure `mμ` is
  `DampedNormsHomog.smoothed μ m = μ.withDensity m`.

Formalized:
* `smoothedCov_spectral` (general form): for `μ` s-finite and tempered with
  `IsSpectralMeasure Γ μ` and `ε > 0`, the measure `p_ε * Γ` has spectral measure
  `e^{-ε|ξ|²/2} μ(dξ)`, in the package's sense (`HomogHypothesis.IsSpectralMeasure`:
  `∫ φ d(p_ε * Γ) = ∫ (∫ φ(x) e^{iξ·x} dx) e^{-ε|ξ|²/2} μ(dξ)` for every Schwartz
  `φ`).  Route: the pointwise identity `LowAlphaConvolution.gammaEps_spectral`,
  `γ_ε(x) = ∫ e^{iξ·x} e^{-ε|ξ|²/2} μ(dξ)`, then Fubini of
  `φ(x) e^{iξ·x} e^{-ε|ξ|²/2}` against Lebesgue measure times `μ`, which is
  absolutely integrable because `φ` is Lebesgue integrable and `e^{-ε|ξ|²/2}`
  is `μ`-integrable.  No Fubini against the infinite measure `Γ` is used (Le's
  decision 2 for wave L8).
* `smoothedCov_props`: `γ_ε ≥ 0`, continuous, bounded by `∫ e^{-ε|ξ|²/2} dμ`;
  `p_ε * Γ` is locally finite.
* `spatial_smoothing_multiplier`: the TeX's assertion in its exact form: there
  is a multiplier `m` in the class with `mμ` a spectral measure of `p_ε * Γ`,
  namely `m = e^{-ε|ξ|²/2}`.
* Auxiliary (no manuscript step; used by the refutations of this item):
  `spectral_gauss_test`, the Gaussian test function against a spectral measure
  `mμ`; `spectral_multiplier_separation`, if `m₂ ≤ m₁ ≤ 1` with `m₂ < m₁` off the
  origin and `μ({ξ ≠ 0}) ≠ 0`, then `m₁μ` and `m₂μ` are not both spectral measures
  of the same covariance (a partial uniqueness statement; the general one is
  `spectralMeasure_unique`).
* `spectralMeasure_unique`: two tempered spectral measures of the same `Γ'` are
  equal (Fourier uniqueness, from `Measure.ext_of_charFun` applied to the finite
  measures `e^{-|ξ|²/4} νᵢ(dξ)`, tested with translated Gaussians); with
  `smoothed_tempered`, `smoothedCov_spectral_unique_paper`: under `H:homog`,
  `e^{-ε|ξ|²/2} μ` is *the* tempered spectral measure of `p_ε * Γ`, so the TeX's
  "give multipliers in this class" holds in its strong reading.

Wrappers:
* `spatial_smoothing_multiplier_paper`: the same under `H:homog`
  (`HomogCovariance`); it uses the fields `μ_radon` (s-finiteness), `μ_tempered`
  and `spectral` only.
* `damped_homogeneous_norms_whole_paper`: `L:damped-homogeneous-norms` under
  `H:homog` alone, with the wave Green measures `waveGreen d`: the conclusions of
  `DampedMultiplier.damped_homogeneous_norms_full_wave` (finiteness, `N₂² ≥ 0`,
  `N₀`, the scaling identities, the tails `E:damped-tail-norms`, the whole display
  `E:damped-multiplier-comparison`, the class with the Gaussian multipliers and
  products, Green smoothing preserves the mass and `N₀`), of
  `WaveGreenFourier.damped_homogeneous_norms_fourier_wave` (the second norm of the
  Gaussian-smoothed Green measures is `N_{2,m,S}(θ)²` with `m = e^{-v|ξ|²}`, in
  every `d`), and the covariance smoothing above (with uniqueness of the
  tempered spectral measure) together with the comparison
  `E:damped-multiplier-comparison` applied to its multiplier.

What the wrapper does not state (reported, not hidden):
* `p_ε * Γ` is the measure with density `γ_ε`; it is not identified with
  Mathlib's `Measure.conv` of `N(0, εI)` and `Γ` (the package defines `γ_ε` as
  the convolution integral, as the TeX does).
* Commentary only (no Lean statement), as in `DampedMultiplier`: lines 1050-1051
  ("the scaling identities above are asserted for the original covariance
  only") and lines 1146-1147.

Hypotheses of `H:homog`: `damped_homogeneous_norms_whole_paper` passes `h` to the
two wrappers it combines, whose field use is documented in `DampedMultiplier` and
`WaveGreenFourier`; the covariance smoothing uses `μ_radon`, `μ_tempered` and
`spectral`.  No other field is used directly and no hypothesis is carried unused
by the general theorems (`SFinite μ`, `IsTempered μ`, `IsSpectralMeasure Γ μ`,
`0 < ε` are each used).  Lemmas marked "Auxiliary to the Lean proof route" have
no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.ClockCopy
public import StratonovichHAMSecondMoment.DampedNorms
public import StratonovichHAMSecondMoment.DampedNormsHomog
public import StratonovichHAMSecondMoment.DampedMultiplier
public import StratonovichHAMSecondMoment.WaveGreenFourier
public import StratonovichHAMSecondMoment.LowAlphaConvolution
public import StratonovichHAMSecondMoment.GaussianTest
public import StratonovichHAMSecondMoment.MaskedSpectralGrowth

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace StratonovichHAMSecondMoment.DampedSmoothing

open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open TimeFractional SpectralHomog DampedNorms ClockCopy DampedNormsHomog WaveKernel WaveGreen
  DampedMultiplier
open MaskedSpectralGrowth (integrable_gauss_zero)
open LowAlphaConvolution (gammaEps gaussFactor gammaEps_spectral gammaEps_nonneg
  gammaEps_continuous_bounded integrable_gaussFactor gaussFactor_pos)

variable {d : ℕ}

/-- The smoothed covariance `p_ε * Γ`, the measure on `ℝ^d` with Lebesgue density
`γ_ε(x) = ∫ p_ε(x - y) Γ(dy)` (`LowAlphaConvolution.gammaEps`). -/
def smoothedCov (Γ : Measure (Rd d)) (ε : ℝ) : Measure (Rd d) :=
  volume.withDensity fun x => ENNReal.ofReal (gammaEps Γ ε x)

/-- Auxiliary to the Lean proof route.  The Fourier multiplier of `p_ε` in the
class's form: `gaussMult (ε/2) = e^{-ε|ξ|²/2} = gaussFactor ε`. -/
theorem coe_gaussMult_half (ε : ℝ) (ξ : Rd d) :
    (gaussMult (ε / 2) ξ : ℝ) = gaussFactor ε ξ := by
  rw [coe_gaussMult, gaussFactor]
  congr 2
  ring

/-- Properties of the smoothed covariance (`ε > 0`, `μ` tempered with
`IsSpectralMeasure Γ μ`): its density `γ_ε` is nonnegative, continuous and
bounded by `∫ e^{-ε|ξ|²/2} dμ`, and `p_ε * Γ` is a locally finite measure. -/
theorem smoothedCov_props {Γ μ : Measure (Rd d)} (hμt : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) {ε : ℝ} (hε : 0 < ε) :
    (∀ x, 0 ≤ gammaEps Γ ε x) ∧ Continuous (gammaEps Γ ε) ∧
      (∀ x, gammaEps Γ ε x ≤ ∫ ξ, gaussFactor ε ξ ∂μ) ∧
      IsLocallyFiniteMeasure (smoothedCov Γ ε) := by
  obtain ⟨hc, hb⟩ := gammaEps_continuous_bounded hμt hsp hε
  refine ⟨gammaEps_nonneg Γ hε.le, hc, fun x => (le_abs_self _).trans (hb x), ?_⟩
  unfold smoothedCov
  exact IsLocallyFiniteMeasure.withDensity_ofReal hc

/-- **Spectral identification of the smoothed covariance** (the covariance half of
"Spatial Gaussian smoothing ... give multipliers in this class",
`L:damped-homogeneous-norms`, main TeX lines 1052-1053, proof lines 1150-1151).  Let
`μ` be s-finite and tempered with `IsSpectralMeasure Γ μ` and `ε > 0`.  Then
`e^{-ε|ξ|²/2} μ(dξ)` is a spectral measure of `p_ε * Γ`: for every Schwartz `φ`,
`∫ φ(x) γ_ε(x) dx = ∫ (∫ φ(x) e^{iξ·x} dx) e^{-ε|ξ|²/2} μ(dξ)`.  Fubini is used
against Lebesgue measure times `μ` only. -/
theorem smoothedCov_spectral {Γ μ : Measure (Rd d)} [SFinite μ] (hμt : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) {ε : ℝ} (hε : 0 < ε) :
    IsSpectralMeasure (smoothedCov Γ ε) (smoothed μ (gaussMult (ε / 2))) := by
  intro φ
  obtain ⟨hc, -⟩ := gammaEps_continuous_bounded hμt hsp hε
  have hm := integrable_gaussFactor hμt hε
  set E : Rd d → Rd d → ℂ := fun x ξ => Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))
    with hE
  have hEc : Continuous (Function.uncurry E) := by
    simp only [hE, Function.uncurry_def]
    fun_prop
  have hEn : ∀ x ξ, ‖E x ξ‖ = 1 := by
    intro x ξ
    simp only [hE]
    rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I]
  set F : Rd d → Rd d → ℂ := fun x ξ => φ x * E x ξ * (gaussFactor ε ξ : ℂ) with hF
  have hFn : ∀ x ξ, ‖F x ξ‖ = ‖φ x‖ * gaussFactor ε ξ := by
    intro x ξ
    simp only [hF, norm_mul, hEn, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (gaussFactor_pos ε ξ)]
  have hFc : Continuous (Function.uncurry F) := by
    have h1 : Continuous fun p : Rd d × Rd d => φ p.1 := φ.continuous.comp continuous_fst
    have h2 : Continuous fun p : Rd d × Rd d => (gaussFactor ε p.2 : ℂ) := by
      simp only [gaussFactor]
      fun_prop
    exact (h1.mul hEc).mul h2
  have hφ : Integrable (fun x => φ x) (volume : Measure (Rd d)) := φ.integrable
  have hprod : Integrable (Function.uncurry F) ((volume : Measure (Rd d)).prod μ) := by
    refine Integrable.mono' (hφ.norm.mul_prod hm) hFc.aestronglyMeasurable
      (Eventually.of_forall fun p => (hFn p.1 p.2).le)
  -- left side: integrate against the density, then insert the pointwise identity
  have hL : ∫ x, φ x ∂(smoothedCov Γ ε) = ∫ x, ∫ ξ, F x ξ ∂μ := by
    unfold smoothedCov
    rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [ENNReal.toReal_ofReal (gammaEps_nonneg Γ hε.le x), Complex.real_smul,
      gammaEps_spectral hsp hε x, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hF, hE]
    ring
  -- right side: integrate against the multiplier
  have hR : ∫ ξ, (∫ x, φ x * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)))
      ∂(smoothed μ (gaussMult (ε / 2))) = ∫ ξ, ∫ x, F x ξ ∂(volume : Measure (Rd d)) ∂μ := by
    unfold smoothed
    rw [integral_withDensity_eq_integral_smul (by
      have := (isMultiplier_gaussMult (d := d) (ε / 2) (by positivity)).1
      exact this)]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only
    rw [NNReal.smul_def, coe_gaussMult_half, Complex.real_smul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF, hE]
    ring
  rw [hL, hR, integral_integral_swap hprod]

/-- `L:damped-homogeneous-norms`, spatial covariance smoothing (main TeX lines
1052-1053, proof 1150-1151), in the TeX's form: for `ε > 0` there is a multiplier `m`
in the class (`IsMultiplier`: measurable, values in `[0,1]`) such that `mμ` is a
spectral measure of `p_ε * Γ`; it is `m = e^{-ε|ξ|²/2}`.  General form: `μ`
s-finite and tempered, `IsSpectralMeasure Γ μ`. -/
theorem spatial_smoothing_multiplier {Γ μ : Measure (Rd d)} [SFinite μ]
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : Rd d → ℝ≥0, IsMultiplier m ∧ (∀ ξ, (m ξ : ℝ) = Real.exp (-(ε * ‖ξ‖ ^ 2 / 2))) ∧
      IsSpectralMeasure (smoothedCov Γ ε) (smoothed μ m) :=
  ⟨gaussMult (ε / 2), isMultiplier_gaussMult _ (by positivity),
    fun ξ => coe_gaussMult_half ε ξ, smoothedCov_spectral hμt hsp hε⟩

/-! ### Testing a smoothed spectral measure against a Gaussian -/

/-- Auxiliary to the Lean proof route (used by the refutations of this item).
If `mμ` is a spectral measure of `Γ'` (`m` measurable), the Gaussian test
function `e^{-|x|²}` (`GaussianTest.gaussTest 1`) has
`∫ e^{-|x|²} Γ'(dx) = π^{d/2} ∫ e^{-|ξ|²/4} m(ξ) μ(dξ)`. -/
theorem spectral_gauss_test {Γ' μ : Measure (Rd d)} {m : Rd d → ℝ≥0} (hm : Measurable m)
    (hsp : IsSpectralMeasure Γ' (smoothed μ m)) :
    ∫ x, GaussianTest.gaussTest 1 one_pos 0 0 x ∂Γ' =
      ((π ^ ((d : ℝ) / 2) * ∫ ξ, Real.exp (-(‖ξ‖ ^ 2 / 4)) * (m ξ : ℝ) ∂μ : ℝ) : ℂ) := by
  have hc : (∫ ξ, ((Real.exp (-(‖ξ‖ ^ 2 / 4)) * (m ξ : ℝ) : ℝ) : ℂ) ∂μ) =
      ((∫ ξ, Real.exp (-(‖ξ‖ ^ 2 / 4)) * (m ξ : ℝ) ∂μ : ℝ) : ℂ) := integral_ofReal
  rw [hsp, smoothed, integral_withDensity_eq_integral_smul hm, Complex.ofReal_mul, ← hc,
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [GaussianTest.gaussTest_fourier, NNReal.smul_def, Complex.real_smul]
  simp only [inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    sub_zero, div_one]
  push_cast
  ring

/-- Auxiliary to the Lean proof route (a separation statement used by the
refutations).  Let `μ` be tempered with `μ({ξ ≠ 0}) ≠ 0`, and `m₂ ≤ m₁ ≤ 1`
measurable with `m₂ < m₁` off the origin.  If `m₁μ` is a spectral measure of
`Γ'`, then `m₂μ` is not. -/
theorem spectral_multiplier_separation {Γ' μ : Measure (Rd d)} (hμt : IsTempered μ)
    (hμ0 : μ {0}ᶜ ≠ 0) {m₁ m₂ : Rd d → ℝ≥0} (h₁ : Measurable m₁) (h₂ : Measurable m₂)
    (hb : ∀ ξ, m₁ ξ ≤ 1) (hle : ∀ ξ, m₂ ξ ≤ m₁ ξ) (hlt : ∀ ξ, ξ ≠ 0 → m₂ ξ < m₁ ξ)
    (hs₁ : IsSpectralMeasure Γ' (smoothed μ m₁)) : ¬ IsSpectralMeasure Γ' (smoothed μ m₂) := by
  intro hs₂
  have e := (spectral_gauss_test h₁ hs₁).symm.trans (spectral_gauss_test h₂ hs₂)
  rw [Complex.ofReal_inj] at e
  have hπ : 0 < π ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hI := mul_left_cancel₀ hπ.ne' e
  have hg := integrable_gauss_zero hμt (c := 1 / 4) (by norm_num)
  have hgc : Continuous fun ξ : Rd d => Real.exp (-(‖ξ‖ ^ 2 / 4)) := by fun_prop
  have hint : ∀ m : Rd d → ℝ≥0, Measurable m → (∀ ξ, m ξ ≤ 1) →
      Integrable (fun ξ => Real.exp (-(‖ξ‖ ^ 2 / 4)) * (m ξ : ℝ)) μ := by
    intro m hm hm1
    refine hg.mono' (hgc.aestronglyMeasurable.mul hm.coe_nnreal_real.aestronglyMeasurable)
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, NNReal.norm_eq]
    calc Real.exp (-(‖ξ‖ ^ 2 / 4)) * (m ξ : ℝ) ≤ Real.exp (-(‖ξ‖ ^ 2 / 4)) * 1 :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hm1 ξ) (Real.exp_pos _).le
      _ = Real.exp (-(1 / 4 * ‖ξ‖ ^ 2)) := by ring_nf
  have i₁ := hint m₁ h₁ hb
  have i₂ := hint m₂ h₂ fun ξ => (hle ξ).trans (hb ξ)
  set f : Rd d → ℝ := fun ξ => Real.exp (-(‖ξ‖ ^ 2 / 4)) * ((m₁ ξ : ℝ) - m₂ ξ) with hf
  have hfi : Integrable f μ := by
    refine (i₁.sub i₂).congr (Eventually.of_forall fun ξ => ?_)
    simp only [hf, Pi.sub_apply]
    ring
  have hf0 : 0 ≤ f := fun ξ =>
    mul_nonneg (Real.exp_pos _).le (sub_nonneg.2 (by exact_mod_cast hle ξ))
  have hsupp : {0}ᶜ ⊆ Function.support f := by
    intro ξ hξ
    simp only [Function.mem_support, hf]
    exact mul_ne_zero (Real.exp_pos _).ne'
      (sub_ne_zero.2 (ne_of_gt (by exact_mod_cast hlt ξ hξ)))
  have hpos : 0 < ∫ ξ, f ξ ∂μ :=
    (integral_pos_iff_support_of_nonneg hf0 hfi).2
      (lt_of_lt_of_le (pos_iff_ne_zero.2 hμ0) (measure_mono hsupp))
  have hdiff : ∫ ξ, f ξ ∂μ = (∫ ξ, Real.exp (-(‖ξ‖ ^ 2 / 4)) * (m₁ ξ : ℝ) ∂μ) -
      ∫ ξ, Real.exp (-(‖ξ‖ ^ 2 / 4)) * (m₂ ξ : ℝ) ∂μ := by
    rw [← integral_sub i₁ i₂]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [hf]
    ring
  rw [hdiff, hI, sub_self] at hpos
  exact lt_irrefl _ hpos

/-! ### Uniqueness of the spectral measure in the tempered class -/

/-- Auxiliary to the Lean proof route.  For a spectral measure `ν` of `Γ'`, the
characteristic function of the finite measure `e^{-|ξ|²/4} ν(dξ)` at `w` is
`π^{-d/2} ∫ e^{-|x-w|²} Γ'(dx)` (the Gaussian test function translated to `w`). -/
theorem charFun_gaussWeighted {Γ' ν : Measure (Rd d)} (hs : IsSpectralMeasure Γ' ν)
    (w : Rd d) :
    charFun (ν.withDensity fun ξ => ENNReal.ofReal (Real.exp (-(‖ξ‖ ^ 2 / 4)))) w =
      (((π ^ ((d : ℝ) / 2))⁻¹ : ℝ) : ℂ) * ∫ x, GaussianTest.gaussTest 1 one_pos w 0 x ∂Γ' := by
  have hπ : 0 < π ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  rw [MaskedSpectralGrowth.spectral_gaussTest hs 1 one_pos w 0, charFun_apply,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]
  simp only [sub_zero, div_one, mul_one]
  rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hπ.ne',
    Complex.ofReal_one, one_mul, mul_comm Complex.I, real_inner_comm]
  ring

/-- **Uniqueness of the spectral measure** in the tempered class (Fourier
uniqueness; used to read "give multipliers in this class", main TeX lines 1052-1053,
as a statement about *the* spectral measure).  If `ν₁` and `ν₂` are tempered
spectral measures of the same `Γ'` (`IsSpectralMeasure`, the package's convention),
then `ν₁ = ν₂`.  Route: testing with the translated Gaussians `e^{-|x-w|²}` shows
that the finite measures `e^{-|ξ|²/4} νᵢ(dξ)` have the same characteristic
function (`charFun_gaussWeighted`), so they are equal (`Measure.ext_of_charFun`);
multiplying back by `e^{|ξ|²/4}` gives `ν₁ = ν₂`. -/
theorem spectralMeasure_unique {Γ' ν₁ ν₂ : Measure (Rd d)} (h₁ : IsTempered ν₁)
    (h₂ : IsTempered ν₂) (hs₁ : IsSpectralMeasure Γ' ν₁) (hs₂ : IsSpectralMeasure Γ' ν₂) :
    ν₁ = ν₂ := by
  have hfin : ∀ ν : Measure (Rd d), IsTempered ν →
      IsFiniteMeasure (ν.withDensity fun ξ => ENNReal.ofReal (Real.exp (-(‖ξ‖ ^ 2 / 4)))) := by
    intro ν h
    refine isFiniteMeasure_withDensity_ofReal ?_
    have hg := integrable_gauss_zero h (c := 1 / 4) (by norm_num)
    refine (hg.congr (Eventually.of_forall fun ξ => ?_)).2
    simp only
    ring_nf
  have hρ : (ν₁.withDensity fun ξ => ENNReal.ofReal (Real.exp (-(‖ξ‖ ^ 2 / 4)))) =
      ν₂.withDensity fun ξ => ENNReal.ofReal (Real.exp (-(‖ξ‖ ^ 2 / 4))) := by
    have := hfin ν₁ h₁
    have := hfin ν₂ h₂
    exact Measure.ext_of_charFun (funext fun w => by
      rw [charFun_gaussWeighted hs₁, charFun_gaussWeighted hs₂])
  have hback : ∀ ν : Measure (Rd d), ν =
      (ν.withDensity fun ξ => ENNReal.ofReal (Real.exp (-(‖ξ‖ ^ 2 / 4)))).withDensity
        fun ξ => ENNReal.ofReal (Real.exp (‖ξ‖ ^ 2 / 4)) := by
    intro ν
    rw [← withDensity_mul ν (by fun_prop) (by fun_prop)]
    conv_lhs => rw [← withDensity_one (μ := ν)]
    congr 1
    funext ξ
    simp only [Pi.mul_apply, Pi.one_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, ENNReal.ofReal_one]
  rw [hback ν₁, hρ, ← hback ν₂]

/-- Auxiliary to the Lean proof route.  Multiplying a tempered measure by a
multiplier with values in `[0,1]` keeps it tempered. -/
theorem smoothed_tempered {μ : Measure (Rd d)} (hμt : IsTempered μ) {m : Rd d → ℝ≥0}
    (hm : Measurable m) (hm1 : ∀ ξ, m ξ ≤ 1) : IsTempered (smoothed μ m) := by
  obtain ⟨k, hk⟩ := hμt
  refine ⟨k, lt_of_le_of_lt ?_ hk⟩
  unfold smoothed
  rw [lintegral_withDensity_eq_lintegral_mul μ hm.coe_nnreal_ennreal (by fun_prop)]
  refine lintegral_mono fun ξ => ?_
  simp only [Pi.mul_apply]
  calc (m ξ : ℝ≥0∞) * ENNReal.ofReal ((1 + ‖ξ‖) ^ (-(k : ℝ)))
      ≤ 1 * ENNReal.ofReal ((1 + ‖ξ‖) ^ (-(k : ℝ))) := by
        gcongr
        exact_mod_cast hm1 ξ
    _ = _ := one_mul _

/-- **`p_ε * Γ` has a unique tempered spectral measure, and it is `e^{-ε|ξ|²/2} μ`**
(main TeX lines 1052-1053, proof 1150-1151, under `H:homog`): for `ε > 0`, the measure
`e^{-ε|ξ|²/2} μ(dξ)` is tempered and a spectral measure of `p_ε * Γ`, and every
tempered spectral measure of `p_ε * Γ` equals it.  Uses the fields `μ_radon`,
`μ_tempered` and `spectral` of `h`. -/
theorem smoothedCov_spectral_unique_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (ε : ℝ) (hε : 0 < ε) :
    IsTempered (smoothed μ (gaussMult (ε / 2))) ∧
      IsSpectralMeasure (smoothedCov Γ ε) (smoothed μ (gaussMult (ε / 2))) ∧
      ∀ ν : Measure (Rd d), IsTempered ν → IsSpectralMeasure (smoothedCov Γ ε) ν →
        ν = smoothed μ (gaussMult (ε / 2)) := by
  have := h.μ_radon
  have hm := isMultiplier_gaussMult (d := d) (ε / 2) (by positivity)
  have ht := smoothed_tempered h.μ_tempered hm.1 hm.2
  have hsp := smoothedCov_spectral h.μ_tempered h.spectral hε
  exact ⟨ht, hsp, fun ν hν hs => spectralMeasure_unique hν ht hs hsp⟩

/-- `spatial_smoothing_multiplier` under `H:homog` (`HomogCovariance`), for every
`ε > 0`, with the properties of `smoothedCov_props`.  Uses the fields `μ_radon`,
`μ_tempered` and `spectral` of `h`. -/
theorem spatial_smoothing_multiplier_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (ε : ℝ) (hε : 0 < ε) :
    IsLocallyFiniteMeasure (smoothedCov Γ ε) ∧ (∀ x, 0 ≤ gammaEps Γ ε x) ∧
      IsMultiplier (gaussMult (d := d) (ε / 2)) ∧
      (∀ ξ : Rd d, (gaussMult (ε / 2) ξ : ℝ) = Real.exp (-(ε * ‖ξ‖ ^ 2 / 2))) ∧
      IsSpectralMeasure (smoothedCov Γ ε) (smoothed μ (gaussMult (ε / 2))) := by
  have := h.μ_radon
  obtain ⟨h0, -, -, hlf⟩ := smoothedCov_props h.μ_tempered h.spectral hε
  exact ⟨hlf, h0, isMultiplier_gaussMult _ (by positivity), fun ξ => coe_gaussMult_half ε ξ,
    smoothedCov_spectral h.μ_tempered h.spectral hε⟩

/-- **`L:damped-homogeneous-norms`** (main TeX lines 1010-1055, proof 1057-1154) under
`H:homog` alone, with the wave Green measures `G_s = waveGreen d s`.  Conclusions:
1. (A) the conclusions of `DampedMultiplier.damped_homogeneous_norms_full_wave`:
   finiteness (integrability statements), `N₂(θ)² ≥ 0`, `N₀(θ) = θ^{-2}`, the
   scaling identities, the tails `E:damped-tail-norms`, the whole display
   `E:damped-multiplier-comparison` for every multiplier in the class, the class
   contains `e^{-η|ξ|²}` (`η ≥ 0`) and is closed under products, and Gaussian Green
   smoothing preserves the mass identity and `N₀`;
2. (B) Gaussian smoothing of the Green kernel gives a multiplier: for `v ≥ 0`,
   `θ > 0`, measurable `S ⊆ S'`, the second norm of `p_v * G` is
   `N_{2,m,S}(θ)²` with `m = e^{-v|ξ|²}`, in `[0, N_{2,1,S'}(θ)²]`, with
   integrability (`WaveGreenFourier.damped_homogeneous_norms_fourier_wave`);
3. (C) spatial Gaussian smoothing gives a multiplier: for `ε > 0`,
   `m = e^{-ε|ξ|²/2}` is in the class, `mμ` is tempered and is *the* tempered
   spectral measure of the smoothed covariance `p_ε * Γ` (`smoothedCov_spectral`,
   `spectralMeasure_unique`), and the comparison
   `E:damped-multiplier-comparison` holds for it: for `θ > 0` and measurable
   `S ⊆ S'`, `0 ≤ N_{1,m,S}(θ) ≤ N_{1,1,S'}(θ)` and
   `0 ≤ N_{2,m,S}(θ)² ≤ N_{2,1,S'}(θ)²`.
The smoothed norms in (C) are therefore those of the unique tempered spectral
measure of `p_ε * Γ`. -/
theorem damped_homogeneous_norms_whole_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) :
    ((∀ θ : ℝ, 0 < θ →
      (Integrable (N2integrand (d := d) alpha0 θ) (P2.prod μ) ∧
        Integrable (fun p : ℝ × ℝ => Real.exp (-(θ * (p.1 + p.2))) * |p.1 - p.2| ^ (-alpha0) *
          ∫ ξ, waveHat p.1 ξ * waveHat p.2 ξ ∂μ) P2 ∧
        Integrable (fun l : ℝ => l ^ (alpha0 - 1) * resolvent μ (θ + l)) L0) ∧
      0 ≤ N2sq alpha0 θ μ ∧
      IntegrableOn (fun s => Real.exp (-(θ * s)) * (waveGreen d s univ).toReal) (Ioi 0) ∧
      N0 (waveGreen d) θ = θ ^ (-(2 : ℝ)) ∧
      N1 alpha0 θ μ = θ ^ (alpha + alpha0 - 2) * N1 alpha0 1 μ ∧
      N2sq alpha0 θ μ = θ ^ (-(4 - alpha - alpha0)) * N2sq alpha0 1 μ) ∧
    (∀ M : ℝ, Integrable (N2onIntegrand (d := d) alpha0 1 (Ioi M)) (P2.prod μ) ∧
      Integrable (N2onOuter alpha0 1 (Ioi M) μ) P2 ∧ 0 ≤ N2tailSq alpha0 M μ) ∧
    Tendsto (fun M => N1tail alpha0 M μ) atTop (𝓝 0) ∧
    Tendsto (fun M => N2tailSq alpha0 M μ) atTop (𝓝 0) ∧
    Tendsto (fun M => N2tail alpha0 M μ) atTop (𝓝 0) ∧
    (∀ θ : ℝ, 0 < θ → ∀ g : Rd d → ℝ≥0, IsMultiplier g →
      ∀ S S' : Set ℝ, MeasurableSet S → MeasurableSet S' → S ⊆ S' →
        Integrable (fun l : ℝ => l ^ (alpha0 - 1) * resolvent (smoothed μ g) (θ + l)) L0 ∧
        0 ≤ N1on alpha0 θ S (smoothed μ g) ∧
        N1on alpha0 θ S (smoothed μ g) ≤ N1on alpha0 θ S' μ ∧
        Integrable (N2onOuter alpha0 θ S (smoothed μ g)) P2 ∧
        Integrable (N2onOuter alpha0 θ S' μ) P2 ∧
        0 ≤ N2onSq alpha0 θ S (smoothed μ g) ∧
        N2onSq alpha0 θ S (smoothed μ g) ≤ N2onSq alpha0 θ S' μ) ∧
    (∀ η : ℝ, 0 ≤ η → IsMultiplier (gaussMult (d := d) η)) ∧
    (∀ g g' : Rd d → ℝ≥0, IsMultiplier g → IsMultiplier g' → IsMultiplier (g * g')) ∧
    (∀ v : ℝ, 0 ≤ v →
      GreenMass (fun s => gaussKernel v ∗ waveGreen d s) ∧
      (∀ θ : ℝ, 0 < θ →
        IntegrableOn (fun s => Real.exp (-(θ * s)) *
          ((gaussKernel v ∗ waveGreen d s) univ).toReal) (Ioi 0) ∧
        N0 (fun s => gaussKernel v ∗ waveGreen d s) θ = N0 (waveGreen d) θ ∧
        N0 (fun s => gaussKernel v ∗ waveGreen d s) θ = θ ^ (-(2 : ℝ))) ∧
      (∀ θ : ℝ, ∀ S : Set ℝ,
        N2GreenSq alpha0 θ S μ (fun s => gaussKernel v ∗ waveGreen d s) =
          N2GreenSq alpha0 θ S (smoothed μ (gaussMult v)) (waveGreen d)))) ∧
    (∀ v : ℝ, 0 ≤ v → ∀ θ : ℝ, 0 < θ → ∀ S S' : Set ℝ, MeasurableSet S →
      MeasurableSet S' → S ⊆ S' →
      Integrable (N2GreenOuter alpha0 θ S μ (waveGreen d)) P2 ∧
      N2GreenSq alpha0 θ S μ (waveGreen d) = (N2onSq alpha0 θ S μ : ℂ) ∧
      Integrable (N2GreenOuter alpha0 θ S μ (fun s => gaussKernel v ∗ waveGreen d s)) P2 ∧
      N2GreenSq alpha0 θ S μ (fun s => gaussKernel v ∗ waveGreen d s) =
        (N2onSq alpha0 θ S (smoothed μ (gaussMult v)) : ℂ) ∧
      Integrable (N2onOuter alpha0 θ S (smoothed μ (gaussMult v))) P2 ∧
      Integrable (N2onOuter alpha0 θ S' μ) P2 ∧
      0 ≤ N2onSq alpha0 θ S (smoothed μ (gaussMult v)) ∧
      N2onSq alpha0 θ S (smoothed μ (gaussMult v)) ≤ N2onSq alpha0 θ S' μ) ∧
    (∀ ε : ℝ, 0 < ε →
      IsMultiplier (gaussMult (d := d) (ε / 2)) ∧
      (∀ ξ : Rd d, (gaussMult (ε / 2) ξ : ℝ) = Real.exp (-(ε * ‖ξ‖ ^ 2 / 2))) ∧
      IsSpectralMeasure (smoothedCov Γ ε) (smoothed μ (gaussMult (ε / 2))) ∧
      IsTempered (smoothed μ (gaussMult (ε / 2))) ∧
      (∀ ν : Measure (Rd d), IsTempered ν → IsSpectralMeasure (smoothedCov Γ ε) ν →
        ν = smoothed μ (gaussMult (ε / 2))) ∧
      ∀ θ : ℝ, 0 < θ → ∀ S S' : Set ℝ, MeasurableSet S → MeasurableSet S' → S ⊆ S' →
        0 ≤ N1on alpha0 θ S (smoothed μ (gaussMult (ε / 2))) ∧
        N1on alpha0 θ S (smoothed μ (gaussMult (ε / 2))) ≤ N1on alpha0 θ S' μ ∧
        0 ≤ N2onSq alpha0 θ S (smoothed μ (gaussMult (ε / 2))) ∧
        N2onSq alpha0 θ S (smoothed μ (gaussMult (ε / 2))) ≤ N2onSq alpha0 θ S' μ) := by
  have A := damped_homogeneous_norms_full_wave h
  refine ⟨A, fun v hv θ hθ S S' hS hS' hSS =>
    WaveGreenFourier.damped_homogeneous_norms_fourier_wave h v hv θ hθ S S' hS hS' hSS,
    fun ε hε => ?_⟩
  obtain ⟨-, -, hm, hval, hsp⟩ := spatial_smoothing_multiplier_paper h ε hε
  obtain ⟨ht, -, hu⟩ := smoothedCov_spectral_unique_paper h ε hε
  refine ⟨hm, hval, hsp, ht, hu, fun θ hθ S S' hS hS' hSS => ?_⟩
  obtain ⟨-, h1, h2, -, -, h3, h4⟩ := A.2.2.2.2.2.1 θ hθ _ hm S S' hS hS' hSS
  exact ⟨h1, h2, h3, h4⟩

end StratonovichHAMSecondMoment.DampedSmoothing
