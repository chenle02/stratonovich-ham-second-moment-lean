module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`L:low-alpha-convolution` (Low-`α` convolution bound) of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` (revision a284420): statement
at main TeX lines 4702-4716 (displays `E:low-alpha-radial`, lines 4704-4708,
and `E:low-alpha-convolution`, lines 4710-4714), proof at lines 4718-4757,
standing assumptions of the subsection at lines 4691-4700.

Objects (the TeX's notation, lines 4695-4698):
* `V = μ({ξ : |ξ| ≤ 1})` is `specV μ` (the closed unit ball, as in the TeX;
  `SpectralMassIdentity.ralpha` uses the open ball for `R_α`, a different
  constant);
* `min{h, |ξ|^{-1}}` is `lowKernel h`, with the value `h` at `ξ = 0` (where
  `|ξ|^{-1} = ∞`), not Lean's junk `min h 0⁻¹ = 0`;
* `p_ε` is the centered Gaussian density with covariance `ε I`
  (`heatDens ε`, `(2πε)^{-d/2} e^{-|w|²/(2ε)}`; the TeX fixes this
  normalization at lines 4513-4515 and 5004-5005, not inside the lemma), and
  `γ_ε = p_ε * Γ` is `gammaEps Γ ε`, `γ_ε(x) = ∫ p_ε(x - y) Γ(dy)`;
* `G_{h,η} = p_η * G_h` is `smoothedGreen G h η = gaussKernel η ∗ G h`
  (`DampedMultiplier.gaussKernel η = N(0, ηI)`); for `η = 0` it is `G_h`
  (`smoothedGreen_zero`), so the TeX's convention `G_{h,0} = G_h` is a theorem;
* the wave kernel `G_h` is `WaveGreen.waveGreen d h` in the wrappers (the
  `d = 3` sphere measure being the recorded `toSphere` definitional choice of
  `WaveGreen`), any family `G` in the general theorem.

Formalized:
* `measure_closedBall_eq`: `μ({|ξ| ≤ R}) = V R^α`, `R > 0`, from
  `μ(cA) = c^α μ(A)` (first display of `E:low-alpha-radial`);
* `integral_lowKernel`: `V < ∞`, `min{h, |ξ|^{-1}}` is `μ`-integrable and
  `∫ min{h, |ξ|^{-1}} dμ = V h^{1-α}/(1-α)` for `h > 0`, `α < 1` (second
  display of `E:low-alpha-radial`), by the layer-cake formula as in the TeX;
* the Gaussian spectral representation (the "Fourier Fubini" step that the
  TeX invokes at lines 4736-4738 without displaying it):
  `gammaEps_spectral`, `γ_ε(x) = ∫ e^{iξ·x} e^{-ε|ξ|²/2} μ(dξ)`, and
  **`smoothed_pairing_spectral`**: for every finite measure `G`, `ε > 0`,
  `z ∈ ℝ^d`, with `Ĝ = charFun G`,
  `∫ G(dy) γ_ε(y + z) = ∫ Ĝ(ξ) e^{iξ·z} e^{-ε|ξ|²/2} μ(dξ)`, with the
  integrability of both integrands and of `p_ε(x - ·)` against `Γ`;
  `smoothedGreen_pairing_spectral` is its instance for `G_{h,η}` under the
  Fourier identity, with integrand `e^{-η|ξ|²/2} Ĝ_h(ξ) e^{iξ·z} e^{-ε|ξ|²/2}`;
* `low_alpha_convolution` (general form) and the wrappers below: the whole
  lemma, `E:low-alpha-convolution` with integrability of `y ↦ γ_ε(y + z)`
  against `G_{h,η}`, for all `ε > 0`, `η ≥ 0`, `z` (the uniformity of line
  4715 is the order of quantifiers: the bound does not depend on `ε, η, z`).

Wrappers:
* `low_alpha_convolution_paper`: under `H:homog`
  (`HomogHypothesis.HomogCovariance`, `d ∈ {1,2,3}`, no `Γ ≠ 0`; the
  subsection retains `H:homog`, line 4691), `α < 1` (with `0 < α` from
  `H:homog`, returned as the first conjunct) and the supplied input below,
  for `G_h = waveGreen d h`;
* `low_alpha_convolution_one`: the same in `d = 1` with nothing supplied (the
  Fourier identity is `DampedMultiplier.greenFourier_one`).

Supplied input (one): `GreenFourier (waveGreen d)`
(`DampedMultiplier.GreenFourier`: `G_h` finite and
`charFun (G_h) = waveHat h`, i.e. `Ĝ_h(ξ) = sin(h|ξ|)/|ξ|` with value `h` at
`0`, for `h > 0`).  It is exactly the identity the TeX imports from the source's
wave-kernel formulas (main TeX lines 4738-4744, Chen (2.3)-(2.5), p. 7), with
the finiteness of `G_h` that the TeX states in the same display (`G_h(ℝ^d) = h`);
so it is no stronger than the TeX's input.  It is proved in `d = 1`
(`greenFourier_one`); for `d = 2, 3` it is being proved by wave item L9-G and
is instantiated at integration.

Hypotheses made explicit: the general theorem assumes `Γ` and `μ` tempered
(`HomogHypothesis.IsTempered`; under `H:homog` the fields `Γ_tempered`,
`μ_tempered`), `μ` locally finite (`μ_radon`), `IsSpectralMeasure Γ μ`
(`spectral`) and `SpectralHomogeneous μ α` (discharged under `H:homog` by
`MaskedSpectralGrowth.spectralHomogeneous_of_homog`).  Integrability of every
integral in a conclusion is part of that conclusion (no identity or bound holds
through the junk value `0` of a non-integrable Bochner integral); `V < ∞` is
proved, so `V.toReal` is not junk; `1 - α > 0`, so the division is genuine.

Fields of `H:homog` used by the wrappers (directly or through
`spectralHomogeneous_of_homog`): `μ_radon`, `μ_tempered`, `Γ_tempered`,
`spectral`, `scaling`, `alpha_range` (for `0 < α`).  Carried, unused: `dim`,
`alpha0_pos`, `alpha0_lt_one`, `Γ_radon`, `Γ_even`, `Γ_posdef`, `μ_even`,
`threshold`.

Differences from the TeX (statement and route):
* The TeX's derivation `μ(cA) = c^α μ(A)` from Fourier uniqueness (lines
  4719-4722) is `MaskedSpectralGrowth.spectralHomogeneous_of_homog`; the
  consequence `μ{0} = 0` (lines 4723-4724) is not needed here: `lowKernel h`
  has the value `h` at `0` and its level sets `{t ≤ lowKernel h}` are closed
  balls, which contain `0` (`SpectralHomog.measure_zero` has `μ{0} = 0`).
* Integrability of `e^{-ε|ξ|²/2}` against `μ` (TeX: "by the polynomial ball
  growth of `μ`", line 4736) is taken from the temperedness of `μ`.
* The lower bound: in Lean `Γ` is a (positive) measure, so `γ_ε ≥ 0` because
  `p_ε ≥ 0` (`gammaEps_nonneg`); the TeX argues by distributional
  nonnegativity (lines 4752-4753).  The covariance of `H:homog` is a measure,
  so this is the same situation.
* The upper bound follows the TeX: `|∫ G_{h,η}(dy) γ_ε(y + z)| ≤
  ∫ |e^{-η|ξ|²/2} Ĝ_h(ξ)| e^{-ε|ξ|²/2} μ(dξ) ≤ ∫ min{h, |ξ|^{-1}} dμ`
  (lines 4744-4750), via `smoothed_pairing_spectral`, Mathlib's `charFun_conv`
  (through `DampedMultiplier.charFun_gaussKernel_conv`) and
  `WaveKernel.abs_waveHat_le_min`.
* The general theorem holds in every dimension `d` and for every family `G`
  with `GreenFourier G`; the wrappers restrict to the TeX's setting.

Narrower than the TeX: none for the lemma's displays.  Not stated: the
commentary sentences "This computation uses ball masses, not a radial density"
(lines 4733-4734) and "No positivity of the oscillatory Fourier integrand is
asserted" (lines 4755-4756).

Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.MaskedSpectralGrowth
public import StratonovichHAMSecondMoment.WaveKernel
public import StratonovichHAMSecondMoment.WaveGreen
public import StratonovichHAMSecondMoment.DampedMultiplier

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter Metric ProbabilityTheory
open scoped ENNReal NNReal

namespace StratonovichHAMSecondMoment.LowAlphaConvolution

open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open SpectralHomog (SpectralHomogeneous)
open MaskedSpectralGrowth (spectralHomogeneous_of_homog integrable_gauss_of_tempered
  integrable_gauss_zero spectral_translated_gauss)
open WaveKernel (waveHat waveHat_zero abs_waveHat_le_min)
open WaveGreen (waveGreen)
open DampedMultiplier (gaussKernel GreenFourier greenFourier_one charFun_gaussKernel_conv)

variable {d : ℕ}

/-! ### Definitions -/

/-- The centered Gaussian density on `ℝ^d` with covariance `ε I`,
`p_ε(w) = (2πε)^{-d/2} e^{-|w|²/(2ε)}`. -/
def heatDens (ε : ℝ) (w : Rd d) : ℝ :=
  (2 * π * ε) ^ (-((d : ℝ) / 2)) * Real.exp (-(‖w‖ ^ 2 / (2 * ε)))

/-- The smoothed covariance `γ_ε = p_ε * Γ`, `γ_ε(x) = ∫ p_ε(x - y) Γ(dy)`. -/
def gammaEps (Γ : Measure (Rd d)) (ε : ℝ) (x : Rd d) : ℝ :=
  ∫ y, heatDens ε (x - y) ∂Γ

/-- The smoothed wave kernel `G_{h,η} = p_η * G_h` (with `p_η = gaussKernel η`,
covariance `η I`); for `η = 0` it is `G_h` (`smoothedGreen_zero`). -/
def smoothedGreen (G : ℝ → Measure (Rd d)) (h η : ℝ) : Measure (Rd d) :=
  gaussKernel η ∗ G h

/-- The spectral mass `V = μ({ξ : |ξ| ≤ 1})`. -/
def specV (μ : Measure (Rd d)) : ℝ≥0∞ := μ (closedBall 0 1)

/-- `min{h, |ξ|^{-1}}`, with the value `h` at `ξ = 0` (where `|ξ|^{-1} = ∞`). -/
def lowKernel (h : ℝ) (ξ : Rd d) : ℝ := if ξ = 0 then h else min h ‖ξ‖⁻¹

/-- The Gaussian spectral multiplier `e^{-ε|ξ|²/2}` of `p_ε`. -/
def gaussFactor (ε : ℝ) (ξ : Rd d) : ℝ := Real.exp (-(ε * ‖ξ‖ ^ 2 / 2))

/-! ### Elementary facts -/

/-- Auxiliary to the Lean proof route. -/
theorem heatDens_nonneg {ε : ℝ} (hε : 0 ≤ ε) (w : Rd d) : 0 ≤ heatDens ε w := by
  unfold heatDens
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.exp_pos _).le

/-- `γ_ε ≥ 0` for `ε ≥ 0` (main TeX line 4752): the smoothed covariance of a
(positive) measure `Γ` is nonnegative, since `p_ε ≥ 0`. -/
theorem gammaEps_nonneg (Γ : Measure (Rd d)) {ε : ℝ} (hε : 0 ≤ ε) (x : Rd d) :
    0 ≤ gammaEps Γ ε x :=
  integral_nonneg fun _ => heatDens_nonneg hε _

/-- Auxiliary to the Lean proof route. -/
theorem measurable_lowKernel (h : ℝ) : Measurable (lowKernel (d := d) h) := by
  unfold lowKernel
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

/-- Auxiliary to the Lean proof route. -/
theorem lowKernel_nonneg {h : ℝ} (hh : 0 ≤ h) (ξ : Rd d) : 0 ≤ lowKernel h ξ := by
  unfold lowKernel
  split_ifs
  · exact hh
  · exact le_min hh (inv_nonneg.2 (norm_nonneg _))

/-- `|Ĝ_h(ξ)| ≤ min{h, |ξ|^{-1}}` for `h ≥ 0`, including `ξ = 0` (the second
inequality of the display at main TeX lines 4747-4751). -/
theorem abs_waveHat_le_lowKernel {h : ℝ} (hh : 0 ≤ h) (ξ : Rd d) :
    |waveHat h ξ| ≤ lowKernel h ξ := by
  unfold lowKernel
  split_ifs with hξ
  · rw [hξ, waveHat_zero, abs_of_nonneg hh]
  · have := abs_waveHat_le_min h hh ξ hξ
    rwa [one_div] at this

/-- Auxiliary to the Lean proof route. -/
theorem gaussFactor_pos (ε : ℝ) (ξ : Rd d) : 0 < gaussFactor ε ξ := Real.exp_pos _

/-- Auxiliary to the Lean proof route. -/
theorem gaussFactor_le_one {ε : ℝ} (hε : 0 ≤ ε) (ξ : Rd d) : gaussFactor ε ξ ≤ 1 := by
  unfold gaussFactor
  rw [Real.exp_le_one_iff]
  have : 0 ≤ ε * ‖ξ‖ ^ 2 / 2 := by positivity
  linarith

/-- Auxiliary to the Lean proof route.  `e^{-ε|ξ|²/2}` is integrable against a
tempered measure for `ε > 0`. -/
theorem integrable_gaussFactor {μ : Measure (Rd d)} (hμt : IsTempered μ) {ε : ℝ}
    (hε : 0 < ε) : Integrable (gaussFactor ε) μ := by
  have h := integrable_gauss_zero hμt (c := ε / 2) (by positivity)
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp only [gaussFactor]
  ring_nf

/-! ### The ball masses and the layer cake (`E:low-alpha-radial`) -/

/-- The ball-mass formula of `E:low-alpha-radial` (main TeX line 4705; proof
lines 4719-4723):
`μ({|ξ| ≤ R}) = V R^α` for `R > 0`, from `μ(cA) = c^α μ(A)`. -/
theorem measure_closedBall_eq {μ : Measure (Rd d)} {alpha : ℝ}
    (hI : SpectralHomogeneous μ alpha) (R : ℝ) (hR : 0 < R) :
    μ (closedBall 0 R) = ENNReal.ofReal (R ^ alpha) * specV μ := by
  have h := smul_closedBall (E := Rd d) R (0 : Rd d) zero_le_one
  rw [smul_zero, Real.norm_eq_abs, abs_of_pos hR, mul_one] at h
  rw [← h, hI _ measurableSet_closedBall R hR, specV]

/-- Auxiliary to the Lean proof route.  The level sets of `lowKernel h`:
`{t ≤ min(h, |ξ|^{-1})} = {|ξ| ≤ t^{-1}}` for `0 < t ≤ h`. -/
theorem levelset_lowKernel {h t : ℝ} (ht : 0 < t) (hth : t ≤ h) :
    {ξ : Rd d | t ≤ lowKernel h ξ} = closedBall 0 t⁻¹ := by
  ext ξ
  simp only [mem_ofPred_eq, mem_closedBall_zero_iff, lowKernel]
  split_ifs with hξ
  · simp only [hξ, norm_zero, hth, true_iff]
    exact (inv_pos.2 ht).le
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    rw [le_min_iff, le_inv_comm₀ ht hn]
    exact ⟨fun h' => h'.2, fun h' => ⟨hth, h'⟩⟩

/-- Auxiliary to the Lean proof route.  The level sets above `h` are empty. -/
theorem levelset_lowKernel_empty {h t : ℝ} (hth : h < t) :
    {ξ : Rd d | t ≤ lowKernel h ξ} = ∅ := by
  ext ξ
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le, lowKernel]
  split_ifs
  · exact hth
  · exact lt_of_le_of_lt (min_le_left _ _) hth

/-- Auxiliary to the Lean proof route (the last integral of main TeX line 4729).
`∫_0^h u^{-α} du = h^{1-α}/(1-α)` for
`α < 1`, `h ≥ 0`, as a lower integral over `(0, h]`. -/
theorem lintegral_rpow_Ioc {alpha h : ℝ} (ha1 : alpha < 1) (hh : 0 ≤ h) :
    ∫⁻ t in Ioc 0 h, ENNReal.ofReal (t ^ (-alpha)) =
      ENNReal.ofReal (h ^ (1 - alpha) / (1 - alpha)) := by
  have hi : IntegrableOn (fun t : ℝ => t ^ (-alpha)) (Ioc 0 h) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := h) (by linarith)).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht =>
      Real.rpow_nonneg ht.1.le _)),
    ← intervalIntegral.integral_of_le hh, integral_rpow (Or.inl (by linarith)),
    Real.zero_rpow (by linarith)]
  congr 1
  rw [show -alpha + 1 = 1 - alpha by ring, sub_zero]

/-- The layer-cake identity of `E:low-alpha-radial` (main TeX lines 4706-4707;
proof lines 4723-4733; with `V < ∞` and the
integrability of `min{h, |ξ|^{-1}}`): for `h > 0` and `α < 1`,
`∫ min{h, |ξ|^{-1}} μ(dξ) = V h^{1-α}/(1-α)`. -/
theorem integral_lowKernel {μ : Measure (Rd d)} {alpha : ℝ} [IsLocallyFiniteMeasure μ]
    (hI : SpectralHomogeneous μ alpha) (ha1 : alpha < 1) {h : ℝ} (hh : 0 < h) :
    specV μ < ⊤ ∧ Integrable (lowKernel h) μ ∧
      ∫ ξ, lowKernel h ξ ∂μ = (specV μ).toReal / (1 - alpha) * h ^ (1 - alpha) := by
  have hV : specV μ < ⊤ := measure_closedBall_lt_top
  have hf0 : ∀ ξ : Rd d, 0 ≤ lowKernel h ξ := lowKernel_nonneg hh.le
  have hfm := measurable_lowKernel (d := d) h
  have hlc : ∫⁻ ξ, ENNReal.ofReal (lowKernel h ξ) ∂μ =
      specV μ * ENNReal.ofReal (h ^ (1 - alpha) / (1 - alpha)) := by
    rw [lintegral_eq_lintegral_meas_le μ (Eventually.of_forall hf0) hfm.aemeasurable]
    have hlev : ∀ t ∈ Ioi (0 : ℝ), μ {ξ | t ≤ lowKernel h ξ} =
        (Ioc 0 h).indicator (fun t => specV μ * ENNReal.ofReal (t ^ (-alpha))) t := by
      intro t ht
      have ht0 : 0 < t := ht
      by_cases hth : t ≤ h
      · rw [indicator_of_mem (show t ∈ Ioc 0 h from ⟨ht0, hth⟩), levelset_lowKernel ht0 hth,
          measure_closedBall_eq hI _ (inv_pos.2 ht0), Real.inv_rpow ht0.le,
          ← Real.rpow_neg ht0.le, mul_comm]
      · rw [indicator_of_notMem (fun hm => hth hm.2),
          levelset_lowKernel_empty (not_le.1 hth), measure_empty]
    rw [setLIntegral_congr_fun measurableSet_Ioi hlev, lintegral_indicator measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioc,
      show Ioc (0 : ℝ) h ∩ Ioi 0 = Ioc 0 h from inter_eq_left.2 fun t ht => ht.1,
      lintegral_const_mul _ (by fun_prop), lintegral_rpow_Ioc ha1 hh.le]
  have hfin : ∫⁻ ξ, ENNReal.ofReal (lowKernel h ξ) ∂μ < ⊤ := by
    rw [hlc]; exact ENNReal.mul_lt_top hV ENNReal.ofReal_lt_top
  refine ⟨hV, ⟨hfm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hf0)).2 hfin⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfm.aestronglyMeasurable,
    hlc, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
      have : 0 < 1 - alpha := by linarith
      positivity)]
  ring

/-! ### The Gaussian spectral representation -/

/-- Auxiliary to the Lean proof route.  `y ↦ p_ε(x - y)` is integrable against a
tempered `Γ` (`ε > 0`). -/
theorem integrable_heatDens {Γ : Measure (Rd d)} (hΓt : IsTempered Γ) {ε : ℝ} (hε : 0 < ε)
    (x : Rd d) : Integrable (fun y => heatDens ε (x - y)) Γ := by
  have h := (integrable_gauss_of_tempered hΓt (b := 1 / (2 * ε)) (by positivity) x).const_mul
    ((2 * π * ε) ^ (-((d : ℝ) / 2)))
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [heatDens]
  rw [norm_sub_rev]
  congr 2
  field_simp

/-- The pointwise Gaussian spectral representation of the smoothed covariance
(part of the Fourier Fubini step invoked at main TeX lines 4736-4738):
for `ε > 0`, `γ_ε(x) = ∫ e^{iξ·x} e^{-ε|ξ|²/2} μ(dξ)`, where `μ` is the
spectral measure of `Γ` (`IsSpectralMeasure Γ μ`). -/
theorem gammaEps_spectral {Γ μ : Measure (Rd d)} (hsp : IsSpectralMeasure Γ μ) {ε : ℝ}
    (hε : 0 < ε) (x : Rd d) :
    (gammaEps Γ ε x : ℂ) =
      ∫ ξ, Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) * (gaussFactor ε ξ : ℂ) ∂μ := by
  have hs : 0 < 1 / (2 * ε) := by positivity
  have h := spectral_translated_gauss hsp (1 / (2 * ε)) hs x
  have hL : (gammaEps Γ ε x : ℂ) = (((2 * π * ε) ^ (-((d : ℝ) / 2)) : ℝ) : ℂ) *
      ∫ y, (Real.exp (-(1 / (2 * ε) * ‖y - x‖ ^ 2)) : ℂ) ∂Γ := by
    have h1 : (∫ y, (Real.exp (-(1 / (2 * ε) * ‖y - x‖ ^ 2)) : ℂ) ∂Γ) =
        ((∫ y, Real.exp (-(1 / (2 * ε) * ‖y - x‖ ^ 2)) ∂Γ : ℝ) : ℂ) := integral_ofReal
    have h2 : gammaEps Γ ε x = (2 * π * ε) ^ (-((d : ℝ) / 2)) *
        ∫ y, Real.exp (-(1 / (2 * ε) * ‖y - x‖ ^ 2)) ∂Γ := by
      rw [gammaEps, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [heatDens]
      rw [norm_sub_rev]
      congr 2
      field_simp
    rw [h1, h2, Complex.ofReal_mul]
  have hpi : π / (1 / (2 * ε)) = 2 * π * ε := by field_simp
  rw [hL, h, hpi, ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add (by positivity),
    neg_add_cancel, Real.rpow_zero, Complex.ofReal_one, one_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [gaussFactor]
  congr 3
  field_simp
  ring

/-- Auxiliary to the Lean proof route.  `γ_ε` is continuous and bounded by
`∫ e^{-ε|ξ|²/2} dμ`. -/
theorem gammaEps_continuous_bounded {Γ μ : Measure (Rd d)} (hμt : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (gammaEps Γ ε) ∧ ∀ x, ‖gammaEps Γ ε x‖ ≤ ∫ ξ, gaussFactor ε ξ ∂μ := by
  have hm := integrable_gaussFactor hμt hε
  set F : Rd d → Rd d → ℂ := fun x ξ =>
    Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) * (gaussFactor ε ξ : ℂ) with hF
  have hnorm : ∀ x ξ, ‖F x ξ‖ = gaussFactor ε ξ := by
    intro x ξ
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (gaussFactor_pos ε ξ)]
    rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hrep : ∀ x, gammaEps Γ ε x = (∫ ξ, F x ξ ∂μ).re := by
    intro x
    rw [hF, ← gammaEps_spectral hsp hε x, Complex.ofReal_re]
  have hcont : Continuous fun x => ∫ ξ, F x ξ ∂μ := by
    refine continuous_of_dominated (bound := gaussFactor ε) (fun x => ?_)
      (fun x => Eventually.of_forall fun ξ => (hnorm x ξ).le) hm
      (Eventually.of_forall fun ξ => ?_)
    · exact (by simp only [hF, gaussFactor]; fun_prop : Continuous (F x)).aestronglyMeasurable
    · simp only [hF]; fun_prop
  refine ⟨?_, fun x => ?_⟩
  · have : gammaEps Γ ε = fun x => (∫ ξ, F x ξ ∂μ).re := funext hrep
    rw [this]
    exact Complex.continuous_re.comp hcont
  · rw [Real.norm_eq_abs, hrep x]
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    exact integral_congr_ae (Eventually.of_forall fun ξ => hnorm x ξ)

/-- **Gaussian spectral representation of the smoothed pairing** (the
"Fourier Fubini" step of the proof of `L:low-alpha-convolution`, main TeX
lines 4736-4738, which the TeX does not display; stated for a general finite
measure `G`).  Let `Γ` and `μ` be tempered with `IsSpectralMeasure Γ μ` (`μ`
s-finite), `ε > 0`, `G` a finite measure on `ℝ^d` and `z ∈ ℝ^d`.  Then
`y ↦ p_ε(x - y)` is `Γ`-integrable for every `x` (so `γ_ε` is a genuine
integral), `y ↦ γ_ε(y + z)` is `G`-integrable,
`ξ ↦ Ĝ(ξ) e^{iξ·z} e^{-ε|ξ|²/2}` is `μ`-integrable (with `Ĝ = charFun G`,
`Ĝ(ξ) = ∫ e^{i y·ξ} G(dy)`), and
`∫ G(dy) γ_ε(y + z) = ∫ Ĝ(ξ) e^{iξ·z} e^{-ε|ξ|²/2} μ(dξ)`. -/
theorem smoothed_pairing_spectral {Γ μ : Measure (Rd d)} [SFinite μ] (hΓt : IsTempered Γ)
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) {ε : ℝ} (hε : 0 < ε)
    (G : Measure (Rd d)) [IsFiniteMeasure G] (z : Rd d) :
    (∀ x : Rd d, Integrable (fun y => heatDens ε (x - y)) Γ) ∧
      Integrable (fun y => gammaEps Γ ε (y + z)) G ∧
      Integrable (fun ξ => charFun G ξ * Complex.exp (Complex.I * (inner ℝ ξ z : ℝ)) *
        (gaussFactor ε ξ : ℂ)) μ ∧
      ((∫ y, gammaEps Γ ε (y + z) ∂G : ℝ) : ℂ) =
        ∫ ξ, charFun G ξ * Complex.exp (Complex.I * (inner ℝ ξ z : ℝ)) *
          (gaussFactor ε ξ : ℂ) ∂μ := by
  obtain ⟨hc, hb⟩ := gammaEps_continuous_bounded hμt hsp hε
  have hm := integrable_gaussFactor hμt hε
  have hint : Integrable (fun y => gammaEps Γ ε (y + z)) G :=
    Integrable.of_bound (hc.comp (continuous_id.add continuous_const)).aestronglyMeasurable _
      (Eventually.of_forall fun y => hb (y + z))
  -- the integrand on `G × μ`
  set F : Rd d → Rd d → ℂ := fun y ξ =>
    Complex.exp (Complex.I * (inner ℝ ξ (y + z) : ℝ)) * (gaussFactor ε ξ : ℂ) with hF
  have hnorm : ∀ y ξ, ‖F y ξ‖ = gaussFactor ε ξ := by
    intro y ξ
    simp only [hF, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (gaussFactor_pos ε ξ)]
    rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hFc : Continuous (Function.uncurry F) := by
    simp only [hF, gaussFactor, Function.uncurry_def]
    fun_prop
  have hprod : Integrable (Function.uncurry F) (G.prod μ) := by
    refine Integrable.mono' (hm.comp_snd G) hFc.aestronglyMeasurable
      (Eventually.of_forall fun p => (hnorm p.1 p.2).le)
  have hinner : ∀ ξ, ∫ y, F y ξ ∂G =
      charFun G ξ * Complex.exp (Complex.I * (inner ℝ ξ z : ℝ)) * (gaussFactor ε ξ : ℂ) := by
    intro ξ
    have hpt : ∀ y, F y ξ = Complex.exp ((inner ℝ y ξ : ℝ) * Complex.I) *
        (Complex.exp (Complex.I * (inner ℝ ξ z : ℝ)) * (gaussFactor ε ξ : ℂ)) := by
      intro y
      simp only [hF]
      rw [inner_add_right, Complex.ofReal_add, mul_add, Complex.exp_add, real_inner_comm ξ y]
      ring_nf
    simp_rw [hpt]
    rw [integral_mul_const, ← charFun_apply, mul_assoc]
  have hswap := integral_integral_swap hprod
  have hL : ((∫ y, gammaEps Γ ε (y + z) ∂G : ℝ) : ℂ) = ∫ y, ∫ ξ, F y ξ ∂μ ∂G := by
    have h1 : (∫ y, (gammaEps Γ ε (y + z) : ℂ) ∂G) =
        ((∫ y, gammaEps Γ ε (y + z) ∂G : ℝ) : ℂ) := integral_ofReal
    rw [← h1]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    exact gammaEps_spectral hsp hε (y + z)
  refine ⟨integrable_heatDens hΓt hε, hint, ?_, ?_⟩
  · have := hprod.integral_prod_right
    simp only [Function.uncurry_def] at this
    exact this.congr (Eventually.of_forall fun ξ => hinner ξ)
  · rw [hL, hswap]
    exact integral_congr_ae (Eventually.of_forall fun ξ => hinner ξ)

/-! ### `L:low-alpha-convolution` -/

/-- `G_{h,0} = G_h` (the convention of main TeX line 4698): `gaussKernel 0` is
the Dirac mass at `0`. -/
theorem smoothedGreen_zero (G : ℝ → Measure (Rd d)) (h : ℝ) [SFinite (G h)] :
    smoothedGreen G h 0 = G h := by
  have hk : gaussKernel (d := d) 0 = Measure.dirac 0 := by
    unfold gaussKernel
    simp only [Real.sqrt_zero, zero_smul]
    rw [Measure.map_const, measure_univ, one_smul]
  rw [smoothedGreen, hk, Measure.dirac_zero_conv]

/-- Auxiliary to the Lean proof route.  Under `GreenFourier G`, for `h > 0` and
`η ≥ 0`, `G_{h,η}` is finite with transform `e^{-η|ξ|²/2} Ĝ_h(ξ)`, of absolute
value at most `min{h, |ξ|^{-1}}`. -/
theorem smoothedGreen_fourier {G : ℝ → Measure (Rd d)} (hGF : GreenFourier G) {h η : ℝ}
    (hh : 0 < h) (hη : 0 ≤ η) :
    IsFiniteMeasure (smoothedGreen G h η) ∧ ∀ ξ,
      charFun (smoothedGreen G h η) ξ =
        Complex.exp (-(η * ‖ξ‖ ^ 2) / 2) * (waveHat h ξ : ℂ) ∧
      ‖charFun (smoothedGreen G h η) ξ‖ ≤ lowKernel h ξ := by
  have := hGF.finite h hh
  refine ⟨by unfold smoothedGreen; infer_instance, fun ξ => ?_⟩
  have he : charFun (smoothedGreen G h η) ξ =
      Complex.exp (-(η * ‖ξ‖ ^ 2) / 2) * (waveHat h ξ : ℂ) := by
    rw [smoothedGreen, charFun_gaussKernel_conv η hη, hGF.fourier h hh]
  refine ⟨he, ?_⟩
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖Complex.exp (-(η * ‖ξ‖ ^ 2) / 2)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    rw [Real.exp_le_one_iff]
    have : (-(↑η * ↑‖ξ‖ ^ 2) / 2 : ℂ).re = -(η * ‖ξ‖ ^ 2) / 2 := by
      norm_cast
    rw [this]
    have : 0 ≤ η * ‖ξ‖ ^ 2 := by positivity
    linarith
  calc ‖Complex.exp (-(η * ‖ξ‖ ^ 2) / 2)‖ * |waveHat h ξ| ≤ 1 * |waveHat h ξ| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |waveHat h ξ| := one_mul _
    _ ≤ lowKernel h ξ := abs_waveHat_le_lowKernel hh.le ξ

/-- The spectral representation `smoothed_pairing_spectral` for the smoothed
Green measure `G_{h,η} = p_η * G_h` under `GreenFourier G` (`h > 0`, `η ≥ 0`,
`ε > 0`): `y ↦ γ_ε(y + z)` is `G_{h,η}`-integrable, the spectral integrand is
`μ`-integrable, and
`∫ G_{h,η}(dy) γ_ε(y + z) = ∫ e^{-η|ξ|²/2} Ĝ_h(ξ) e^{iξ·z} e^{-ε|ξ|²/2} μ(dξ)`
with `Ĝ_h(ξ) = sin(h|ξ|)/|ξ|` (`waveHat h ξ`). -/
theorem smoothedGreen_pairing_spectral {Γ μ : Measure (Rd d)} [SFinite μ]
    (hΓt : IsTempered Γ) (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ)
    {G : ℝ → Measure (Rd d)} (hGF : GreenFourier G) {h η ε : ℝ} (hh : 0 < h) (hη : 0 ≤ η)
    (hε : 0 < ε) (z : Rd d) :
    Integrable (fun y => gammaEps Γ ε (y + z)) (smoothedGreen G h η) ∧
      Integrable (fun ξ => (gaussFactor η ξ : ℂ) * (waveHat h ξ : ℂ) *
        Complex.exp (Complex.I * (inner ℝ ξ z : ℝ)) * (gaussFactor ε ξ : ℂ)) μ ∧
      ((∫ y, gammaEps Γ ε (y + z) ∂(smoothedGreen G h η) : ℝ) : ℂ) =
        ∫ ξ, (gaussFactor η ξ : ℂ) * (waveHat h ξ : ℂ) *
          Complex.exp (Complex.I * (inner ℝ ξ z : ℝ)) * (gaussFactor ε ξ : ℂ) ∂μ := by
  obtain ⟨hfin, hGh⟩ := smoothedGreen_fourier hGF hh hη
  have hc : ∀ ξ, charFun (smoothedGreen G h η) ξ = (gaussFactor η ξ : ℂ) * (waveHat h ξ : ℂ) := by
    intro ξ
    rw [(hGh ξ).1, gaussFactor, Complex.ofReal_exp]
    push_cast
    ring_nf
  obtain ⟨-, hint, hint2, hrep⟩ :=
    smoothed_pairing_spectral hΓt hμt hsp hε (smoothedGreen G h η) z
  simp_rw [hc] at hint2 hrep
  exact ⟨hint, hint2, hrep⟩

/-- **`L:low-alpha-convolution`, general form** (main TeX lines 4702-4757).
Let `μ` be a locally finite measure with `μ(cA) = c^α μ(A)`
(`SpectralHomogeneous μ α`), `α < 1` (no lower bound on `α` is used), `Γ`,
`μ` tempered with
`IsSpectralMeasure Γ μ`, and `G` a family of measures with the Fourier identity
`GreenFourier G` (`G_h` finite with `Ĝ_h(ξ) = sin(h|ξ|)/|ξ|`, value `h` at `0`).
Then for `R, h > 0`: `μ({|ξ| ≤ R}) = V R^α` with `V < ∞`, `min{h, |ξ|^{-1}}` is
`μ`-integrable with integral `V h^{1-α}/(1-α)` (`E:low-alpha-radial`);
`y ↦ p_ε(x - y)` is `Γ`-integrable for `ε > 0` and every `x`; and for `ε > 0`, `η ≥ 0`,
`z ∈ ℝ^d`, `y ↦ γ_ε(y + z)` is `G_{h,η}`-integrable and
`0 ≤ ∫ G_{h,η}(dy) γ_ε(y + z) ≤ V h^{1-α}/(1-α)` (`E:low-alpha-convolution`). -/
theorem low_alpha_convolution {Γ μ : Measure (Rd d)} {alpha : ℝ} [IsLocallyFiniteMeasure μ]
    (hI : SpectralHomogeneous μ alpha) (ha1 : alpha < 1) (hΓt : IsTempered Γ)
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) {G : ℝ → Measure (Rd d)}
    (hGF : GreenFourier G) :
    specV μ < ⊤ ∧
      (∀ R : ℝ, 0 < R → μ (closedBall 0 R) = ENNReal.ofReal (R ^ alpha) * specV μ) ∧
      (∀ h : ℝ, 0 < h → Integrable (lowKernel h) μ ∧
        ∫ ξ, lowKernel h ξ ∂μ = (specV μ).toReal / (1 - alpha) * h ^ (1 - alpha)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ x, Integrable (fun y => heatDens ε (x - y)) Γ) ∧
      ∀ h : ℝ, 0 < h → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 ≤ η → ∀ z : Rd d,
        Integrable (fun y => gammaEps Γ ε (y + z)) (smoothedGreen G h η) ∧
        0 ≤ ∫ y, gammaEps Γ ε (y + z) ∂(smoothedGreen G h η) ∧
        ∫ y, gammaEps Γ ε (y + z) ∂(smoothedGreen G h η) ≤
          (specV μ).toReal / (1 - alpha) * h ^ (1 - alpha) := by
  refine ⟨measure_closedBall_lt_top, measure_closedBall_eq hI,
    fun h hh => (integral_lowKernel hI ha1 hh).2, fun ε hε => integrable_heatDens hΓt hε,
    fun h hh ε hε η hη z => ?_⟩
  obtain ⟨-, hKi, hK⟩ := integral_lowKernel hI ha1 hh
  obtain ⟨hfin, hGh⟩ := smoothedGreen_fourier hGF hh hη
  obtain ⟨-, hint, hint2, hrep⟩ :=
    smoothed_pairing_spectral hΓt hμt hsp hε (smoothedGreen G h η) z
  refine ⟨hint, integral_nonneg fun y => gammaEps_nonneg Γ hε.le _, ?_⟩
  rw [← hK]
  refine (le_abs_self _).trans ?_
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hrep]
  refine (norm_integral_le_integral_norm _).trans (integral_mono hint2.norm hKi fun ξ => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussFactor_pos ε ξ)]
  rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one]
  calc ‖charFun (smoothedGreen G h η) ξ‖ * gaussFactor ε ξ
      ≤ lowKernel h ξ * 1 :=
        mul_le_mul (hGh ξ).2 (gaussFactor_le_one hε.le ξ) (gaussFactor_pos ε ξ).le
          (lowKernel_nonneg hh.le ξ)
    _ = lowKernel h ξ := mul_one _

/-- Auxiliary to the Lean proof route.  Under `H:homog` with `α < 1`, `0 < α`. -/
theorem alpha_pos_of_homog {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (ha1 : alpha < 1) : 0 < alpha := by
  rcases hH.alpha_range with h | ⟨h, hd⟩
  · exact h.1
  · subst hd; norm_num at h; linarith

/-- **`L:low-alpha-convolution`** (main TeX lines 4702-4757) under the
manuscript's hypotheses: `H:homog` (`HomogCovariance`, `d ∈ {1,2,3}`; no
`Γ ≠ 0`), `α < 1` (so `0 < α < 1`), `G_h` the wave Green measures
`waveGreen d h`, and the Fourier identity of the source's wave-kernel formulas
(main TeX line 4741), supplied as `GreenFourier (waveGreen d)`.  Conclusions as
in `low_alpha_convolution`, with `G_{h,η} = p_η * G_h` (`smoothedGreen`,
`= G_h` for `η = 0` by `smoothedGreen_zero`). -/
theorem low_alpha_convolution_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (ha1 : alpha < 1)
    (hGF : GreenFourier (waveGreen d)) :
    0 < alpha ∧ specV μ < ⊤ ∧
      (∀ R : ℝ, 0 < R → μ (closedBall 0 R) = ENNReal.ofReal (R ^ alpha) * specV μ) ∧
      (∀ h : ℝ, 0 < h → Integrable (lowKernel h) μ ∧
        ∫ ξ, lowKernel h ξ ∂μ = (specV μ).toReal / (1 - alpha) * h ^ (1 - alpha)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ x, Integrable (fun y => heatDens ε (x - y)) Γ) ∧
      ∀ h : ℝ, 0 < h → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 ≤ η → ∀ z : Rd d,
        Integrable (fun y => gammaEps Γ ε (y + z)) (smoothedGreen (waveGreen d) h η) ∧
        0 ≤ ∫ y, gammaEps Γ ε (y + z) ∂(smoothedGreen (waveGreen d) h η) ∧
        ∫ y, gammaEps Γ ε (y + z) ∂(smoothedGreen (waveGreen d) h η) ≤
          (specV μ).toReal / (1 - alpha) * h ^ (1 - alpha) := by
  have := hH.μ_radon
  exact ⟨alpha_pos_of_homog hH ha1,
    low_alpha_convolution (spectralHomogeneous_of_homog hH) ha1 hH.Γ_tempered hH.μ_tempered
      hH.spectral hGF⟩

/-- **`L:low-alpha-convolution` in `d = 1`, unconditional**: the wrapper
`low_alpha_convolution_paper` with the Fourier identity discharged by
`DampedMultiplier.greenFourier_one`. -/
theorem low_alpha_convolution_one {alpha alpha0 : ℝ} {Γ μ : Measure (Rd 1)}
    (hH : HomogCovariance 1 alpha alpha0 Γ μ) (ha1 : alpha < 1) :
    0 < alpha ∧ specV μ < ⊤ ∧
      (∀ R : ℝ, 0 < R → μ (closedBall 0 R) = ENNReal.ofReal (R ^ alpha) * specV μ) ∧
      (∀ h : ℝ, 0 < h → Integrable (lowKernel h) μ ∧
        ∫ ξ, lowKernel h ξ ∂μ = (specV μ).toReal / (1 - alpha) * h ^ (1 - alpha)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ x, Integrable (fun y => heatDens ε (x - y)) Γ) ∧
      ∀ h : ℝ, 0 < h → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 ≤ η → ∀ z : Rd 1,
        Integrable (fun y => gammaEps Γ ε (y + z)) (smoothedGreen (waveGreen 1) h η) ∧
        0 ≤ ∫ y, gammaEps Γ ε (y + z) ∂(smoothedGreen (waveGreen 1) h η) ∧
        ∫ y, gammaEps Γ ε (y + z) ∂(smoothedGreen (waveGreen 1) h η) ≤
          (specV μ).toReal / (1 - alpha) * h ^ (1 - alpha) :=
  low_alpha_convolution_paper hH ha1 greenFourier_one

end StratonovichHAMSecondMoment.LowAlphaConvolution
