module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`L:alpha-one-convolution` (Degree-one convolution bound) of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision edf7085f: statement lines
5635-5643, proof lines 5645-5708, with the section's standing assumptions (lines
5552-5563: `H:homog`, `d ∈ {1,2,3}`, `μ` the spectral measure in the convention
`γ(x) = ∫ e^{iξ·x} μ(dξ)`, `V = μ{|ξ| ≤ 1}`, `G_h` the wave Green measure,
`G_{h,η} = p_η * G_h`, `G_{h,0} = G_h`).

Formalized (proved here):
* (i) `polar_decomposition` (lines 5653-5665): for a locally finite `μ` with
  `μ(cA) = cμ(A)` (`SpectralHomog.SpectralHomogeneous μ 1`): `μ{0} = 0`, `V < ∞`, the
  angular measure `σ(E) = μ{0 < |ξ| ≤ 1, ξ/|ξ| ∈ E}` (`sphereMeasure`,
  `sphereMeasure_apply`) has mass `V` and is concentrated on the unit sphere, and
  `μ` is the image of `σ ⊗ (dr on (0,∞))` under `(θ,r) ↦ rθ`.  `σ` is a measure on
  `ℝ^d` concentrated on the sphere, not a measure on the sphere subtype (a
  representation choice).  `sphereMeasure_even`: `σ` is even when `μ` is.
  `polar_integral`: the integral form (auxiliary).
* (ii) `alpha_one_radial` (lines 5682-5683, 5691-5703): for `a > 0`, `h ≥ 0`:
  absolute convergence of `I_a(h,v) = ∫_0^∞ e^{-ar²} (sin(hr)/r) cos(rv) dr` (`Ia`),
  `I_a(h,v) = π (g_h * p_{2a}^{(1)})(v)` (`gBox`, `gauss1`, `boxConv`), and
  `0 ≤ I_a(h,v) ≤ π/2`.
* (iii) `alpha_one_polar`: the spectral side of `E:alpha-one-polar`,
  `∫ Ĝ_h(ξ) e^{-a|ξ|²} cos(ξ·z) μ(dξ) = ∫ I_a(h,θ·z) σ(dθ)`, with both integrability
  statements, and `0 ≤ … ≤ πV/2`.
* (iv) `alpha_one_convolution` (general form) and `alpha_one_convolution_paper`
  (the manuscript's hypotheses: `HomogCovariance d 1 α₀ Γ μ`; no `Γ ≠ 0`): integrability
  of `y ↦ γ_ε(y+z)` against `G_{h,η}`, `E:alpha-one-polar` with `a = (ε+η)/2`, and
  `E:alpha-one-convolution`, `0 ≤ ∫ G_{h,η}(dy) γ_ε(y+z) ≤ πV/2`, for `h > 0`,
  `ε > 0`, `η ≥ 0`, `z ∈ ℝ^d`.  `alpha_one_convolution_one`: the same in `d = 1` with
  the Fourier identity of `G_h` discharged.  `alpha_one_polar_decomposition_paper`: (i)
  plus evenness of `σ` under `H:homog`.

Objects: `γ_ε = Γ * p_ε` is `VariationalDilation.conv Γ (VariationalMean.heatK ε)`
(existing; `p_ε` has covariance `εI`, multiplier `e^{-ε|ξ|²/2}`, the TeX's Brownian
convention, line 5671; definitionally `LowAlphaConvolution.gammaEps Γ ε`,
`conv_heatK_eq_gammaEps`); `G_h = WaveGreen.waveGreen d h`; `Ĝ_h = WaveKernel.waveHat h`;
`G_{h,η} = p_η * G_h` is wave L9-L's `LowAlphaConvolution.smoothedGreen`
(`= DampedMultiplier.gaussKernel η ∗ G h`, `p_η = N(0, ηI)`).  This module defines no
Gaussian law or smoothed Green measure of its own (wave L10-A1i removed the local
duplicates `gaussLaw` and `smoothedGreen`).

Supplied inputs (named hypotheses of the convolution statements only; (i)-(iii) have
none):
* `SpectralPairing Γ μ`: the Fourier-Fubini representation
  `∫ G_{h,η}(dy) γ_ε(y+z) = ∫ Ĝ_{h,η}(ξ) e^{iξ·z} e^{-ε|ξ|²/2} μ(dξ)` with the
  integrability of the left integrand (lines 5610-5612, used at line 5673); it is
  `LowAlphaConvolution.smoothed_pairing_spectral` (wave L9-L) at `G = G_{h,η}`.
* `WaveGreenFourier d`: `∫ e^{iξ·y} G_s(dy) = sin(s|ξ|)/|ξ|` for `s > 0` (lines
  5614-5618); proved for `d = 1` (`waveGreenFourier_one`), wave L9-G for `d = 2, 3`.
Both are discharged under `H:homog` in `L10Completed` (`alpha_one_convolution_paper_completed`);
they stay hypotheses here so that this module does not depend on `WaveGreenFourier`.

Proof-route differences: (ii) uses `sin(hr)/r = ½∫_{-h}^{h} cos(ru) du`, Fubini and
the Gaussian cosine integral (from Mathlib's `fourierIntegral_gaussian`) instead of the
TeX's Fourier inversion of `ĝ_h p̂_{2a}`; in (iv) the passage from `e^{iξ·z}` to
`cos(ξ·z)` takes the real part of an identity with real left side instead of using the
evenness of `σ` (lines 5683-5685); the Gaussian factor of `G_{h,η}` is obtained from
Mathlib's `charFun_conv` and `charFun_stdGaussian`.  Lemmas marked "Auxiliary to the
Lean proof route" have no manuscript label.  Nothing narrower than the TeX statement.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.MaskedSpectralGrowth
public import StratonovichHAMSecondMoment.WaveKernel
public import StratonovichHAMSecondMoment.WaveGreen
public import StratonovichHAMSecondMoment.VariationalDilation
public import StratonovichHAMSecondMoment.VariationalMean
public import StratonovichHAMSecondMoment.DampedMultiplier
public import StratonovichHAMSecondMoment.LowAlphaConvolution

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter Metric ProbabilityTheory
open scoped ENNReal NNReal Pointwise

namespace StratonovichHAMSecondMoment.AlphaOneConvolution

open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open SpectralHomog (SpectralHomogeneous)

/-! ### (ii) The one-dimensional radial integral `I_a(h,v)` -/

/-- `I_a(h,v) = ∫_0^∞ e^{-ar²} (sin(hr)/r) cos(rv) dr` (`E:alpha-one-polar`, second line). -/
def Ia (a h v : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), Real.exp (-(a * r ^ 2)) * (Real.sin (h * r) / r) * Real.cos (r * v)

/-- `g_h(u) = ½ 1_{|u|<h}`. -/
def gBox (h u : ℝ) : ℝ := (Ioo (-h) h).indicator (fun _ => (1 / 2 : ℝ)) u

/-- The one-dimensional Gaussian density `p_{2a}^{(1)}(w) = (4πa)^{-1/2} e^{-w²/(4a)}`. -/
def gauss1 (a w : ℝ) : ℝ := (4 * π * a) ^ (-(1 / 2 : ℝ)) * Real.exp (-(w ^ 2 / (4 * a)))

/-- `(g_h * p_{2a}^{(1)})(v) = ∫ g_h(u) p_{2a}^{(1)}(v - u) du`. -/
def boxConv (a h v : ℝ) : ℝ := ∫ u, gBox h u * gauss1 a (v - u)

/-- Auxiliary to the Lean proof route. -/
theorem gauss1_nonneg (a w : ℝ) (ha : 0 < a) : 0 ≤ gauss1 a w := by
  unfold gauss1; positivity

/-- Auxiliary to the Lean proof route.  `p_{2a}^{(1)}` is even. -/
theorem gauss1_neg (a w : ℝ) : gauss1 a (-w) = gauss1 a w := by
  unfold gauss1; rw [neg_sq]

/-- Auxiliary to the Lean proof route.  `p_{2a}^{(1)}` is integrable with mass one. -/
theorem gauss1_integrable_and_mass (a : ℝ) (ha : 0 < a) :
    Integrable (gauss1 a) ∧ ∫ w, gauss1 a w = 1 := by
  have hb : 0 < 1 / (4 * a) := by positivity
  have hrw : gauss1 a = fun w : ℝ =>
      (4 * π * a) ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / (4 * a)) * w ^ 2) := by
    funext w; unfold gauss1; congr 2; ring
  refine ⟨?_, ?_⟩
  · rw [hrw]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  · rw [hrw, integral_const_mul, integral_gaussian]
    have h4 : π / (1 / (4 * a)) = 4 * π * a := by field_simp
    rw [h4, Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity)]
    norm_num

/-- Auxiliary to the Lean proof route.  The Gaussian cosine integral on the line:
`∫ e^{-ax²} cos(xw) dx = √(π/a) e^{-w²/(4a)}` (`a > 0`), from Mathlib's
`fourierIntegral_gaussian`. -/
theorem integral_gauss_cos_line (a w : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, Real.exp (-(a * x ^ 2)) * Real.cos (x * w) =
      Real.sqrt (π / a) * Real.exp (-(w ^ 2 / (4 * a))) := by
  have hb : 0 < ((a : ℂ)).re := by simpa using ha
  have hF := fourierIntegral_gaussian hb (w : ℂ)
  have hint : Integrable (fun x : ℝ =>
      Complex.exp (Complex.I * (w : ℂ) * x) * Complex.exp (-(a : ℂ) * x ^ 2)) := by
    refine Integrable.mono' (integrable_exp_neg_mul_sq ha) (by fun_prop)
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
    apply le_of_eq
    have h1 : (Complex.I * (w : ℂ) * x).re = 0 := by simp
    have h2 : (-(a : ℂ) * (x : ℂ) ^ 2).re = -a * x ^ 2 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [h1, h2, Real.exp_zero, one_mul]
  have hre := congrArg Complex.re hF
  have h3 : ∫ x : ℝ, (Complex.exp (Complex.I * (w : ℂ) * x) *
      Complex.exp (-(a : ℂ) * x ^ 2)).re =
      (∫ x : ℝ, Complex.exp (Complex.I * (w : ℂ) * x) * Complex.exp (-(a : ℂ) * x ^ 2)).re :=
    integral_re hint
  rw [← h3] at hre
  have hpt : ∀ x : ℝ, (Complex.exp (Complex.I * (w : ℂ) * x) *
      Complex.exp (-(a : ℂ) * x ^ 2)).re = Real.exp (-(a * x ^ 2)) * Real.cos (x * w) := by
    intro x
    have e1 : Complex.exp (-(a : ℂ) * x ^ 2) = ((Real.exp (-(a * x ^ 2)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    have e2 : Complex.I * (w : ℂ) * x = ((x * w : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e1, e2, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, mul_comm]
  simp_rw [hpt] at hre
  rw [hre]
  have e3 : ((π : ℂ) / (a : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt (π / a) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  have e4 : Complex.exp (-(w : ℂ) ^ 2 / (4 * (a : ℂ))) =
      ((Real.exp (-(w ^ 2 / (4 * a))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; push_cast; ring_nf
  rw [e3, e4, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Auxiliary to the Lean proof route.  The Gaussian cosine integral on the half
line: `∫_0^∞ e^{-ar²} cos(rw) dr = π p_{2a}^{(1)}(w)`, with integrability. -/
theorem integral_gauss_cos (a w : ℝ) (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => Real.exp (-(a * r ^ 2)) * Real.cos (r * w)) (Ioi 0) ∧
      ∫ r in Ioi (0 : ℝ), Real.exp (-(a * r ^ 2)) * Real.cos (r * w) = π * gauss1 a w := by
  have hI : Integrable (fun r : ℝ => Real.exp (-(a * r ^ 2)) * Real.cos (r * w)) := by
    refine Integrable.mono' (integrable_exp_neg_mul_sq ha) (by fun_prop)
      (Eventually.of_forall fun r => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
  refine ⟨hI.integrableOn, ?_⟩
  have habs := integral_comp_abs (f := fun r : ℝ => Real.exp (-(a * r ^ 2)) * Real.cos (r * w))
  have hev : ∀ x : ℝ, Real.exp (-(a * |x| ^ 2)) * Real.cos (|x| * w) =
      Real.exp (-(a * x ^ 2)) * Real.cos (x * w) := by
    intro x
    rcases abs_cases x with ⟨hx, -⟩ | ⟨hx, -⟩ <;> rw [hx]
    · simp [neg_mul, Real.cos_neg]
  simp only [hev] at habs
  rw [integral_gauss_cos_line a w ha] at habs
  have key : Real.sqrt (π / a) * Real.sqrt (4 * π * a) = 2 * π := by
    rw [← Real.sqrt_mul (by positivity)]
    have : π / a * (4 * π * a) = (2 * π) ^ 2 := by field_simp; ring
    rw [this, Real.sqrt_sq (by positivity)]
  have hs : 0 < Real.sqrt (4 * π * a) := Real.sqrt_pos.2 (by positivity)
  have hg : gauss1 a w = (Real.sqrt (4 * π * a))⁻¹ * Real.exp (-(w ^ 2 / (4 * a))) := by
    unfold gauss1
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity)]
  rw [hg]
  have : ∫ r in Ioi (0 : ℝ), Real.exp (-(a * r ^ 2)) * Real.cos (r * w) =
      Real.sqrt (π / a) * Real.exp (-(w ^ 2 / (4 * a))) / 2 := by linarith
  have hsq : Real.sqrt (π / a) = 2 * π / Real.sqrt (4 * π * a) := by
    rw [eq_div_iff hs.ne']; exact key
  rw [this, hsq]
  field_simp

/-- Auxiliary to the Lean proof route.  `sin(hr)/r = ½ ∫_{-h}^{h} cos(ru) du` for `r ≠ 0`. -/
theorem sin_div_eq_integral (h r : ℝ) (hr : r ≠ 0) :
    Real.sin (h * r) / r = (1 / 2) * ∫ u in (-h)..h, Real.cos (r * u) := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hr, integral_cos]
  rw [mul_neg, Real.sin_neg, smul_eq_mul]
  field_simp
  ring_nf

/-- Auxiliary to the Lean proof route.  The radial integrand of `I_a(h,v)` is
integrable on `(0,∞)` (`a > 0`): it is bounded by `|h| e^{-ar²}` (TeX lines 5682-5683). -/
theorem Ia_integrableOn (a h v : ℝ) (ha : 0 < a) :
    IntegrableOn (fun r : ℝ => Real.exp (-(a * r ^ 2)) * (Real.sin (h * r) / r) *
      Real.cos (r * v)) (Ioi 0) := by
  refine Integrable.mono' ((integrable_exp_neg_mul_sq ha).const_mul |h|).integrableOn
    (by fun_prop : Measurable fun r : ℝ => Real.exp (-(a * r ^ 2)) * (Real.sin (h * r) / r) *
      Real.cos (r * v)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
  have hr0 : 0 < r := hr
  have hs : |Real.sin (h * r) / r| ≤ |h| := by
    rw [abs_div, abs_of_pos hr0, div_le_iff₀ hr0]
    calc |Real.sin (h * r)| ≤ |h * r| := Real.abs_sin_le_abs
      _ = |h| * r := by rw [abs_mul, abs_of_pos hr0]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul]
  calc Real.exp (-(a * r ^ 2)) * |Real.sin (h * r) / r| * |Real.cos (r * v)|
      ≤ Real.exp (-(a * r ^ 2)) * |h| * 1 := by
        gcongr
        exact Real.abs_cos_le_one _
    _ = |h| * Real.exp (-(a * r ^ 2)) := by ring

/-- **`I_a(h,v) = π (g_h * p_{2a}^{(1)})(v)` and `0 ≤ I_a(h,v) ≤ π/2`** (proof of
`L:alpha-one-convolution`, main TeX lines 5691-5703), for `a > 0`, `h ≥ 0`, every `v`:
the radial integrand is integrable on `(0,∞)`, `y ↦ g_h(y) p_{2a}^{(1)}(v-y)` is
integrable, `I_a(h,v) = π (g_h * p_{2a}^{(1)})(v)`, and `0 ≤ I_a(h,v) ≤ π/2`.
Proof route (differs from the TeX): the TeX identifies `I_a` with the inverse Fourier
transform of `ĝ_h · p̂_{2a}`; here `sin(hr)/r = ½∫_{-h}^{h} cos(ru) du`, Fubini on
`(0,∞) × (-h,h]` and the Gaussian cosine integral `∫_0^∞ e^{-ar²}cos(rw)dr = π p_{2a}(w)`
give the identity without Fourier inversion. -/
theorem alpha_one_radial (a h v : ℝ) (ha : 0 < a) (hh : 0 ≤ h) :
    IntegrableOn (fun r : ℝ => Real.exp (-(a * r ^ 2)) * (Real.sin (h * r) / r) *
      Real.cos (r * v)) (Ioi 0) ∧
    Integrable (fun u => gBox h u * gauss1 a (v - u)) ∧
    Ia a h v = π * boxConv a h v ∧ 0 ≤ Ia a h v ∧ Ia a h v ≤ π / 2 := by
  have hle : -h ≤ h := by linarith
  obtain ⟨hgi, hg1⟩ := gauss1_integrable_and_mass a ha
  have hgv : Integrable (fun u => gauss1 a (v - u)) := hgi.comp_sub_left v
  -- the box convolution as a set integral
  have hbox_pt : ∀ u, gBox h u * gauss1 a (v - u) =
      (Ioo (-h) h).indicator (fun u => (1 / 2 : ℝ) * gauss1 a (v - u)) u := by
    intro u
    by_cases hu : u ∈ Ioo (-h) h
    · simp [gBox, indicator_of_mem hu]
    · simp [gBox, indicator_of_notMem hu]
  have hboxI : Integrable (fun u => gBox h u * gauss1 a (v - u)) := by
    simp_rw [hbox_pt]
    exact (hgv.const_mul _).indicator measurableSet_Ioo
  have hbox : boxConv a h v = (1 / 2) * ∫ u in Ioc (-h) h, gauss1 a (v - u) := by
    unfold boxConv
    simp_rw [hbox_pt]
    rw [integral_indicator measurableSet_Ioo, integral_const_mul, integral_Ioc_eq_integral_Ioo]
  -- Fubini
  have : IsFiniteMeasure (volume.restrict (Ioc (-h) h)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  set F : ℝ → ℝ → ℝ := fun r u =>
    Real.exp (-(a * r ^ 2)) * Real.cos (r * u) * Real.cos (r * v) with hF
  have hFi : Integrable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (-h) h))) := by
    have hd : Integrable (fun z : ℝ × ℝ => Real.exp (-a * z.1 ^ 2) * (1 : ℝ))
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (-h) h))) :=
      Integrable.mul_prod (f := fun r : ℝ => Real.exp (-a * r ^ 2)) (g := fun _ : ℝ => (1 : ℝ))
        (integrable_exp_neg_mul_sq ha).integrableOn (integrable_const (1 : ℝ))
    refine hd.mono' (by rw [hF]; fun_prop) (Eventually.of_forall fun z => ?_)
    simp only [Function.uncurry, hF, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      neg_mul, mul_one]
    calc Real.exp (-(a * z.1 ^ 2)) * |Real.cos (z.1 * z.2)| * |Real.cos (z.1 * v)|
        ≤ Real.exp (-(a * z.1 ^ 2)) * 1 * 1 := by
          gcongr
          · exact Real.abs_cos_le_one _
          · exact Real.abs_cos_le_one _
      _ = Real.exp (-(a * z.1 ^ 2)) := by ring
  have hIa : Ia a h v = (1 / 2) * ∫ r in Ioi (0 : ℝ), ∫ u in Ioc (-h) h, F r u := by
    unfold Ia
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : r ≠ 0 := (ne_of_lt hr).symm
    simp only [hF]
    rw [sin_div_eq_integral h r hr0, intervalIntegral.integral_of_le hle, integral_mul_const,
      integral_const_mul]
    ring
  have hinner : ∀ u, ∫ r in Ioi (0 : ℝ), F r u =
      (π / 2) * (gauss1 a (u - v) + gauss1 a (u + v)) := by
    intro u
    obtain ⟨i1, e1⟩ := integral_gauss_cos a (u - v) ha
    obtain ⟨i2, e2⟩ := integral_gauss_cos a (u + v) ha
    have hpt : ∀ r, F r u = (1 / 2) * (Real.exp (-(a * r ^ 2)) * Real.cos (r * (u - v))) +
        (1 / 2) * (Real.exp (-(a * r ^ 2)) * Real.cos (r * (u + v))) := by
      intro r
      simp only [hF, mul_sub, mul_add, Real.cos_sub, Real.cos_add]
      ring
    simp_rw [hpt]
    rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
      e1, e2]
    ring
  have hswap := integral_integral_swap hFi
  rw [hswap] at hIa
  simp_rw [hinner] at hIa
  have hsym : ∫ u in Ioc (-h) h, (π / 2) * (gauss1 a (u - v) + gauss1 a (u + v)) =
      π * ∫ u in Ioc (-h) h, gauss1 a (v - u) := by
    have i1 : IntervalIntegrable (fun u => gauss1 a (u - v)) volume (-h) h :=
      (hgi.comp_sub_right v).intervalIntegrable
    have i2 : IntervalIntegrable (fun u => gauss1 a (u + v)) volume (-h) h :=
      (hgi.comp_add_right v).intervalIntegrable
    rw [← intervalIntegral.integral_of_le hle, ← intervalIntegral.integral_of_le hle,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add i1 i2]
    have e1 : ∫ u in (-h)..h, gauss1 a (u - v) = ∫ u in (-h)..h, gauss1 a (v - u) := by
      congr 1; funext u; rw [← gauss1_neg, neg_sub]
    have e2 : ∫ u in (-h)..h, gauss1 a (u + v) = ∫ u in (-h)..h, gauss1 a (v - u) := by
      have := intervalIntegral.integral_comp_neg (a := -h) (b := h)
        (fun u => gauss1 a (v - u))
      simp only [neg_neg, sub_neg_eq_add] at this
      rw [← this]; congr 1; funext u; rw [add_comm]
    rw [e1, e2]; ring
  rw [hsym] at hIa
  have hId : Ia a h v = π * boxConv a h v := by rw [hIa, hbox]; ring
  -- bounds
  have hb0 : 0 ≤ boxConv a h v := by
    rw [hbox]
    exact mul_nonneg (by norm_num) (setIntegral_nonneg measurableSet_Ioc
      fun u _ => gauss1_nonneg a _ ha)
  have hb1 : boxConv a h v ≤ 1 / 2 := by
    rw [hbox]
    have : ∫ u in Ioc (-h) h, gauss1 a (v - u) ≤ ∫ u, gauss1 a (v - u) :=
      setIntegral_le_integral hgv (Eventually.of_forall fun u => gauss1_nonneg a _ ha)
    rw [integral_sub_left_eq_self (gauss1 a) volume v, hg1] at this
    linarith
  refine ⟨Ia_integrableOn a h v ha, hboxI, hId, ?_, ?_⟩
  · rw [hId]; positivity
  · rw [hId]; nlinarith [Real.pi_pos]

/-- Auxiliary (not a TeX step; used by the refutations).  `I_a(-h,v) = -I_a(h,v)`. -/
theorem Ia_neg_h (a h v : ℝ) : Ia a (-h) v = -Ia a h v := by
  unfold Ia
  rw [← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only [neg_mul, Real.sin_neg, neg_div]
  ring

/-- Auxiliary (not a TeX step; used by the refutations).  A lower bound for the box
convolution at `v = 0`: `h p_{2a}^{(1)}(h) ≤ (g_h * p_{2a}^{(1)})(0)` (`a > 0`, `h ≥ 0`). -/
theorem boxConv_zero_ge (a h : ℝ) (ha : 0 < a) (hh : 0 ≤ h) :
    h * gauss1 a h ≤ boxConv a h 0 := by
  have hI := (alpha_one_radial a h 0 ha hh).2.1
  have hc : Integrable ((Ioo (-h) h).indicator fun _ : ℝ => (1 / 2 : ℝ) * gauss1 a h) :=
    (integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_const (by simp))
  have hle : ∀ u, (Ioo (-h) h).indicator (fun _ : ℝ => (1 / 2 : ℝ) * gauss1 a h) u ≤
      gBox h u * gauss1 a (0 - u) := by
    intro u
    by_cases hu : u ∈ Ioo (-h) h
    · rw [indicator_of_mem hu, gBox, indicator_of_mem hu]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      unfold gauss1
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
      have h4 : 0 < 4 * a := by positivity
      have hsq : (0 - u) ^ 2 ≤ h ^ 2 := by nlinarith [hu.1, hu.2]
      have := div_le_div_of_nonneg_right hsq h4.le
      linarith
    · rw [indicator_of_notMem hu, gBox, indicator_of_notMem hu, zero_mul]
  calc h * gauss1 a h
      = ∫ u, (Ioo (-h) h).indicator (fun _ : ℝ => (1 / 2 : ℝ) * gauss1 a h) u := by
        rw [integral_indicator_const _ measurableSet_Ioo, measureReal_def, Real.volume_Ioo,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        ring
    _ ≤ boxConv a h 0 := integral_mono hc hI hle

/-! ### (i) Polar decomposition of a degree-one spectral measure -/

variable {d : ℕ}

/-- `ξ ↦ ξ/|ξ|` (Lean's value at `ξ = 0` is `0`; only `ξ ≠ 0` is used). -/
def nrm (ξ : Rd d) : Rd d := ‖ξ‖⁻¹ • ξ

/-- The angular measure `σ(E) = μ{ξ : 0 < |ξ| ≤ 1, ξ/|ξ| ∈ E}` (main TeX line 5657),
realized as a measure on `ℝ^d` concentrated on the unit sphere
(`polar_decomposition`), not as a measure on the sphere subtype. -/
def sphereMeasure (μ : Measure (Rd d)) : Measure (Rd d) :=
  (μ.restrict (closedBall 0 1 \ {0})).map nrm

/-- The polar map `(θ, r) ↦ rθ`. -/
def polarMap (p : Rd d × ℝ) : Rd d := p.2 • p.1

/-- Auxiliary to the Lean proof route. -/
theorem measurable_nrm : Measurable (nrm (d := d)) := by
  unfold nrm; fun_prop

/-- Auxiliary to the Lean proof route. -/
theorem measurable_polarMap : Measurable (polarMap (d := d)) := by
  unfold polarMap; fun_prop

/-- Auxiliary to the Lean proof route. -/
theorem norm_nrm {ξ : Rd d} (hξ : ξ ≠ 0) : ‖nrm ξ‖ = 1 := by
  rw [nrm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hξ)]

/-- Auxiliary to the Lean proof route. -/
theorem nrm_smul (ξ : Rd d) {r : ℝ} (hr : 0 < r) : nrm (r • ξ) = nrm ξ := by
  unfold nrm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, smul_smul, mul_inv_rev, mul_assoc,
    inv_mul_cancel₀ hr.ne', mul_one]

/-- The defining formula of `σ` (main TeX line 5657): for measurable `E`,
`σ(E) = μ{ξ : 0 < |ξ| ≤ 1, ξ/|ξ| ∈ E}`. -/
theorem sphereMeasure_apply (μ : Measure (Rd d)) {E : Set (Rd d)} (hE : MeasurableSet E) :
    sphereMeasure μ E = μ ({ξ | ξ ≠ 0 ∧ ‖ξ‖ ≤ 1} ∩ nrm ⁻¹' E) := by
  rw [sphereMeasure, Measure.map_apply measurable_nrm hE,
    Measure.restrict_apply (measurable_nrm hE)]
  congr 1
  ext ξ
  simp only [mem_inter_iff, mem_preimage, Set.mem_sdiff, mem_closedBall_zero_iff,
    mem_singleton_iff, mem_ofPred_eq]
  tauto

/-- Auxiliary to the Lean proof route.  `σ` is a finite measure when `μ` is locally
finite. -/
instance isFiniteMeasure_sphereMeasure (μ : Measure (Rd d)) [IsLocallyFiniteMeasure μ] :
    IsFiniteMeasure (sphereMeasure μ) := by
  unfold sphereMeasure
  have : IsFiniteMeasure (μ.restrict (closedBall (0 : Rd d) 1 \ {0})) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact (measure_mono sdiff_subset).trans_lt measure_closedBall_lt_top⟩
  infer_instance

/-- Auxiliary to the Lean proof route.  Cone masses: for `μ(cA) = cμ(A)`, `μ` locally
finite and measurable `s`, `μ{|ξ| ≤ r, ξ/|ξ| ∈ s} = r⁺ σ(s)` for every real `r` (main TeX
lines 5659-5660: "the corresponding sector of radius `R` has mass `Rσ(E)`"). -/
theorem cone_measure {μ : Measure (Rd d)} (hI : SpectralHomogeneous μ 1)
    [IsLocallyFiniteMeasure μ] {s : Set (Rd d)} (hs : MeasurableSet s) (r : ℝ) :
    μ (closedBall 0 r ∩ nrm ⁻¹' s) = ENNReal.ofReal r * sphereMeasure μ s := by
  have h0 : μ {0} = 0 := SpectralHomog.measure_zero hI one_pos
  set C : ℝ → Set (Rd d) := fun r => {ξ | ξ ≠ 0 ∧ ‖ξ‖ ≤ r} ∩ nrm ⁻¹' s with hC
  have hCm : ∀ r, MeasurableSet (C r) := fun r =>
    ((measurableSet_singleton (0 : Rd d)).compl.inter
      (measurableSet_le measurable_norm measurable_const)).inter (measurable_nrm hs)
  -- `D r` and `C r` differ by a subset of `{0}`
  have hDC : μ (closedBall 0 r ∩ nrm ⁻¹' s) = μ (C r) := by
    refine le_antisymm ?_ (measure_mono fun ξ hξ => ⟨mem_closedBall_zero_iff.2 hξ.1.2, hξ.2⟩)
    calc μ (closedBall 0 r ∩ nrm ⁻¹' s) ≤ μ (C r ∪ {0}) := by
          refine measure_mono fun ξ hξ => ?_
          by_cases h : ξ = 0
          · exact Or.inr h
          · exact Or.inl ⟨⟨h, mem_closedBall_zero_iff.1 hξ.1⟩, hξ.2⟩
      _ ≤ μ (C r) + μ {0} := measure_union_le _ _
      _ = μ (C r) := by rw [h0, add_zero]
  rw [hDC]
  rcases le_or_gt r 0 with hr | hr
  · have hempty : C r = ∅ := by
      ext ξ
      simp only [hC, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨⟨hξ, hle⟩, -⟩
      exact hξ (norm_le_zero_iff.1 (hle.trans hr))
    rw [hempty, measure_empty, ENNReal.ofReal_of_nonpos hr, zero_mul]
  · have hsc : C r = r • C 1 := by
      ext ξ
      rw [Set.mem_smul_set]
      constructor
      · rintro ⟨⟨hξ, hle⟩, hns⟩
        refine ⟨r⁻¹ • ξ, ⟨⟨smul_ne_zero (inv_ne_zero hr.ne') hξ, ?_⟩, ?_⟩, ?_⟩
        · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr), inv_mul_le_iff₀ hr,
            mul_one]
          exact hle
        · show nrm (r⁻¹ • ξ) ∈ s
          rw [nrm_smul ξ (inv_pos.2 hr)]; exact hns
        · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      · rintro ⟨y, ⟨⟨hy, hle⟩, hns⟩, rfl⟩
        refine ⟨⟨smul_ne_zero hr.ne' hy, ?_⟩, ?_⟩
        · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
          nlinarith [norm_nonneg y]
        · show nrm (r • y) ∈ s
          rw [nrm_smul y hr]; exact hns
    rw [hsc, hI _ (hCm 1) r hr, Real.rpow_one, sphereMeasure_apply μ hs]

/-- **Polar decomposition of a degree-one spectral measure** (proof of
`L:alpha-one-convolution`, main TeX lines 5653-5665).  Let `μ` be a locally finite
measure on `ℝ^d` with `μ(cA) = cμ(A)` for Borel `A` and `c > 0`
(`SpectralHomogeneous μ 1`).  Then `μ{0} = 0`, `V = μ{|ξ| ≤ 1} < ∞`, the angular
measure `σ` (`sphereMeasure μ`) has total mass `V` and is concentrated on the unit
sphere, and `μ` is the image of `σ ⊗ (dr on (0,∞))` under `(θ, r) ↦ rθ`, i.e.
`μ(dξ) = dr σ(dθ)`.  The uniqueness step uses rectangles `s × (a, b]` (Mathlib's
`Measure.prod_eq` and `Measure.ext_of_Ioc'`), as in the TeX. -/
theorem polar_decomposition {μ : Measure (Rd d)} (hI : SpectralHomogeneous μ 1)
    [IsLocallyFiniteMeasure μ] :
    μ {0} = 0 ∧ μ (closedBall 0 1) < ⊤ ∧ sphereMeasure μ univ = μ (closedBall 0 1) ∧
      sphereMeasure μ (sphere 0 1)ᶜ = 0 ∧
      μ = ((sphereMeasure μ).prod (volume.restrict (Ioi (0 : ℝ)))).map polarMap := by
  have h0 : μ {0} = 0 := SpectralHomog.measure_zero hI one_pos
  refine ⟨h0, measure_closedBall_lt_top, ?_, ?_, ?_⟩
  · rw [sphereMeasure, Measure.map_apply measurable_nrm MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ, measure_sdiff_null h0]
  · rw [sphereMeasure_apply μ isClosed_sphere.measurableSet.compl]
    convert measure_empty (μ := μ)
    ext ξ
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, mem_compl_iff, mem_sphere_iff_norm,
      sub_zero, mem_empty_iff_false, iff_false, not_and, not_not]
    rintro ⟨hξ, -⟩
    exact norm_nrm hξ
  -- the polar coordinates map
  set P : Rd d → Rd d × ℝ := fun ξ => (nrm ξ, ‖ξ‖) with hP
  have hPm : Measurable P := measurable_nrm.prodMk measurable_norm
  have hprod : μ.map P = (sphereMeasure μ).prod (volume.restrict (Ioi (0 : ℝ))) := by
    symm
    refine Measure.prod_eq fun s t hs ht => ?_
    rw [Measure.map_apply hPm (hs.prod ht)]
    -- the radial law of the cone over `s`
    set m1 : Measure ℝ := (μ.restrict (nrm ⁻¹' s)).map (fun ξ => ‖ξ‖) with hm1
    set m2 : Measure ℝ := sphereMeasure μ s • volume.restrict (Ioi (0 : ℝ)) with hm2
    have hσs : sphereMeasure μ s ≠ ⊤ := measure_ne_top _ _
    have hm1I : ∀ a b : ℝ, a < b →
        m1 (Ioc a b) = (ENNReal.ofReal b - ENNReal.ofReal a) * sphereMeasure μ s := by
      intro a b hab
      rw [hm1, Measure.map_apply measurable_norm measurableSet_Ioc,
        Measure.restrict_apply (measurable_norm measurableSet_Ioc)]
      have hset : (fun ξ : Rd d => ‖ξ‖) ⁻¹' Ioc a b ∩ nrm ⁻¹' s =
          (closedBall 0 b ∩ nrm ⁻¹' s) \ (closedBall 0 a ∩ nrm ⁻¹' s) := by
        ext ξ
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioc, Set.mem_sdiff,
          mem_closedBall_zero_iff]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨⟨h2, h3⟩, fun h => absurd h.1 (not_le.2 h1)⟩
        · rintro ⟨⟨h2, h3⟩, h4⟩
          exact ⟨⟨lt_of_not_ge fun h => h4 ⟨h, h3⟩, h2⟩, h3⟩
      rw [hset, measure_sdiff (inter_subset_inter_left _ (closedBall_subset_closedBall hab.le))
        ((measurableSet_closedBall.inter (measurable_nrm hs)).nullMeasurableSet)
        (by rw [cone_measure hI hs a]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hσs),
        cone_measure hI hs a, cone_measure hI hs b, ENNReal.sub_mul fun _ _ => hσs]
    have hm2I : ∀ a b : ℝ, a < b →
        m2 (Ioc a b) = (ENNReal.ofReal b - ENNReal.ofReal a) * sphereMeasure μ s := by
      intro a b hab
      rw [hm2, Measure.smul_apply, Measure.restrict_apply measurableSet_Ioc, smul_eq_mul,
        mul_comm]
      have hset : Ioc a b ∩ Ioi (0 : ℝ) = Ioc (max a 0) b := by
        ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ioi, max_lt_iff]; tauto
      rw [hset, Real.volume_Ioc]
      congr 1
      rcases le_or_gt a 0 with ha | ha
      · simp [max_eq_right ha, ENNReal.ofReal_of_nonpos ha]
      · rw [max_eq_left ha.le, ENNReal.ofReal_sub _ ha.le]
    have hm : m1 = m2 := Measure.ext_of_Ioc' m1 m2
      (fun a b hab => by
        rw [hm1I a b hab]
        exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top tsub_le_self) hσs)
      (fun a b hab => by rw [hm1I a b hab, hm2I a b hab])
    have ht' := congrArg (fun m : Measure ℝ => m t) hm
    simp only [hm1, hm2, Measure.map_apply measurable_norm ht,
      Measure.restrict_apply (measurable_norm ht), Measure.smul_apply, smul_eq_mul] at ht'
    have hpre : P ⁻¹' s ×ˢ t = (fun ξ : Rd d => ‖ξ‖) ⁻¹' t ∩ nrm ⁻¹' s := by
      ext ξ; simp only [hP, mem_preimage, mem_prod, mem_inter_iff]; tauto
    rw [hpre, ht']
  have hid : polarMap ∘ P = id := by
    funext ξ
    simp only [Function.comp_apply, hP, polarMap, nrm, id]
    by_cases hξ : ξ = 0
    · simp [hξ]
    · rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hξ), one_smul]
  rw [← hprod, Measure.map_map measurable_polarMap hPm, hid, Measure.map_id]

/-- `σ` is even when `μ` is (main TeX lines 5664-5665: "Fourier uniqueness makes `μ`,
and hence `σ`, even"; here the evenness of `μ` is the hypothesis). -/
theorem sphereMeasure_even {μ : Measure (Rd d)} (hμe : HomogHypothesis.IsEven μ) :
    HomogHypothesis.IsEven (sphereMeasure μ) := by
  unfold HomogHypothesis.IsEven sphereMeasure
  set S : Set (Rd d) := closedBall 0 1 \ {0} with hS
  have hSm : MeasurableSet S := measurableSet_closedBall.diff (measurableSet_singleton 0)
  have hneg : Measurable (fun x : Rd d => -x) := measurable_neg
  have hSneg : (fun x : Rd d => -x) ⁻¹' S = S := by
    ext ξ; simp [hS]
  have hnn : (fun x : Rd d => -x) ∘ nrm = nrm ∘ (fun x : Rd d => -x) := by
    funext ξ; simp [nrm, norm_neg, smul_neg]
  have hres : (μ.restrict S).map (fun x : Rd d => -x) = μ.restrict S := by
    have := Measure.restrict_map (μ := μ) hneg hSm
    rw [hSneg, hμe] at this
    exact this.symm
  rw [Measure.map_map hneg measurable_nrm, hnn, ← Measure.map_map measurable_nrm hneg, hres]

/-- The polar integration formula (auxiliary to the Lean proof route; the integral form of
`μ(dξ) = dr σ(dθ)`): for `μ` as in `polar_decomposition` and `f` integrable,
`θ ↦ ∫_0^∞ f(rθ) dr` is `σ`-integrable and `∫ f dμ = ∫ (∫_0^∞ f(rθ) dr) σ(dθ)`. -/
theorem polar_integral {μ : Measure (Rd d)} (hI : SpectralHomogeneous μ 1)
    [IsLocallyFiniteMeasure μ] {f : Rd d → ℝ} (hf : Integrable f μ) :
    Integrable (fun θ : Rd d => ∫ r : ℝ in Ioi 0, f (r • θ)) (sphereMeasure μ) ∧
      ∫ ξ, f ξ ∂μ = ∫ θ : Rd d, (∫ r : ℝ in Ioi 0, f (r • θ)) ∂(sphereMeasure μ) := by
  have hpol := (polar_decomposition hI).2.2.2.2
  have hf' := hf
  rw [hpol] at hf'
  have hfc : Integrable (f ∘ polarMap)
      ((sphereMeasure μ).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (integrable_map_measure hf'.aestronglyMeasurable measurable_polarMap.aemeasurable).1 hf'
  refine ⟨hfc.integral_prod_left, ?_⟩
  conv_lhs => rw [hpol]
  rw [integral_map measurable_polarMap.aemeasurable hf'.aestronglyMeasurable]
  exact integral_prod (fun p => f (polarMap p)) hfc

/-! ### (iii) `E:alpha-one-polar` and the bound `0 ≤ … ≤ πV/2` -/

open WaveKernel (waveHat waveHat_of_ne_zero abs_waveHat_le waveHat_continuous)

/-- **`E:alpha-one-polar` on the spectral side, and its bound** (proof of
`L:alpha-one-convolution`, main TeX lines 5674-5704).  Let `μ` be locally finite and
tempered with `μ(cA) = cμ(A)`, `a > 0`, `h ≥ 0`, `z ∈ ℝ^d`, and `V = μ{|ξ| ≤ 1}`.  Then
`ξ ↦ Ĝ_h(ξ) e^{-a|ξ|²} cos(ξ·z)` is `μ`-integrable, `θ ↦ I_a(h, θ·z)` is `σ`-integrable,
`∫ Ĝ_h(ξ) e^{-a|ξ|²} cos(ξ·z) μ(dξ) = ∫ I_a(h, θ·z) σ(dθ)`, and
`0 ≤ ∫ I_a(h, θ·z) σ(dθ) ≤ πV/2`.  Here `Ĝ_h = waveHat h` is the function
`sin(h|ξ|)/|ξ|` (value `h` at `0`); its identification with the Fourier transform of
`G_h` is not used in this theorem. -/
theorem alpha_one_polar {μ : Measure (Rd d)} (hI : SpectralHomogeneous μ 1)
    [IsLocallyFiniteMeasure μ] (hμt : IsTempered μ) {a : ℝ} (ha : 0 < a) {h : ℝ}
    (hh : 0 ≤ h) (z : Rd d) :
    Integrable (fun ξ : Rd d => waveHat h ξ * Real.exp (-(a * ‖ξ‖ ^ 2)) *
      Real.cos (inner ℝ ξ z)) μ ∧
    Integrable (fun θ : Rd d => Ia a h (inner ℝ θ z)) (sphereMeasure μ) ∧
    ∫ ξ, waveHat h ξ * Real.exp (-(a * ‖ξ‖ ^ 2)) * Real.cos (inner ℝ ξ z) ∂μ =
      ∫ θ, Ia a h (inner ℝ θ z) ∂(sphereMeasure μ) ∧
    0 ≤ ∫ θ, Ia a h (inner ℝ θ z) ∂(sphereMeasure μ) ∧
    ∫ θ, Ia a h (inner ℝ θ z) ∂(sphereMeasure μ) ≤ π * (μ (closedBall 0 1)).toReal / 2 := by
  obtain ⟨-, hV, hσV, hσS, -⟩ := polar_decomposition hI
  set f : Rd d → ℝ := fun ξ => waveHat h ξ * Real.exp (-(a * ‖ξ‖ ^ 2)) *
    Real.cos (inner ℝ ξ z) with hf
  have hfc : Continuous f := by
    have : Continuous fun ξ : Rd d => waveHat h ξ :=
      waveHat_continuous.comp (continuous_const.prodMk continuous_id)
    rw [hf]; fun_prop
  have hfi : Integrable f μ := by
    refine ((MaskedSpectralGrowth.integrable_gauss_zero hμt ha).const_mul |h|).mono'
      hfc.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    rw [hf, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |waveHat h ξ| * Real.exp (-(a * ‖ξ‖ ^ 2)) * |Real.cos (inner ℝ ξ z)|
        ≤ |h| * Real.exp (-(a * ‖ξ‖ ^ 2)) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right (abs_waveHat_le h ξ) (Real.exp_pos _).le)
            (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
      _ = |h| * Real.exp (-(a * ‖ξ‖ ^ 2)) := mul_one _
  obtain ⟨hpi, hpe⟩ := polar_integral hI hfi
  have hae : ∀ᵐ θ ∂(sphereMeasure μ), ∫ r : ℝ in Ioi 0, f (r • θ) = Ia a h (inner ℝ θ z) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hσS] with θ hθ
    have hθ1 : ‖θ‖ = 1 := by simpa using hθ
    unfold Ia
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 < r := hr
    have hn : ‖r • θ‖ = r := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hθ1, mul_one]
    have hne : r • θ ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hn; exact hr0.ne' hn.symm
    simp only [hf]
    rw [waveHat_of_ne_zero h _ hne, hn, real_inner_smul_left]
    ring
  have hIai : Integrable (fun θ : Rd d => Ia a h (inner ℝ θ z)) (sphereMeasure μ) :=
    hpi.congr hae
  have hb := fun θ : Rd d => alpha_one_radial a h (inner ℝ θ z) ha hh
  refine ⟨hfi, hIai, hpe.trans (integral_congr_ae hae), ?_, ?_⟩
  · exact integral_nonneg fun θ => (hb θ).2.2.2.1
  · calc ∫ θ, Ia a h (inner ℝ θ z) ∂(sphereMeasure μ)
        ≤ ∫ _θ, π / 2 ∂(sphereMeasure μ) :=
          integral_mono hIai (integrable_const _) fun θ => (hb θ).2.2.2.2
      _ = π * (μ (closedBall 0 1)).toReal / 2 := by
          rw [integral_const, smul_eq_mul, measureReal_def, hσV]; ring

/-! ### (iv) The convolution bound `E:alpha-one-convolution` -/

open WaveGreen (waveGreen waveGreen_fourier_one isFiniteMeasure_waveGreen)
open VariationalDilation (conv)
open VariationalMean (heatK)
open LowAlphaConvolution (smoothedGreen)

/-- Auxiliary to the Lean proof route.  Gaussian smoothing multiplies the characteristic
function by `e^{-η|ξ|²/2}` (`η ≥ 0`, `G_h` finite); `smoothedGreen` is
`LowAlphaConvolution.smoothedGreen`, and this is `DampedMultiplier.charFun_gaussKernel_conv`
in the real-exponential form used below. -/
theorem charFun_smoothedGreen (G : ℝ → Measure (Rd d)) (h : ℝ) [IsFiniteMeasure (G h)]
    {η : ℝ} (hη : 0 ≤ η) (ξ : Rd d) :
    charFun (smoothedGreen G h η) ξ =
      (Real.exp (-(η * ‖ξ‖ ^ 2 / 2)) : ℂ) * charFun (G h) ξ := by
  rw [smoothedGreen, DampedMultiplier.charFun_gaussKernel_conv η hη, Complex.ofReal_exp]
  push_cast
  ring_nf

/-- Auxiliary (bridge to wave L9-L).  The smoothed covariance `γ_ε(x) = (Γ * p_ε)(x)`
used here, `VariationalDilation.conv Γ (VariationalMean.heatK ε) x`, is definitionally
`∫ (2πε)^{-d/2} e^{-|x-y|²/(2ε)} Γ(dy)`, the body of `LowAlphaConvolution.gammaEps`. -/
theorem conv_heatK_eq (Γ : Measure (Rd d)) (ε : ℝ) (x : Rd d) :
    conv Γ (heatK ε) x =
      ∫ y, (2 * π * ε) ^ (-((d : ℝ) / 2)) * Real.exp (-(‖x - y‖ ^ 2 / (2 * ε))) ∂Γ := rfl

/-- Auxiliary (bridge to wave L9-L).  `γ_ε = Γ * p_ε` of this module is wave L9-L's
`LowAlphaConvolution.gammaEps Γ ε` (the same integral; definitional). -/
theorem conv_heatK_eq_gammaEps (Γ : Measure (Rd d)) (ε : ℝ) :
    conv Γ (heatK ε) = LowAlphaConvolution.gammaEps Γ ε := rfl

/-- **Named input `SpectralPairing Γ μ`**: the Fourier-Fubini spectral representation of
the smoothed pairing.  For `h > 0`, `ε > 0`, `η ≥ 0` and `z ∈ ℝ^d`, the function
`y ↦ γ_ε(y + z)` (with `γ_ε = Γ * p_ε`, `γ_ε(x) = ∫ p_ε(x - y) Γ(dy)`) is
`G_{h,η}`-integrable and
`∫ G_{h,η}(dy) γ_ε(y + z) = ∫ Ĝ_{h,η}(ξ) e^{iξ·z} e^{-ε|ξ|²/2} μ(dξ)`,
where `Ĝ_{h,η} = charFun G_{h,η}`, `Ĝ(ξ) = ∫ e^{i y·ξ} G(dy)`.  Manuscript source: the
"Fourier Fubini" step for `γ_ε` and the finite measure `G_{h,η}`, stated in the proof of
`L:low-alpha-convolution` (main TeX lines 5610-5612) and used again at line 5673 of the
proof of `L:alpha-one-convolution`; wave L9-L proves it for every finite measure in place
of `G_{h,η}` (`LowAlphaConvolution.smoothed_pairing_spectral`), for tempered `Γ`, `μ` with
the spectral convention.  It contains no Fourier transform of `G_h` and no homogeneity. -/
def SpectralPairing (Γ μ : Measure (Rd d)) : Prop :=
  ∀ h : ℝ, 0 < h → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 ≤ η → ∀ z : Rd d,
    Integrable (fun y => conv Γ (heatK ε) (y + z)) (smoothedGreen (waveGreen d) h η) ∧
      ((∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen d) h η) : ℝ) : ℂ) =
        ∫ ξ, charFun (smoothedGreen (waveGreen d) h η) ξ *
          Complex.exp (Complex.I * (inner ℝ ξ z : ℝ)) * (Real.exp (-(ε * ‖ξ‖ ^ 2 / 2)) : ℂ) ∂μ

/-- **Named input `WaveGreenFourier d`**: the Fourier identity of the wave Green measures,
`∫ e^{iξ·y} G_s(dy) = Ĝ_s(ξ) = sin(s|ξ|)/|ξ|` (value `s` at `ξ = 0`) for `s > 0`, from
the source's wave-kernel formulas as quoted at main TeX lines 5614-5618 (and lines
983-984).  Proved in `d = 1` (`waveGreenFourier_one`, from
`WaveGreen.waveGreen_fourier_one`); for `d ∈ {1,2,3}` it is
`L10Completed.waveGreenFourier_holds` (from wave L9-G). -/
def WaveGreenFourier (d : ℕ) : Prop :=
  ∀ s : ℝ, 0 < s → ∀ ξ : Rd d,
    ∫ x, Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) ∂(waveGreen d s) = (waveHat s ξ : ℂ)

/-- `WaveGreenFourier 1` holds (from `WaveGreen.waveGreen_fourier_one`). -/
theorem waveGreenFourier_one : WaveGreenFourier 1 := fun s hs ξ =>
  (waveGreen_fourier_one s hs ξ).2

/-- **`L:alpha-one-convolution`, general form** (main TeX lines 5635-5707).  Let `μ` be a
locally finite tempered measure with `μ(cA) = cμ(A)` (`SpectralHomogeneous μ 1`), and
assume the two named inputs `SpectralPairing Γ μ` and `WaveGreenFourier d`.  Then
`V = μ{|ξ| ≤ 1} < ∞`, and for every `h > 0`, `ε > 0`, `η ≥ 0`, `z ∈ ℝ^d`, with
`a = (ε + η)/2`: `y ↦ γ_ε(y + z)` is `G_{h,η}`-integrable,
`∫ G_{h,η}(dy) γ_ε(y + z) = ∫ I_a(h, θ·z) σ(dθ)` (`E:alpha-one-polar`, with
`σ = sphereMeasure μ`), and `0 ≤ ∫ G_{h,η}(dy) γ_ε(y + z) ≤ πV/2`
(`E:alpha-one-convolution`).  Proof-route difference: the TeX passes from the complex
exponential to the cosine by the evenness of `σ`; here the left side is real, so the
spectral identity is equated with its real part (evenness of `σ` is proved separately,
`sphereMeasure_even`, and not used). -/
theorem alpha_one_convolution {Γ μ : Measure (Rd d)} (hI : SpectralHomogeneous μ 1)
    [IsLocallyFiniteMeasure μ] (hμt : IsTempered μ) (hpair : SpectralPairing Γ μ)
    (hG : WaveGreenFourier d) :
    μ (closedBall 0 1) < ⊤ ∧
      ∀ h : ℝ, 0 < h → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 ≤ η → ∀ z : Rd d,
        Integrable (fun y => conv Γ (heatK ε) (y + z)) (smoothedGreen (waveGreen d) h η) ∧
        (∀ v : ℝ, IntegrableOn (fun r : ℝ => Real.exp (-((ε + η) / 2 * r ^ 2)) *
          (Real.sin (h * r) / r) * Real.cos (r * v)) (Ioi 0)) ∧
        Integrable (fun θ : Rd d => Ia ((ε + η) / 2) h (inner ℝ θ z)) (sphereMeasure μ) ∧
        ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen d) h η) =
          ∫ θ, Ia ((ε + η) / 2) h (inner ℝ θ z) ∂(sphereMeasure μ) ∧
        0 ≤ ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen d) h η) ∧
        ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen d) h η) ≤
          π * (μ (closedBall 0 1)).toReal / 2 := by
  refine ⟨measure_closedBall_lt_top, fun h hh ε hε η hη z => ?_⟩
  obtain ⟨hint, hrep⟩ := hpair h hh ε hε η hη z
  set a : ℝ := (ε + η) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  obtain ⟨hfi, hσi, hpol, h0, h1⟩ := alpha_one_polar hI hμt ha hh.le z
  have := isFiniteMeasure_waveGreen d h
  -- the spectral integrand
  have hpt : ∀ ξ : Rd d, charFun (smoothedGreen (waveGreen d) h η) ξ *
      Complex.exp (Complex.I * (inner ℝ ξ z : ℝ)) * (Real.exp (-(ε * ‖ξ‖ ^ 2 / 2)) : ℂ) =
      ((waveHat h ξ * Real.exp (-(a * ‖ξ‖ ^ 2)) : ℝ) : ℂ) *
        Complex.exp ((inner ℝ ξ z : ℝ) * Complex.I) := by
    intro ξ
    rw [charFun_smoothedGreen _ _ hη, charFun_apply]
    have hc : ∫ x, Complex.exp ((inner ℝ x ξ : ℝ) * Complex.I) ∂(waveGreen d h) =
        (waveHat h ξ : ℂ) := by
      rw [← hG h hh ξ]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [real_inner_comm, mul_comm]
    rw [hc]
    have he : Real.exp (-(η * ‖ξ‖ ^ 2 / 2)) * Real.exp (-(ε * ‖ξ‖ ^ 2 / 2)) =
        Real.exp (-(a * ‖ξ‖ ^ 2)) := by
      rw [← Real.exp_add, ha_def]; congr 1; ring
    rw [← he, Complex.ofReal_mul, Complex.ofReal_mul, mul_comm Complex.I]
    ring
  simp_rw [hpt] at hrep
  have hci : Integrable (fun ξ : Rd d => ((waveHat h ξ * Real.exp (-(a * ‖ξ‖ ^ 2)) : ℝ) : ℂ) *
      Complex.exp ((inner ℝ ξ z : ℝ) * Complex.I)) μ := by
    have hwc : Continuous fun ξ : Rd d => waveHat h ξ :=
      waveHat_continuous.comp (continuous_const.prodMk continuous_id)
    refine ((MaskedSpectralGrowth.integrable_gauss_zero hμt ha).const_mul |h|).mono'
      (by fun_prop) (Eventually.of_forall fun ξ => ?_)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (abs_waveHat_le h ξ) (Real.exp_pos _).le
  have hre := congrArg Complex.re hrep
  rw [Complex.ofReal_re] at hre
  have h3 : ∫ ξ : Rd d, (((waveHat h ξ * Real.exp (-(a * ‖ξ‖ ^ 2)) : ℝ) : ℂ) *
      Complex.exp ((inner ℝ ξ z : ℝ) * Complex.I)).re ∂μ =
      (∫ ξ : Rd d, ((waveHat h ξ * Real.exp (-(a * ‖ξ‖ ^ 2)) : ℝ) : ℂ) *
        Complex.exp ((inner ℝ ξ z : ℝ) * Complex.I) ∂μ).re := integral_re hci
  rw [← h3] at hre
  simp only [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at hre
  have hL : ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen d) h η) =
      ∫ θ, Ia a h (inner ℝ θ z) ∂(sphereMeasure μ) := hre.trans hpol
  exact ⟨hint, fun v => Ia_integrableOn a h v ha, hσi, hL, hL ▸ h0, hL ▸ h1⟩

/-- **`L:alpha-one-convolution`** (main TeX lines 5635-5707) under the manuscript's
hypotheses: `H:homog` (`HomogCovariance d 1 α₀ Γ μ`, so `d ∈ {1,2,3}`, `α = 1`; no
`Γ ≠ 0`, as in the TeX), `G_h` the wave Green measures `waveGreen d h`, `γ_ε = Γ * p_ε`,
`G_{h,η} = p_η * G_h`, and the two named inputs `SpectralPairing Γ μ` (the Fourier-Fubini
representation, wave L9-L) and `WaveGreenFourier d` (the Fourier identity of `G_h`,
lines 5614-5618; wave L9-G in `d = 2, 3`).  Conclusions: `V = μ{|ξ| ≤ 1} < ∞`, and for
`h > 0`, `ε > 0`, `η ≥ 0`, `z ∈ ℝ^d`, with `a = (ε+η)/2`: integrability of
`y ↦ γ_ε(y+z)` against `G_{h,η}`, absolute convergence of the radial integral defining
`I_a(h,v)`, `σ`-integrability of `θ ↦ I_a(h,θ·z)`, `E:alpha-one-polar`, and
`0 ≤ ∫ G_{h,η}(dy) γ_ε(y+z) ≤ πV/2` (`E:alpha-one-convolution`).  The homogeneity
`μ(cA) = cμ(A)` is derived from `H:homog` by
`MaskedSpectralGrowth.spectralHomogeneous_of_homog`. -/
theorem alpha_one_convolution_paper {alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d 1 alpha0 Γ μ) (hpair : SpectralPairing Γ μ)
    (hG : WaveGreenFourier d) :
    μ (closedBall 0 1) < ⊤ ∧
      ∀ h : ℝ, 0 < h → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 ≤ η → ∀ z : Rd d,
        Integrable (fun y => conv Γ (heatK ε) (y + z)) (smoothedGreen (waveGreen d) h η) ∧
        (∀ v : ℝ, IntegrableOn (fun r : ℝ => Real.exp (-((ε + η) / 2 * r ^ 2)) *
          (Real.sin (h * r) / r) * Real.cos (r * v)) (Ioi 0)) ∧
        Integrable (fun θ : Rd d => Ia ((ε + η) / 2) h (inner ℝ θ z)) (sphereMeasure μ) ∧
        ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen d) h η) =
          ∫ θ, Ia ((ε + η) / 2) h (inner ℝ θ z) ∂(sphereMeasure μ) ∧
        0 ≤ ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen d) h η) ∧
        ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen d) h η) ≤
          π * (μ (closedBall 0 1)).toReal / 2 := by
  have := hH.μ_radon
  exact alpha_one_convolution (MaskedSpectralGrowth.spectralHomogeneous_of_homog hH)
    hH.μ_tempered hpair hG

/-- **`L:alpha-one-convolution` in `d = 1`**: `alpha_one_convolution_paper` with the
Fourier identity discharged by `waveGreenFourier_one`; the only remaining named input is
`SpectralPairing Γ μ`. -/
theorem alpha_one_convolution_one {alpha0 : ℝ} {Γ μ : Measure (Rd 1)}
    (hH : HomogCovariance 1 1 alpha0 Γ μ) (hpair : SpectralPairing Γ μ) :
    μ (closedBall 0 1) < ⊤ ∧
      ∀ h : ℝ, 0 < h → ∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 ≤ η → ∀ z : Rd 1,
        Integrable (fun y => conv Γ (heatK ε) (y + z)) (smoothedGreen (waveGreen 1) h η) ∧
        (∀ v : ℝ, IntegrableOn (fun r : ℝ => Real.exp (-((ε + η) / 2 * r ^ 2)) *
          (Real.sin (h * r) / r) * Real.cos (r * v)) (Ioi 0)) ∧
        Integrable (fun θ : Rd 1 => Ia ((ε + η) / 2) h (inner ℝ θ z)) (sphereMeasure μ) ∧
        ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen 1) h η) =
          ∫ θ, Ia ((ε + η) / 2) h (inner ℝ θ z) ∂(sphereMeasure μ) ∧
        0 ≤ ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen 1) h η) ∧
        ∫ y, conv Γ (heatK ε) (y + z) ∂(smoothedGreen (waveGreen 1) h η) ≤
          π * (μ (closedBall 0 1)).toReal / 2 :=
  alpha_one_convolution_paper hH hpair waveGreenFourier_one

/-- The polar decomposition of the proof of `L:alpha-one-convolution` (main TeX lines
5653-5665) under `H:homog` with `α = 1`: the conclusions of `polar_decomposition`
together with the evenness of `σ` (from the evenness of `μ` in `H:homog`). -/
theorem alpha_one_polar_decomposition_paper {alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d 1 alpha0 Γ μ) :
    μ {0} = 0 ∧ μ (closedBall 0 1) < ⊤ ∧ sphereMeasure μ univ = μ (closedBall 0 1) ∧
      sphereMeasure μ (sphere 0 1)ᶜ = 0 ∧
      μ = ((sphereMeasure μ).prod (volume.restrict (Ioi (0 : ℝ)))).map polarMap ∧
      HomogHypothesis.IsEven (sphereMeasure μ) := by
  have := hH.μ_radon
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    polar_decomposition (MaskedSpectralGrowth.spectralHomogeneous_of_homog hH)
  exact ⟨h1, h2, h3, h4, h5, sphereMeasure_even hH.μ_even⟩

end StratonovichHAMSecondMoment.AlphaOneConvolution
