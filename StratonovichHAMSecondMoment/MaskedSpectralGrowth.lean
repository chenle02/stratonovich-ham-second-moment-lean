module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`P:masked-spectral-growth` (Translated spectral mass) of
`notes/integrated_covariance_foundation.tex` (revision a284420, lines 34-77),
and the derivation of the spectral homogeneity `μ(cA) = c^α μ(A)` from the
scaling of `Γ` (main TeX file `notes/notes_stratonovich_ham_second_moment.tex`,
lines 851-852, proof of `L:damped-homogeneous-norms`), which discharges the one
supplied input of `SpectralHomog`, `DampedNorms` and `ClockCopy` (see
`ClockCopyHomog`).

Formalized:
* `masked_spectral_growth_paper`, under the section's standing assumptions
  (lines 5-6): `H:homog` (`HomogHypothesis.HomogCovariance`) and `Γ ≠ 0`.
  With `M_Γ = ∫ e^{-|x|²/4} Γ(dx)` (`MGamma`) and `C_Γ = e M_Γ/(2√π)^d`
  (`CGamma`): `e^{-|x|²/4}` is `Γ`-integrable (the manuscript's `M_Γ < ∞`)
  and `M_Γ > 0`; for every `y ∈ ℝ^d` and `r > 0` both integrands of
  `E:masked-gaussian-transform` are integrable and the transform holds;
  `0 ≤ ∫ e^{-|ξ-y|²/r²} μ(dξ) ≤ r^α M_Γ/(2√π)^d`; and
  `μ(B(y,r)) ≤ C_Γ r^α` for the open and for the closed ball
  (`E:masked-translated-ball`).  The general form `masked_spectral_growth`
  assumes only: `Γ` and `μ` tempered, the spectral convention
  (`HomogHypothesis.IsSpectralMeasure`), the scaling `Γ(cA) = c^{d-α}Γ(A)`
  (written `SpectralHomog.SpectralHomogeneous Γ (d - α)`, which is literally
  the `scaling` field of `H:homog`) and `Γ ≠ 0` (used only for `M_Γ > 0`).
  The transform `masked_gaussian_transform` needs only the spectral
  convention, the Gaussian bound `translated_gauss_le` only the convention and
  the scaling.
* `spectralHomogeneous_of_homog`: under `H:homog`,
  `SpectralHomog.SpectralHomogeneous μ α`.  General form
  `spectralHomogeneous_of_scaling` (`μ` tempered, the spectral convention, the
  scaling of `Γ`; no range condition on `α`); pushforward form
  `map_smul_of_scaling`.

Hypotheses of `H:homog` used by the wrappers: `Γ_tempered`, `μ_tempered`,
`spectral`, `scaling` (and `Γ ≠ 0`); the other fields are carried, unused.

Supplied inputs: none.  The Gaussian Schwartz test is built in
`GaussianTest` (no Schwartz-membership input; the fallback of the wave plan
was not needed).

Implicit hypotheses made explicit: the manuscript's `M_Γ < ∞` is the
integrability of `e^{-|x|²/4}` against `Γ`, and each integral of the
proposition comes with an integrability conclusion, since a Lean Bochner
integral of a non-integrable function is `0`.  The balls are
`Metric.ball y r` and `Metric.closedBall y r`.

Proof route.  As in the TeX for the proposition, except that the Gaussian
Fourier integral (lines 56-64, computed there via `J'(b) = -bJ(b)/(2A)`) is
Mathlib's `GaussianFourier.integral_cexp_neg_mul_sq_norm_add`, and the
integrability of the Gaussian against a tempered measure is proved directly
from the package's integral form of temperedness (`IsTempered`:
`∫(1+|x|)^{-k} < ∞`), not from the polynomial mass growth argument of lines
23-30.  For the homogeneity the manuscript only says "Fourier uniqueness"; the
Lean route weights both `μ ∘ (c·)⁻¹` and `c^{-α} μ` by `e^{-|ξ|²}` (finite
measures because `μ` is tempered), shows that their characteristic functions
agree (each is a translated Gaussian integral against `Γ`, by the spectral
convention applied to the test `e^{-s|x-t|²}`, and the two are related by the
scaling of `Γ`), concludes with `Measure.ext_of_charFun`, and removes the
weight with `withDensity_inv_same`.  Lemmas marked "Auxiliary to the Lean
proof route" have no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.TimeFractional
public import StratonovichHAMSecondMoment.GaussianTest

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Real Metric
open scoped ENNReal NNReal Pointwise

namespace StratonovichHAMSecondMoment.MaskedSpectralGrowth

open HomogHypothesis SpectralHomog GaussianTest

variable {d : ℕ}

/-! ### Integrability of Gaussians against tempered measures -/

/-- Auxiliary to the Lean proof route. A tempered measure integrates every
translated Gaussian `e^{-b‖x-w‖²}`, `b > 0` (the Schwartz integrability noted
at lines 23-30, for this test). -/
theorem integrable_gauss_of_tempered {ν : Measure (Rd d)} (hν : IsTempered ν) {b : ℝ}
    (hb : 0 < b) (w : Rd d) : Integrable (fun x : Rd d => Real.exp (-(b * ‖x - w‖ ^ 2))) ν := by
  obtain ⟨k, hk⟩ := hν
  have hg : Integrable (fun x : Rd d => (1 + ‖x‖) ^ (-(k : ℝ))) ν := by
    refine ⟨(by fun_prop : Measurable fun x : Rd d => (1 + ‖x‖) ^ (-(k : ℝ))).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => ?_)).2 hk⟩
    exact Real.rpow_nonneg (by positivity) _
  set K := (1 + ‖w‖) ^ k * Real.exp ((k : ℝ) ^ 2 / (4 * b))
  refine Integrable.mono' (hg.const_mul K)
    (by fun_prop : Measurable fun x : Rd d => Real.exp (-(b * ‖x - w‖ ^ 2))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hp : 0 < (1 + ‖x‖) ^ k := by positivity
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.rpow_neg (by positivity), Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ hp]
  have h1 : 1 + ‖x‖ ≤ (1 + ‖w‖) * (1 + ‖x - w‖) := by
    have : ‖x‖ ≤ ‖x - w‖ + ‖w‖ := by
      calc ‖x‖ = ‖(x - w) + w‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - w‖ + ‖w‖ := norm_add_le _ _
    nlinarith [norm_nonneg w, norm_nonneg (x - w)]
  have h2 : (1 + ‖x‖) ^ k ≤ (1 + ‖w‖) ^ k * (1 + ‖x - w‖) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 k
  have h3 := poly_mul_exp_neg_sq_le k hb (norm_nonneg (x - w))
  calc Real.exp (-(b * ‖x - w‖ ^ 2)) * (1 + ‖x‖) ^ k
      ≤ Real.exp (-(b * ‖x - w‖ ^ 2)) * ((1 + ‖w‖) ^ k * (1 + ‖x - w‖) ^ k) :=
        mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = (1 + ‖w‖) ^ k * ((1 + ‖x - w‖) ^ k * Real.exp (-(b * ‖x - w‖ ^ 2))) := by ring
    _ ≤ K := mul_le_mul_of_nonneg_left h3 (by positivity)

/-! ### The spectral convention applied to Gaussian tests -/

/-- `E:masked-spectral-convention` (lines 15-19) applied to the Schwartz test
`e^{-i⟨y,x⟩} e^{-s‖x-w‖²}`, with the inner Gaussian Fourier integral computed:
`∫ test dΓ = ∫ (π/s)^{d/2} e^{i⟨ξ-y,w⟩} e^{-‖ξ-y‖²/(4s)} μ(dξ)`. Only the
spectral convention is assumed. -/
theorem spectral_gaussTest {Γ μ : Measure (Rd d)} (hsp : IsSpectralMeasure Γ μ) (s : ℝ)
    (hs : 0 < s) (w y : Rd d) :
    ∫ x, gaussTest s hs w y x ∂Γ =
      ∫ ξ, ((Real.pi / s) ^ ((d : ℝ) / 2) : ℝ) *
        Complex.exp (Complex.I * (inner ℝ (ξ - y) w : ℝ)) *
          (Real.exp (-(‖ξ - y‖ ^ 2 / (4 * s))) : ℂ) ∂μ := by
  rw [hsp]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => gaussTest_fourier s hs w y ξ)

/-- Auxiliary to the Lean proof route. The case `y = 0`: the translated
Gaussian `e^{-s‖x-t‖²}` against `Γ` is `(π/s)^{d/2}` times the transform
`∫ e^{i⟨ξ,t⟩} e^{-‖ξ‖²/(4s)} μ(dξ)`. -/
theorem spectral_translated_gauss {Γ μ : Measure (Rd d)} (hsp : IsSpectralMeasure Γ μ) (s : ℝ)
    (hs : 0 < s) (t : Rd d) :
    ∫ x, (Real.exp (-(s * ‖x - t‖ ^ 2)) : ℂ) ∂Γ =
      ((Real.pi / s) ^ ((d : ℝ) / 2) : ℝ) *
        ∫ ξ, Complex.exp (Complex.I * (inner ℝ ξ t : ℝ)) *
          (Real.exp (-(‖ξ‖ ^ 2 / (4 * s))) : ℂ) ∂μ := by
  have h := spectral_gaussTest hsp s hs t 0
  simp only [gaussTest_apply, inner_zero_left, Complex.ofReal_zero, mul_zero, neg_zero,
    Complex.exp_zero, one_mul, sub_zero] at h
  rw [h, ← integral_const_mul]
  congr 1
  funext ξ
  ring

/-- Auxiliary to the Lean proof route. `(a²)^{d/2} = a^d` for `a ≥ 0`. -/
theorem sq_rpow_half (a : ℝ) (ha : 0 ≤ a) (d : ℕ) : (a ^ 2) ^ ((d : ℝ) / 2) = a ^ d := by
  rw [← Real.rpow_natCast a 2, ← Real.rpow_mul ha, ← Real.rpow_natCast a d]
  congr 1
  push_cast
  ring

/-! ### Spectral homogeneity from the scaling of `Γ` -/

/-- Auxiliary to the Lean proof route. The Gaussian density `e^{-‖ξ‖²}` as an
`ℝ≥0`-valued function. -/
def gdens (ξ : Rd d) : ℝ≥0 := Real.toNNReal (Real.exp (-‖ξ‖ ^ 2))

/-- Auxiliary to the Lean proof route. -/
theorem measurable_gdens : Measurable (gdens (d := d)) :=
  (by fun_prop : Measurable fun ξ : Rd d => Real.exp (-‖ξ‖ ^ 2)).real_toNNReal

/-- Auxiliary to the Lean proof route. -/
theorem coe_gdens (ξ : Rd d) : (gdens ξ : ℝ) = Real.exp (-‖ξ‖ ^ 2) :=
  Real.coe_toNNReal _ (Real.exp_pos _).le

/-- Auxiliary to the Lean proof route. The characteristic function of the
finite measure `e^{-‖ξ‖²} (μ ∘ (c·)⁻¹)(dξ)`. -/
theorem charFun_map_withDensity (μ : Measure (Rd d)) (c : ℝ) (t : Rd d) :
    charFun ((μ.map (fun ξ => c • ξ)).withDensity (fun ξ => (gdens ξ : ℝ≥0∞))) t =
      ∫ ξ, Complex.exp (Complex.I * (inner ℝ ξ (c • t) : ℝ)) *
        (Real.exp (-((c ^ 2) * ‖ξ‖ ^ 2)) : ℂ) ∂μ := by
  rw [charFun_apply, integral_withDensity_eq_integral_smul measurable_gdens,
    integral_map (measurable_const_smul c).aemeasurable
      (f := fun x : Rd d => gdens x • Complex.exp ((inner ℝ x t : ℝ) * Complex.I))
      (measurable_gdens.smul (by fun_prop)).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [NNReal.smul_def, coe_gdens, Complex.real_smul, real_inner_smul_left,
    real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_comm]
  congr 2
  push_cast; ring

/-- Auxiliary to the Lean proof route. The characteristic function of
`e^{-‖ξ‖²} (k • μ)(dξ)`. -/
theorem charFun_smul_withDensity (μ : Measure (Rd d)) (k : ℝ≥0∞) (t : Rd d) :
    charFun ((k • μ).withDensity (fun ξ => (gdens ξ : ℝ≥0∞))) t =
      (k.toReal : ℂ) * ∫ ξ, Complex.exp (Complex.I * (inner ℝ ξ t : ℝ)) *
        (Real.exp (-(1 ^ 2 * ‖ξ‖ ^ 2)) : ℂ) ∂μ := by
  rw [charFun_apply, integral_withDensity_eq_integral_smul measurable_gdens,
    integral_smul_measure, Complex.real_smul]
  congr 1
  congr 1
  funext ξ
  rw [NNReal.smul_def, coe_gdens, Complex.real_smul, one_pow, one_mul, mul_comm, mul_comm (_ : ℂ) Complex.I]

/-- Auxiliary to the Lean proof route. Real constants of the scaling argument:
`(c⁻¹)^{-(d-α)} (4π)^{d/2} = c^{-α} (4πc²)^{d/2}`. -/
theorem scaling_constants (alpha c : ℝ) (hc : 0 < c) :
    (c⁻¹) ^ (-((d : ℝ) - alpha)) * (Real.pi / (1 / 4)) ^ ((d : ℝ) / 2) =
      c ^ (-alpha) * (Real.pi / (1 / (4 * c ^ 2))) ^ ((d : ℝ) / 2) := by
  have hs := Real.sqrt_nonneg Real.pi
  have hpi := Real.sq_sqrt Real.pi_pos.le
  have h1 : Real.pi / (1 / (4 * c ^ 2)) = (2 * Real.sqrt Real.pi * c) ^ 2 := by
    rw [mul_pow, mul_pow, hpi]; field_simp; norm_num
  have h0 : Real.pi / (1 / 4) = (2 * Real.sqrt Real.pi) ^ 2 := by
    rw [mul_pow, hpi]; field_simp; norm_num
  have hq : (c⁻¹) ^ (-((d : ℝ) - alpha)) = c ^ (-alpha) * c ^ d := by
    rw [Real.inv_rpow hc.le, Real.rpow_neg hc.le, inv_inv, ← Real.rpow_natCast,
      ← Real.rpow_add hc]
    congr 1; ring
  rw [h1, h0, sq_rpow_half _ (by positivity), sq_rpow_half _ (by positivity), hq, mul_pow]
  ring

/-- The pushforward form of the spectral homogeneity, derived (not supplied):
if `μ` is tempered and is the spectral measure of `Γ` in the sense of
`E:masked-spectral-convention`, and `Γ(cA) = c^{d-α} Γ(A)` (the scaling clause
of `H:homog`), then `μ ∘ (c·)⁻¹ = c^{-α} μ` for `c > 0`.  This is the step
"Scaling the Fourier representation of `Γ` and using Fourier uniqueness gives
`μ(cA) = c^α μ(A)`" (main TeX lines 851-852).  Route: both sides weighted by
`e^{-‖ξ‖²}` are finite measures with equal characteristic functions (each is a
translated Gaussian integral against `Γ`, compared through the scaling of
`Γ`); `Measure.ext_of_charFun` identifies them and the weight is removed. -/
theorem map_smul_of_scaling {Γ μ : Measure (Rd d)} {alpha : ℝ} (hμt : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha)) (c : ℝ)
    (hc : 0 < c) :
    μ.map (fun ξ => c • ξ) = ENNReal.ofReal (c ^ (-alpha)) • μ := by
  set G : Rd d → ℝ≥0∞ := fun ξ => (gdens ξ : ℝ≥0∞) with hG
  have hGm : Measurable G := measurable_gdens.coe_nnreal_ennreal
  set k := ENNReal.ofReal (c ^ (-alpha)) with hk
  have hfin0 : ∫⁻ ξ, G ξ ∂μ < ⊤ := by
    have h := (integrable_gauss_of_tempered hμt (b := 1) one_pos 0).lintegral_lt_top
    convert h using 3 with ξ
    simp [hG, gdens, ENNReal.ofReal]
  have : IsFiniteMeasure ((μ.map (fun ξ => c • ξ)).withDensity G) := by
    refine isFiniteMeasure_withDensity ?_
    rw [lintegral_map hGm (measurable_const_smul c)]
    have h := (integrable_gauss_of_tempered hμt (b := c ^ 2) (by positivity) 0).lintegral_lt_top
    refine ne_of_lt ?_
    convert h using 3 with ξ
    simp only [hG, gdens, sub_zero, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rfl
  have : IsFiniteMeasure ((k • μ).withDensity G) := by
    refine isFiniteMeasure_withDensity ?_
    rw [lintegral_smul_measure]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin0.ne
  have h12 : (μ.map (fun ξ => c • ξ)).withDensity G = (k • μ).withDensity G := by
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [charFun_map_withDensity, charFun_smul_withDensity, hk,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hc.le _)]
    have e1 := spectral_translated_gauss hsp (1 / (4 * c ^ 2)) (by positivity) (c • t)
    have e0 := spectral_translated_gauss hsp (1 / 4) (by norm_num) t
    have hx1 : ∀ ξ : Rd d, ‖ξ‖ ^ 2 / (4 * (1 / (4 * c ^ 2))) = c ^ 2 * ‖ξ‖ ^ 2 := by
      intro ξ; field_simp
    have hx0 : ∀ ξ : Rd d, ‖ξ‖ ^ 2 / (4 * (1 / 4)) = 1 ^ 2 * ‖ξ‖ ^ 2 := by
      intro ξ; ring
    simp only [hx1] at e1
    simp only [hx0] at e0
    have escale : ∫ x, (Real.exp (-(1 / (4 * c ^ 2) * ‖x - c • t‖ ^ 2)) : ℂ) ∂Γ =
        (((c⁻¹) ^ (-((d : ℝ) - alpha)) : ℝ) : ℂ) *
          ∫ x, (Real.exp (-(1 / 4 * ‖x - t‖ ^ 2)) : ℂ) ∂Γ := by
      rw [integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_mul,
        ← integral_comp_smul hΓs c⁻¹ (inv_pos.2 hc)
          (fun u => Real.exp (-(1 / 4 * ‖u - t‖ ^ 2))) (by fun_prop)]
      congr 2
      funext x
      have hv : c⁻¹ • x - t = c⁻¹ • (x - c • t) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      rw [hv, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc, mul_pow]
      congr 2
      field_simp
    have hC := congrArg (fun r : ℝ => (r : ℂ)) (scaling_constants (d := d) alpha c hc)
    simp only [Complex.ofReal_mul] at hC
    have hP1 : (((Real.pi / (1 / (4 * c ^ 2))) ^ ((d : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
      have : 0 < (Real.pi / (1 / (4 * c ^ 2))) ^ ((d : ℝ) / 2) :=
        Real.rpow_pos_of_pos (by positivity) _
      exact_mod_cast this.ne'
    refine mul_left_cancel₀ hP1 ?_
    rw [← e1, escale, e0]
    linear_combination (∫ ξ, Complex.exp (Complex.I * (inner ℝ ξ t : ℝ)) *
        (Real.exp (-(1 ^ 2 * ‖ξ‖ ^ 2)) : ℂ) ∂μ) * hC
  have hne0 : ∀ ξ, G ξ ≠ 0 := fun ξ =>
    ENNReal.coe_ne_zero.2 (Real.toNNReal_pos.2 (Real.exp_pos _)).ne'
  have hnetop : ∀ ξ, G ξ ≠ ⊤ := fun ξ => ENNReal.coe_ne_top
  rw [← withDensity_inv_same hGm (μ := μ.map (fun ξ => c • ξ))
      (Filter.Eventually.of_forall hne0) (Filter.Eventually.of_forall hnetop),
    h12, withDensity_inv_same hGm (Filter.Eventually.of_forall hne0)
      (Filter.Eventually.of_forall hnetop)]

/-- **Discharge of the supplied input of `SpectralHomog`.** Under the
tempered spectral convention and the scaling `Γ(cA) = c^{d-α} Γ(A)`,
`μ(cA) = c^α μ(A)` for Borel `A` and `c > 0` (main TeX lines 851-852; the
same derivation is used at lines 4718-4722).  Hypotheses: `μ` tempered,
`IsSpectralMeasure Γ μ`, and the scaling of `Γ`. -/
theorem spectralHomogeneous_of_scaling {Γ μ : Measure (Rd d)} {alpha : ℝ}
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ)
    (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha)) : SpectralHomogeneous μ alpha := by
  intro A hA c hc
  have hm := congrArg (fun ν : Measure (Rd d) => ν A)
    (map_smul_of_scaling hμt hsp hΓs c⁻¹ (inv_pos.2 hc))
  rw [Measure.map_apply (measurable_const_smul _) hA, Set.preimage_smul₀ (inv_ne_zero hc.ne'),
    inv_inv, Measure.smul_apply, smul_eq_mul, Real.inv_rpow hc.le, Real.rpow_neg hc.le,
      inv_inv] at hm
  exact hm

/-- The discharge under `H:homog`: the spectral measure of a covariance
satisfying `HomogHypothesis.HomogCovariance` is `α`-homogeneous.  Uses the
fields `μ_tempered`, `spectral` and `scaling` only. -/
theorem spectralHomogeneous_of_homog {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) : SpectralHomogeneous μ alpha :=
  spectralHomogeneous_of_scaling h.μ_tempered h.spectral h.scaling

/-! ### `P:masked-spectral-growth` -/

/-- `M_Γ = ∫ e^{-|x|²/4} Γ(dx)` (line 37). -/
def MGamma (Γ : Measure (Rd d)) : ℝ := ∫ x, Real.exp (-(‖x‖ ^ 2 / 4)) ∂Γ

/-- `C_Γ = e M_Γ/(2√π)^d` (line 38). -/
def CGamma (Γ : Measure (Rd d)) : ℝ := Real.exp 1 * MGamma Γ / (2 * Real.sqrt Real.pi) ^ d

/-- Auxiliary to the Lean proof route. Integrability of the centred Gaussian
`e^{-c‖x‖²}` (`c > 0`) against a tempered measure. -/
theorem integrable_gauss_zero {ν : Measure (Rd d)} (hν : IsTempered ν) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Rd d => Real.exp (-(c * ‖x‖ ^ 2))) ν := by
  simpa using integrable_gauss_of_tempered hν hc 0

/-- `0 < M_Γ < ∞` (line 40): `e^{-|x|²/4}` is `Γ`-integrable for a tempered
`Γ`, and `M_Γ > 0` when moreover `Γ ≠ 0`. -/
theorem MGamma_pos {Γ : Measure (Rd d)} (hΓt : IsTempered Γ) (hΓ : Γ ≠ 0) :
    Integrable (fun x : Rd d => Real.exp (-(‖x‖ ^ 2 / 4))) Γ ∧ 0 < MGamma Γ := by
  have hi : Integrable (fun x : Rd d => Real.exp (-(‖x‖ ^ 2 / 4))) Γ := by
    have h := integrable_gauss_zero hΓt (c := 1 / 4) (by norm_num)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring_nf
  exact ⟨hi, TimeFractional.integral_pos_of_ae_pos hi hΓ
    (Filter.Eventually.of_forall fun _ => Real.exp_pos _)⟩

/-- Auxiliary to the Lean proof route. `(π/(r²/4))^{d/2} (r/(2√π))^d = 1`. -/
theorem gauss_const_cancel (r : ℝ) (hr : 0 < r) :
    (Real.pi / (r ^ 2 / 4)) ^ ((d : ℝ) / 2) * (r / (2 * Real.sqrt Real.pi)) ^ d = 1 := by
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hpi := Real.sq_sqrt Real.pi_pos.le
  have h1 : Real.pi / (r ^ 2 / 4) = (2 * Real.sqrt Real.pi / r) ^ 2 := by
    rw [div_pow, mul_pow, hpi]; field_simp; norm_num
  rw [h1, sq_rpow_half _ (by positivity), ← mul_pow]
  rw [show 2 * Real.sqrt Real.pi / r * (r / (2 * Real.sqrt Real.pi)) = 1 by field_simp, one_pow]

/-- `E:masked-gaussian-transform` (lines 42-45): for `y ∈ ℝ^d`, `r > 0`,
`∫ e^{-|ξ-y|²/r²} μ(dξ) = (r/(2√π))^d ∫ e^{-r²|x|²/4} e^{-iy·x} Γ(dx)`.
Only the spectral convention is assumed (as an identity of Lean integrals;
integrability of both integrands is `masked_spectral_growth`). -/
theorem masked_gaussian_transform {Γ μ : Measure (Rd d)} (hsp : IsSpectralMeasure Γ μ)
    (y : Rd d) (r : ℝ) (hr : 0 < r) :
    ((∫ ξ, Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2)) ∂μ : ℝ) : ℂ) =
      (((r / (2 * Real.sqrt Real.pi)) ^ d : ℝ) : ℂ) *
        ∫ x, (Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ y x : ℝ))) ∂Γ := by
  have h := spectral_gaussTest hsp (r ^ 2 / 4) (by positivity) 0 y
  simp only [gaussTest_apply, inner_zero_right, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, mul_one, sub_zero] at h
  have hx : ∀ ξ : Rd d, ‖ξ - y‖ ^ 2 / (4 * (r ^ 2 / 4)) = ‖ξ - y‖ ^ 2 / r ^ 2 := by
    intro ξ; field_simp
  simp only [hx] at h
  rw [integral_const_mul, integral_complex_ofReal] at h
  have hΓint : ∫ x, (Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ y x : ℝ))) ∂Γ =
      ∫ x, Complex.exp (-(Complex.I * (inner ℝ y x : ℝ))) *
        (Real.exp (-(r ^ 2 / 4 * ‖x‖ ^ 2)) : ℂ) ∂Γ := by
    congr 1; funext x; rw [mul_comm]; congr 3; ring
  rw [hΓint, h, ← mul_assoc, ← Complex.ofReal_mul,
    mul_comm ((r / (2 * Real.sqrt Real.pi)) ^ d), gauss_const_cancel (d := d) r hr,
    Complex.ofReal_one, one_mul]

/-- `E:masked-translated-ball`, Gaussian part (lines 46-47):
`∫ e^{-|ξ-y|²/r²} μ(dξ) ≤ r^α M_Γ/(2√π)^d`, from the transform, the
nonnegativity of `Γ` and the scaling `Γ(cA) = c^{d-α}Γ(A)`. -/
theorem translated_gauss_le {Γ μ : Measure (Rd d)} {alpha : ℝ} (hsp : IsSpectralMeasure Γ μ)
    (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha)) (y : Rd d) (r : ℝ) (hr : 0 < r) :
    ∫ ξ, Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2)) ∂μ ≤
      r ^ alpha * MGamma Γ / (2 * Real.sqrt Real.pi) ^ d := by
  have hs : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hT := masked_gaussian_transform hsp y r hr
  have hL : 0 ≤ ∫ ξ, Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2)) ∂μ :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hnorm := congrArg norm hT
  rw [Complex.norm_real, Real.norm_of_nonneg hL, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)] at hnorm
  rw [hnorm]
  have hle := norm_integral_le_integral_norm (μ := Γ) (fun x : Rd d =>
    (Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) * Complex.exp (-(Complex.I * (inner ℝ y x : ℝ))))
  have hpt : ∀ x : Rd d, ‖(Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ y x : ℝ)))‖ = Real.exp (-(‖r • x‖ ^ 2 / 4)) := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, neg_zero, Real.exp_zero, mul_one]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    congr 2; ring
  simp only [hpt] at hle
  rw [integral_comp_smul hΓs r hr (fun u => Real.exp (-(‖u‖ ^ 2 / 4))) (by fun_prop)] at hle
  calc (r / (2 * Real.sqrt Real.pi)) ^ d * ‖∫ x, (Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) *
        Complex.exp (-(Complex.I * (inner ℝ y x : ℝ))) ∂Γ‖
      ≤ (r / (2 * Real.sqrt Real.pi)) ^ d * (r ^ (-((d : ℝ) - alpha)) * MGamma Γ) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = r ^ alpha * MGamma Γ / (2 * Real.sqrt Real.pi) ^ d := by
        have hrr : r ^ d * r ^ (-((d : ℝ) - alpha)) = r ^ alpha := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hr]; congr 1; ring
        rw [div_pow, ← hrr]
        field_simp

/-- `E:masked-translated-ball`, mass part (line 48): `μ(B̄(y,r)) ≤ C_Γ r^α`
for the closed ball, given the integrability of `e^{-|ξ-y|²/r²}` (which holds
for tempered `μ`). -/
theorem closedBall_le {Γ μ : Measure (Rd d)} {alpha : ℝ} (hsp : IsSpectralMeasure Γ μ)
    (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha)) (y : Rd d) (r : ℝ) (hr : 0 < r)
    (hint : Integrable (fun ξ : Rd d => Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2))) μ) :
    μ (closedBall y r) ≤ ENNReal.ofReal (CGamma Γ * r ^ alpha) := by
  set f := fun ξ : Rd d => Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2)) with hf
  have hb := translated_gauss_le hsp hΓs y r hr
  have hmark : ENNReal.ofReal (Real.exp (-1)) * μ (closedBall y r) ≤
      ENNReal.ofReal (∫ ξ, f ξ ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le),
      ← setLIntegral_const]
    refine (setLIntegral_mono (by fun_prop) fun ξ hξ => ?_).trans
      (setLIntegral_le_lintegral _ _)
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    rw [mem_closedBall, dist_eq_norm] at hξ
    have h1 : ‖ξ - y‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hξ 2
    have h2 : ‖ξ - y‖ ^ 2 / r ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact h1
    linarith
  have he : ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (Real.exp (-1)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; simp
  calc μ (closedBall y r)
      = ENNReal.ofReal (Real.exp 1) * (ENNReal.ofReal (Real.exp (-1)) * μ (closedBall y r)) := by
        rw [← mul_assoc, he, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (∫ ξ, f ξ ∂μ) := by gcongr
    _ ≤ ENNReal.ofReal (Real.exp 1) *
          ENNReal.ofReal (r ^ alpha * MGamma Γ / (2 * Real.sqrt Real.pi) ^ d) := by
        gcongr
    _ = ENNReal.ofReal (CGamma Γ * r ^ alpha) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, CGamma]
        congr 1; ring

/-- **`P:masked-spectral-growth`** (lines 34-52), general form: for a tempered
`Γ ≠ 0` with tempered spectral measure `μ` (`E:masked-spectral-convention`)
and the scaling `Γ(cA) = c^{d-α}Γ(A)`:
`e^{-|x|²/4}` is `Γ`-integrable and `M_Γ > 0`; for every `y` and `r > 0` the
integrands of `E:masked-gaussian-transform` are integrable, the transform
holds, `0 ≤ ∫ e^{-|ξ-y|²/r²}dμ ≤ r^α M_Γ/(2√π)^d`, and `μ(B(y,r)) ≤ C_Γ r^α`
for the open and the closed ball. -/
theorem masked_spectral_growth {Γ μ : Measure (Rd d)} {alpha : ℝ} (hΓt : IsTempered Γ)
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ)
    (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha)) (hΓ : Γ ≠ 0) :
    Integrable (fun x : Rd d => Real.exp (-(‖x‖ ^ 2 / 4))) Γ ∧ 0 < MGamma Γ ∧
      ∀ y : Rd d, ∀ r : ℝ, 0 < r →
        Integrable (fun ξ : Rd d => Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2))) μ ∧
        Integrable (fun x : Rd d => (Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ y x : ℝ)))) Γ ∧
        ((∫ ξ, Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2)) ∂μ : ℝ) : ℂ) =
          (((r / (2 * Real.sqrt Real.pi)) ^ d : ℝ) : ℂ) *
            ∫ x, (Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) *
              Complex.exp (-(Complex.I * (inner ℝ y x : ℝ))) ∂Γ ∧
        0 ≤ ∫ ξ, Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2)) ∂μ ∧
        ∫ ξ, Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2)) ∂μ ≤
          r ^ alpha * MGamma Γ / (2 * Real.sqrt Real.pi) ^ d ∧
        μ (ball y r) ≤ ENNReal.ofReal (CGamma Γ * r ^ alpha) ∧
        μ (closedBall y r) ≤ ENNReal.ofReal (CGamma Γ * r ^ alpha) := by
  obtain ⟨hM1, hM2⟩ := MGamma_pos hΓt hΓ
  refine ⟨hM1, hM2, fun y r hr => ?_⟩
  have hiμ : Integrable (fun ξ : Rd d => Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2))) μ := by
    refine (integrable_gauss_of_tempered hμt (b := 1 / r ^ 2) (by positivity) y).congr
      (Filter.Eventually.of_forall fun ξ => ?_)
    simp only; congr 1; field_simp
  have hiΓ : Integrable (fun x : Rd d => (Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ y x : ℝ)))) Γ := by
    have hg := integrable_gauss_zero hΓt (c := r ^ 2 / 4) (by positivity)
    refine hg.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Complex.norm_exp]
    simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, neg_zero, Real.exp_zero, mul_one]
    exact le_of_eq (by congr 2; ring)
  have hcb := closedBall_le hsp hΓs y r hr hiμ
  exact ⟨hiμ, hiΓ, masked_gaussian_transform hsp y r hr,
    integral_nonneg fun _ => (Real.exp_pos _).le, translated_gauss_le hsp hΓs y r hr,
    (measure_mono ball_subset_closedBall).trans hcb, hcb⟩

/-- **`P:masked-spectral-growth` with the manuscript's hypotheses**: the
section's standing assumptions `H:homog` (`HomogCovariance`) and `Γ ≠ 0`
(lines 5-6).  Uses the fields `Γ_tempered`, `μ_tempered`, `spectral` and
`scaling`. -/
theorem masked_spectral_growth_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (hΓ : Γ ≠ 0) :
    Integrable (fun x : Rd d => Real.exp (-(‖x‖ ^ 2 / 4))) Γ ∧ 0 < MGamma Γ ∧
      ∀ y : Rd d, ∀ r : ℝ, 0 < r →
        Integrable (fun ξ : Rd d => Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2))) μ ∧
        Integrable (fun x : Rd d => (Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ y x : ℝ)))) Γ ∧
        ((∫ ξ, Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2)) ∂μ : ℝ) : ℂ) =
          (((r / (2 * Real.sqrt Real.pi)) ^ d : ℝ) : ℂ) *
            ∫ x, (Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) *
              Complex.exp (-(Complex.I * (inner ℝ y x : ℝ))) ∂Γ ∧
        0 ≤ ∫ ξ, Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2)) ∂μ ∧
        ∫ ξ, Real.exp (-(‖ξ - y‖ ^ 2 / r ^ 2)) ∂μ ≤
          r ^ alpha * MGamma Γ / (2 * Real.sqrt Real.pi) ^ d ∧
        μ (ball y r) ≤ ENNReal.ofReal (CGamma Γ * r ^ alpha) ∧
        μ (closedBall y r) ≤ ENNReal.ofReal (CGamma Γ * r ^ alpha) :=
  masked_spectral_growth h.Γ_tempered h.μ_tempered h.spectral h.scaling hΓ

end StratonovichHAMSecondMoment.MaskedSpectralGrowth
