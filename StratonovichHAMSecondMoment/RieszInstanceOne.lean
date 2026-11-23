module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L20, item R (approved by Le on 2026-11-22, decision 6): the one-dimensional Riesz covariance
of `E:d1-covariances` is an instance of `H:homog`.  TeX lines at revision edf7085f (book 1.1.3),
main file `notes/notes_stratonovich_ham_second_moment.tex`:
* `H:homog`, lines 384-401: `Γ` a nonnegative, even, positive-definite tempered Radon measure on
  `ℝ^d` with positive even tempered Radon spectral measure `μ`, `Γ = ∫ e^{iξ·x} μ(dξ)` in the
  sense of tempered distributions, `Γ(cA) = c^{d-α} Γ(A)`, `α₀ + α < 2`, `0 < α < d` or
  `α = d = 1`, with `d ∈ {1,2,3}` and `0 < α₀ < 1`;
* `E:d1-covariances`, lines 5317-5322 (with "Throughout this section `0 < α₀ < 1`", 5315): the
  Riesz case `γ(y) = c_α |y|^{-α}`, `0 < α < 1`, `c_α > 0`.

Result: `riesz_homogCovariance_one`: for `0 < α₀ < 1`, `c > 0` and `0 < α < 1`,
`∃ μ, HomogCovariance 1 α α₀ (volume.withDensity (riesz c α)) μ`, with the explicit witness
`rieszSpectral c α` (`riesz_homogCovariance_one_spectral`).  The statement has exactly the
hypotheses of TeX 5315-5322 for the Riesz case; nothing is supplied.  (The auxiliary lemmas
need only `c ≥ 0`; the two instance theorems carry the TeX's `c_α > 0`.)

The spectral measure.  `μ = h(ξ) dξ` with the Gaussian-mixture density
`h(ξ) = c Γ(α/2)^{-1} ∫_0^∞ s^{α/2-1} (4πs)^{-1/2} e^{-|ξ|²/(4s)} ds` (`spectralDensity`;
`h(ξ)` is a constant multiple of `|ξ|^{α-1}`, which is neither computed nor used).

**Route (the TeX states the instance without proof; disclosed).**
* `Γ`: tempered from the integrability of `|x|^{-α}(1+|x|)^{-2}` on `ℝ` (`0 ≤ α < 1`); locally
  finite, even and `Γ(rA) = r^{1-α}Γ(A)` by the generic density lemmas of `EndpointLemmas`;
  positive definite by `RieszPositiveDefinite.posdef_of_mixture` (Gaussian subordination
  without Fourier transforms) with a d = 1 copy of `riesz_mixture` (`riesz_mixture_one`).
* `μ`: tempered by Tonelli: the Gaussian `g_s` has mass one and supremum `(4πs)^{-1/2}`, and
  `∫_0^1 s^{α/2-1} ds + ∫_1^∞ s^{α/2-3/2} ds < ∞` (here `α < 1` is used); hence locally finite
  (`EndpointLemmas.isLocallyFiniteMeasure_of_tempered`); even since `h` is radial.
* The spectral identity `∫ φ dΓ = ∫ (∫ φ(x) e^{iξx} dx) μ(dξ)` (`isSpectralMeasure_riesz`): the
  subordination `c|x|^{-α} = ∫ e^{-s|x|²} ρ(ds)` (`RieszPositiveDefinite.mixOne_spec`), the
  Gaussian Fourier integral `∫ g_s(ξ) e^{iξx} dξ = e^{-s|x|²}` (Mathlib's
  `GaussianFourier.integral_cexp_neg_mul_sq_norm_add`), and three applications of Fubini,
  justified by the Schwartz decay of `φ` and of its Fourier transform
  (`RieszPositiveDefinite.schwartz_bound`) together with the two temperedness integrals.
  No Fourier transform of `|x|^{-α}` and no Bochner-Schwartz theorem is used.

Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.RieszPositiveDefinite
public import StratonovichHAMSecondMoment.RieszFourDiagrams
public import StratonovichHAMSecondMoment.WhiteModel

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Metric Filter
open scoped ENNReal NNReal FourierTransform

namespace StratonovichHAMSecondMoment.RieszInstanceOne

open HomogHypothesis (Rd IsTempered IsEven IsPosDefDistr IsSpectralMeasure HomogCovariance)
open HigherRieszTwo (riesz measurable_riesz)
open RieszPositiveDefinite (gauss mixOne mixOne_spec mixOne_nonneg posdef_of_mixture
  continuous_gauss_joint schwartz_bound)

/-! ### Definitions -/

/-- The mixing measure `ρ = c Γ(α/2)^{-1} s^{α/2-1} ds` on `(0, ∞)` of `c|x|^{-α}`
(`c · RieszPositiveDefinite.mixOne α`). -/
def mixR (c α : ℝ) : Measure ℝ := ENNReal.ofReal c • mixOne α

/-- The heat kernel `g_s(ξ) = (4πs)^{-1/2} e^{-|ξ|²/(4s)}` on `ℝ`, whose Fourier integral is
`e^{-s|x|²}` (used for `s > 0`). -/
def gaussK (s : ℝ) (ξ : Rd 1) : ℝ :=
  (4 * π * s) ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / (4 * s)) * ‖ξ‖ ^ 2)

/-- The density `h(ξ) = ∫ g_s(ξ) ρ(ds)` of the spectral measure of `c|x|^{-α} dx` on `ℝ`. -/
def spectralDensity (c α : ℝ) (ξ : Rd 1) : ℝ≥0∞ :=
  ∫⁻ s, ENNReal.ofReal (gaussK s ξ) ∂mixR c α

/-- The spectral measure `μ = h(ξ) dξ` of `c|x|^{-α} dx` on `ℝ` (`H:homog`, TeX 384-401). -/
def rieszSpectral (c α : ℝ) : Measure (Rd 1) :=
  (volume : Measure (Rd 1)).withDensity (spectralDensity c α)

/-- The weight `(1 + |ξ|)^{-2}` of the temperedness integrals (`k = 2` in
`HomogHypothesis.IsTempered`). -/
def wt (ξ : Rd 1) : ℝ≥0∞ := ENNReal.ofReal ((1 + ‖ξ‖) ^ (-((2 : ℕ) : ℝ)))

/-! ### The mixing measure -/

/-- Auxiliary to the Lean proof route. -/
instance mixR_sFinite (c α : ℝ) : SFinite (mixR c α) := by
  unfold mixR; infer_instance

/-- Auxiliary to the Lean proof route: `ρ` is carried by `s > 0` (`α ≠ 0`). -/
theorem mixR_pos {c α : ℝ} (hα : α ≠ 0) : ∀ᵐ s ∂mixR c α, 0 < s := by
  refine Measure.ae_smul_measure ?_ _
  unfold mixOne
  simp only [hα, ↓reduceIte]
  refine (withDensity_absolutelyContinuous _ _).ae_le ?_
  exact ae_restrict_mem measurableSet_Ioi

/-- The subordination `c|x|^{-α} = ∫ e^{-s|x|²} ρ(ds)` for `x ≠ 0`, with integrability. -/
theorem riesz_mix {c α : ℝ} (hc : 0 ≤ c) (hα : 0 < α) {x : Rd 1} (hx : x ≠ 0) :
    Integrable (fun s => Real.exp (-s * ‖x‖ ^ 2)) (mixR c α) ∧
      ∫ s, Real.exp (-s * ‖x‖ ^ 2) ∂mixR c α = c * ‖x‖ ^ (-α) := by
  obtain ⟨hI, hv⟩ := mixOne_spec hα.le (norm_ne_zero_iff.2 hx)
  refine ⟨hI.smul_measure ENNReal.ofReal_ne_top, ?_⟩
  rw [mixR, integral_smul_measure, hv, abs_norm, ENNReal.toReal_ofReal hc, smul_eq_mul]

/-! ### The heat kernel -/

/-- Auxiliary to the Lean proof route. -/
theorem measurable_gaussK : Measurable fun p : ℝ × Rd 1 => gaussK p.1 p.2 := by
  unfold gaussK; fun_prop

/-- Auxiliary to the Lean proof route. -/
theorem gaussK_nonneg {s : ℝ} (hs : 0 < s) (ξ : Rd 1) : 0 ≤ gaussK s ξ := by
  unfold gaussK; positivity

/-- Auxiliary to the Lean proof route: `g_s ≤ (4πs)^{-1/2}`. -/
theorem gaussK_le {s : ℝ} (hs : 0 < s) (ξ : Rd 1) :
    gaussK s ξ ≤ (4 * π * s) ^ (-(1 / 2 : ℝ)) := by
  unfold gaussK
  have h1 : Real.exp (-(1 / (4 * s)) * ‖ξ‖ ^ 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ 1 / (4 * s) * ‖ξ‖ ^ 2 := by positivity
    linarith
  have h0 : 0 ≤ (4 * π * s) ^ (-(1 / 2 : ℝ)) := by positivity
  calc (4 * π * s) ^ (-(1 / 2 : ℝ)) * Real.exp (-(1 / (4 * s)) * ‖ξ‖ ^ 2)
      ≤ (4 * π * s) ^ (-(1 / 2 : ℝ)) * 1 := by gcongr
    _ = _ := mul_one _

/-- Auxiliary to the Lean proof route: `g_s` has mass one. -/
theorem integral_gaussK {s : ℝ} (hs : 0 < s) : ∫ ξ : Rd 1, gaussK s ξ = 1 := by
  unfold gaussK
  rw [integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity),
    finrank_euclideanSpace_fin]
  have hp : 0 < 4 * π * s := by positivity
  have hq : π / (1 / (4 * s)) = 4 * π * s := by field_simp
  rw [hq, Real.rpow_neg hp.le, Nat.cast_one]
  exact inv_mul_cancel₀ (Real.rpow_pos_of_pos hp _).ne'

/-- Auxiliary to the Lean proof route. -/
theorem integrable_gaussK {s : ℝ} (hs : 0 < s) : Integrable (gaussK s) :=
  Integrable.of_integral_ne_zero (by rw [integral_gaussK hs]; exact one_ne_zero)

/-- The Gaussian Fourier integral `∫ g_s(ξ) e^{iξx} dξ = e^{-s|x|²}` (`s > 0`), in the
convention of `H:homog`. -/
theorem gaussK_charfun {s : ℝ} (hs : 0 < s) (x : Rd 1) :
    ∫ ξ : Rd 1, (gaussK s ξ : ℂ) * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) =
      (Real.exp (-s * ‖x‖ ^ 2) : ℂ) := by
  have hb : 0 < ((1 / (4 * s) : ℂ)).re := by
    have : ((1 / (4 * s) : ℂ)) = ((1 / (4 * s) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]; positivity
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := Rd 1) hb Complex.I x
  rw [finrank_euclideanSpace_fin] at h
  have hp : 0 < 4 * π * s := by positivity
  have hfun : ∀ ξ : Rd 1, (gaussK s ξ : ℂ) * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) =
      (((4 * π * s) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        Complex.exp (-(1 / (4 * s) : ℂ) * (‖ξ‖ : ℂ) ^ 2 + Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) := by
    intro ξ
    unfold gaussK
    rw [Complex.exp_add, real_inner_comm]
    push_cast
    ring
  simp_rw [hfun]
  rw [integral_const_mul, h, Complex.I_sq]
  have hq : (π : ℂ) / (1 / (4 * s) : ℂ) = ((4 * π * s : ℝ) : ℂ) := by
    push_cast; field_simp
  have hhalf : ((1 : ℕ) : ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hq, hhalf, ← Complex.ofReal_cpow hp.le, ← mul_assoc, ← Complex.ofReal_mul,
    Real.rpow_neg hp.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hp _).ne', Complex.ofReal_one,
    one_mul]
  push_cast
  congr 1
  field_simp

/-! ### The covariance `Γ = c|x|^{-α} dx` -/

/-- Auxiliary to the Lean proof route: `|x|^{-α}(1+|x|)^{-2}` is integrable on `ℝ` for
`0 ≤ α < 1`. -/
theorem integrable_norm_rpow_wt {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    Integrable fun x : Rd 1 => ‖x‖ ^ (-α) * (1 + ‖x‖) ^ (-((2 : ℕ) : ℝ)) := by
  set g : Rd 1 → ℝ := fun x => ‖x‖ ^ (-α) * (1 + ‖x‖) ^ (-((2 : ℕ) : ℝ))
  have hgm : Measurable g := by fun_prop
  have hg0 : ∀ x, 0 ≤ g x := fun x => by positivity
  have hb : IntegrableOn g (ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := α) (by simp)
      (by simpa using hα1) (Eventually.of_forall fun x => ?_) hgm.aestronglyMeasurable
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x), one_mul]
    change ‖x‖ ^ (-α) * (1 + ‖x‖) ^ (-((2 : ℕ) : ℝ)) ≤ _
    have hq : (1 + ‖x‖) ^ (-((2 : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by norm_num)
    have := Real.rpow_nonneg (norm_nonneg x) (-α)
    calc ‖x‖ ^ (-α) * (1 + ‖x‖) ^ (-((2 : ℕ) : ℝ)) ≤ ‖x‖ ^ (-α) * 1 := by gcongr
      _ = _ := mul_one _
  have hc : IntegrableOn g (ball 0 1)ᶜ := by
    have hI : Integrable (fun x : Rd 1 => (1 + ‖x‖) ^ (-((2 : ℕ) : ℝ))) :=
      integrable_one_add_norm (by simp)
    refine hI.integrableOn.mono' hgm.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_ball.compl).2 (Eventually.of_forall fun x hx => ?_))
    have hx1 : 1 ≤ ‖x‖ := by simpa using hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    change ‖x‖ ^ (-α) * (1 + ‖x‖) ^ (-((2 : ℕ) : ℝ)) ≤ _
    have : ‖x‖ ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc ‖x‖ ^ (-α) * (1 + ‖x‖) ^ (-((2 : ℕ) : ℝ)) ≤ 1 * (1 + ‖x‖) ^ (-((2 : ℕ) : ℝ)) := by
          gcongr
      _ = _ := one_mul _
  have := hb.union hc
  rwa [union_compl_self, integrableOn_univ] at this

/-- `Γ = c|x|^{-α} dx` is tempered (`c ≥ 0`, `0 ≤ α < 1`). -/
theorem riesz_tempered {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 ≤ α) (hα1 : α < 1) :
    IsTempered ((volume : Measure (Rd 1)).withDensity (riesz c α)) := by
  refine ⟨2, ?_⟩
  have hmk : Measurable fun x : Rd 1 => ENNReal.ofReal ((1 + ‖x‖) ^ (-((2 : ℕ) : ℝ))) := by
    fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_riesz c α) hmk]
  have hI := (integrable_norm_rpow_wt hα0 hα1).const_mul c
  refine lt_of_le_of_lt (le_of_eq ?_) hI.lintegral_lt_top
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, riesz]
  rw [← ENNReal.ofReal_mul (mul_nonneg hc (Real.rpow_nonneg (norm_nonneg _) _))]
  congr 1
  ring

/-- d = 1 copy of `RieszPositiveDefinite.riesz_mixture`: `c|x|^{-e} = ∫ gauss s x ν(ds)` a.e.
(`gauss s x = e^{-s|x|²}` here, not the heat kernel `g_s = gaussK s`). -/
theorem riesz_mixture_one {c e : ℝ} (hc : 0 ≤ c) (he : 0 < e) :
    ∀ᵐ x : Rd 1, riesz c e x = ∫⁻ s, ENNReal.ofReal (gauss s x)
      ∂(ENNReal.ofReal c • (mixOne e).map fun t => fun _ : Fin 1 => t) := by
  have hnull : ∀ᵐ x : Rd 1, x ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [hnull] with x hx
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  obtain ⟨hI, hv⟩ := mixOne_spec he.le hn
  have hg : ∀ t : ℝ, gauss (fun _ : Fin 1 => t) x = Real.exp (-t * ‖x‖ ^ 2) := by
    intro t
    simp only [gauss]
    rw [← Real.exp_sum, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  have hm : Measurable fun s : Fin 1 → ℝ => ENNReal.ofReal (gauss s x) :=
    ENNReal.measurable_ofReal.comp
      (continuous_gauss_joint.comp (continuous_const.prodMk continuous_id)).measurable
  have hmap : Measurable fun t : ℝ => fun _ : Fin 1 => t :=
    (continuous_pi fun _ => continuous_id).measurable
  rw [lintegral_smul_measure, lintegral_map hm hmap]
  simp_rw [hg]
  rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun _ => (Real.exp_pos _).le), hv,
    abs_norm, riesz, ENNReal.ofReal_mul hc, smul_eq_mul]

/-- `Γ = c|x|^{-e} dx` is positive definite on `ℝ` (`c ≥ 0`, `e > 0`, `Γ` tempered). -/
theorem riesz_posdef_one {c e : ℝ} (hc : 0 ≤ c) (he0 : 0 < e)
    (ht : IsTempered ((volume : Measure (Rd 1)).withDensity (riesz c e))) :
    IsPosDefDistr ((volume : Measure (Rd 1)).withDensity (riesz c e)) := by
  have hν : ∀ᵐ s ∂(ENNReal.ofReal c • (mixOne e).map fun t => fun _ : Fin 1 => t),
      ∀ j, 0 ≤ s j := by
    refine Measure.ae_smul_measure ?_ _
    have hmeas : Measurable fun t : ℝ => fun _ : Fin 1 => t :=
      (continuous_pi fun _ => continuous_id).measurable
    have hset : MeasurableSet {s : Fin 1 → ℝ | ∀ j, 0 ≤ s j} := by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => measurableSet_le measurable_const (measurable_pi_apply j)
    rw [ae_map_iff hmeas.aemeasurable hset]
    filter_upwards [mixOne_nonneg e] with t ht using fun _ => ht
  have h := posdef_of_mixture (LinearIsometry.id : Rd 1 →ₗᵢ[ℝ] Rd 1) _ hν
    (measurable_riesz c e) (fun _ => ENNReal.ofReal_lt_top) (riesz_mixture_one hc he0) ht
  rwa [LinearIsometry.coe_id, Measure.map_id] at h

/-! ### The spectral measure -/

/-- Auxiliary to the Lean proof route. -/
theorem measurable_wt : Measurable wt := by unfold wt; fun_prop

/-- Auxiliary to the Lean proof route. -/
theorem wt_le_one (ξ : Rd 1) : wt ξ ≤ 1 := by
  unfold wt
  rw [ENNReal.ofReal_le_one]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg ξ]) (by norm_num)

/-- Auxiliary to the Lean proof route. -/
theorem wt_pos (ξ : Rd 1) : wt ξ ≠ 0 := by
  unfold wt
  exact (ENNReal.ofReal_pos.2 (by positivity)).ne'

/-- Auxiliary to the Lean proof route. -/
theorem lintegral_wt_lt_top : ∫⁻ ξ : Rd 1, wt ξ < ∞ :=
  (integrable_one_add_norm (E := Rd 1) (r := ((2 : ℕ) : ℝ)) (by simp)).lintegral_lt_top

/-- Auxiliary to the Lean proof route: the Gaussian bound of the inner integral,
`∫ g_s(ξ)(1+|ξ|)^{-2} dξ ≤ 1` (`s > 0`; the bound by `(4πs)^{-1/2} ∫ (1+|ξ|)^{-2}` is
`inner_le_sup`). -/
theorem inner_le_one {s : ℝ} (hs : 0 < s) :
    ∫⁻ ξ : Rd 1, ENNReal.ofReal (gaussK s ξ) * wt ξ ≤ 1 := by
  calc ∫⁻ ξ : Rd 1, ENNReal.ofReal (gaussK s ξ) * wt ξ
      ≤ ∫⁻ ξ : Rd 1, ENNReal.ofReal (gaussK s ξ) := by
        refine lintegral_mono fun ξ => ?_
        calc ENNReal.ofReal (gaussK s ξ) * wt ξ ≤ ENNReal.ofReal (gaussK s ξ) * 1 := by
              gcongr; exact wt_le_one ξ
          _ = _ := mul_one _
    _ = ENNReal.ofReal (∫ ξ : Rd 1, gaussK s ξ) :=
        (ofReal_integral_eq_lintegral_ofReal (integrable_gaussK hs)
          (ae_of_all _ (gaussK_nonneg hs))).symm
    _ = 1 := by rw [integral_gaussK hs, ENNReal.ofReal_one]

/-- Auxiliary to the Lean proof route. -/
theorem inner_le_sup {s : ℝ} (hs : 0 < s) :
    ∫⁻ ξ : Rd 1, ENNReal.ofReal (gaussK s ξ) * wt ξ ≤
      ENNReal.ofReal ((4 * π * s) ^ (-(1 / 2 : ℝ))) * ∫⁻ ξ : Rd 1, wt ξ := by
  rw [← lintegral_const_mul _ measurable_wt]
  exact lintegral_mono fun ξ => by gcongr; exact gaussK_le hs ξ

/-- The temperedness integral of the spectral measure, in mixture form:
`∫ ρ(ds) ∫ g_s(ξ)(1+|ξ|)^{-2} dξ < ∞` (any `c`, `0 < α < 1`; uses `α < 1` at `s → ∞`). -/
theorem lintegral_mix_wt_lt_top {c α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∫⁻ s, (∫⁻ ξ : Rd 1, ENNReal.ofReal (gaussK s ξ) * wt ξ) ∂mixR c α < ∞ := by
  set Φ : ℝ → ℝ≥0∞ := fun s => ∫⁻ ξ : Rd 1, ENNReal.ofReal (gaussK s ξ) * wt ξ
  have hΦm : Measurable Φ := by
    refine Measurable.lintegral_prod_right' (f := fun p : ℝ × Rd 1 =>
      ENNReal.ofReal (gaussK p.1 p.2) * wt p.2) ?_
    exact (ENNReal.measurable_ofReal.comp measurable_gaussK).mul (measurable_wt.comp measurable_snd)
  set a : ℝ := α / 2 - 1
  set G : ℝ := Real.Gamma (α / 2)
  have hG : 0 < G := Real.Gamma_pos_of_pos (by linarith)
  have hdm : Measurable fun s : ℝ => ENNReal.ofReal (s ^ a / G) := by fun_prop
  have hmix : mixOne α = (volume.restrict (Ioi (0 : ℝ))).withDensity
      fun s => ENNReal.ofReal (s ^ a / G) := by
    unfold mixOne; simp only [hα0.ne', ↓reduceIte]; rfl
  rw [mixR, lintegral_smul_measure, hmix, lintegral_withDensity_eq_lintegral_mul _ hdm hΦm]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  -- split `(0, ∞)` into `(0, 1)` and `[1, ∞)`
  have hsub : Ioi (0 : ℝ) ⊆ Ioo 0 1 ∪ Ici 1 := by
    intro s hs
    by_cases h1 : s < 1
    · exact Or.inl ⟨hs, h1⟩
    · exact Or.inr (not_lt.1 h1)
  have hfm : Measurable ((fun s : ℝ => ENNReal.ofReal (s ^ a / G)) * Φ) := hdm.mul hΦm
  calc ∫⁻ s in Ioi 0, ((fun s : ℝ => ENNReal.ofReal (s ^ a / G)) * Φ) s
      ≤ ∫⁻ s in Ioo 0 1 ∪ Ici 1, ((fun s : ℝ => ENNReal.ofReal (s ^ a / G)) * Φ) s :=
        lintegral_mono_set hsub
    _ ≤ (∫⁻ s in Ioo 0 1, ((fun s : ℝ => ENNReal.ofReal (s ^ a / G)) * Φ) s) +
          ∫⁻ s in Ici 1, ((fun s : ℝ => ENNReal.ofReal (s ^ a / G)) * Φ) s :=
        lintegral_union_le _ _ _
    _ < ∞ := by
      refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
      · -- near zero: `Φ ≤ 1` and `∫_0^1 s^{α/2-1} < ∞`
        have hI : IntegrableOn (fun s : ℝ => s ^ a / G) (Ioo 0 1) :=
          ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by simp only [a]; linarith)).div_const G
        refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioo fun s hs => ?_)
          hI.lintegral_lt_top
        change ENNReal.ofReal (s ^ a / G) * Φ s ≤ ENNReal.ofReal (s ^ a / G)
        calc ENNReal.ofReal (s ^ a / G) * Φ s ≤ ENNReal.ofReal (s ^ a / G) * 1 := by
              gcongr; exact inner_le_one hs.1
          _ = _ := mul_one _
      · -- at infinity: `Φ ≤ (4πs)^{-1/2} ∫ w` and `∫_1^∞ s^{α/2-3/2} < ∞`
        set K : ℝ := (4 * π) ^ (-(1 / 2 : ℝ)) / G
        have hI : IntegrableOn (fun s : ℝ => K * s ^ (a - 1 / 2)) (Ici 1) := by
          rw [integrableOn_Ici_iff_integrableOn_Ioi]
          exact ((integrableOn_Ioi_rpow_iff zero_lt_one).2 (by simp only [a]; linarith)).const_mul K
        have hle : ∀ s ∈ Ici (1 : ℝ), ((fun s : ℝ => ENNReal.ofReal (s ^ a / G)) * Φ) s ≤
            ENNReal.ofReal (K * s ^ (a - 1 / 2)) * ∫⁻ ξ : Rd 1, wt ξ := by
          intro s hs
          have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
          change ENNReal.ofReal (s ^ a / G) * Φ s ≤ _
          calc ENNReal.ofReal (s ^ a / G) * Φ s ≤ ENNReal.ofReal (s ^ a / G) *
                (ENNReal.ofReal ((4 * π * s) ^ (-(1 / 2 : ℝ))) * ∫⁻ ξ : Rd 1, wt ξ) := by
                gcongr; exact inner_le_sup hs0
            _ = ENNReal.ofReal (s ^ a / G * (4 * π * s) ^ (-(1 / 2 : ℝ))) *
                  ∫⁻ ξ : Rd 1, wt ξ := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
            _ = ENNReal.ofReal (K * s ^ (a - 1 / 2)) * ∫⁻ ξ : Rd 1, wt ξ := by
                congr 2
                rw [Real.mul_rpow (by positivity) hs0.le, Real.rpow_sub hs0 a (1 / 2),
                  Real.rpow_neg (x := s) hs0.le]
                simp only [K]
                ring
        calc ∫⁻ s in Ici 1, ((fun s : ℝ => ENNReal.ofReal (s ^ a / G)) * Φ) s
            ≤ ∫⁻ s in Ici 1, ENNReal.ofReal (K * s ^ (a - 1 / 2)) * ∫⁻ ξ : Rd 1, wt ξ :=
              setLIntegral_mono' measurableSet_Ici hle
          _ = (∫⁻ s in Ici 1, ENNReal.ofReal (K * s ^ (a - 1 / 2))) * ∫⁻ ξ : Rd 1, wt ξ :=
              lintegral_mul_const _ (by fun_prop)
          _ < ∞ := ENNReal.mul_lt_top hI.lintegral_lt_top lintegral_wt_lt_top

/-- Auxiliary to the Lean proof route. -/
theorem measurable_spectralDensity (c α : ℝ) : Measurable (spectralDensity c α) := by
  unfold spectralDensity
  exact Measurable.lintegral_prod_right' (f := fun p : Rd 1 × ℝ => ENNReal.ofReal (gaussK p.2 p.1))
    (ENNReal.measurable_ofReal.comp (measurable_gaussK.comp measurable_swap))

/-- `∫ h(ξ) (1+|ξ|)^{-2} dξ = ∫ ρ(ds) ∫ g_s(ξ)(1+|ξ|)^{-2} dξ` (Tonelli). -/
theorem lintegral_spectralDensity_wt (c α : ℝ) :
    ∫⁻ ξ, spectralDensity c α ξ * wt ξ =
      ∫⁻ s, (∫⁻ ξ : Rd 1, ENNReal.ofReal (gaussK s ξ) * wt ξ) ∂mixR c α := by
  unfold spectralDensity
  have hc : ∀ ξ : Rd 1, (∫⁻ s, ENNReal.ofReal (gaussK s ξ) ∂mixR c α) * wt ξ =
      ∫⁻ s, ENNReal.ofReal (gaussK s ξ) * wt ξ ∂mixR c α := fun ξ =>
    (lintegral_mul_const _ (ENNReal.measurable_ofReal.comp
      (measurable_gaussK.comp (measurable_id.prodMk measurable_const)))).symm
  simp_rw [hc]
  refine lintegral_lintegral_swap ?_
  exact ((ENNReal.measurable_ofReal.comp (measurable_gaussK.comp measurable_swap)).mul
    (measurable_wt.comp measurable_fst)).aemeasurable

/-- The spectral measure is tempered. -/
theorem rieszSpectral_tempered {c α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    IsTempered (rieszSpectral c α) := by
  refine ⟨2, ?_⟩
  change ∫⁻ ξ, wt ξ ∂rieszSpectral c α < ∞
  rw [rieszSpectral, lintegral_withDensity_eq_lintegral_mul _ (measurable_spectralDensity c α)
    measurable_wt]
  exact (lintegral_spectralDensity_wt c α).symm ▸ lintegral_mix_wt_lt_top hα0 hα1

/-- Auxiliary to the Lean proof route: `h(ξ) < ∞` for a.e. `ξ`. -/
theorem spectralDensity_lt_top {c α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∀ᵐ ξ : Rd 1, spectralDensity c α ξ < ∞ := by
  have h : ∫⁻ ξ, spectralDensity c α ξ * wt ξ < ∞ :=
    (lintegral_spectralDensity_wt c α).symm ▸ lintegral_mix_wt_lt_top hα0 hα1
  filter_upwards [ae_lt_top' ((measurable_spectralDensity c α).mul measurable_wt).aemeasurable
    h.ne] with ξ hξ
  exact ENNReal.lt_top_of_mul_ne_top_left hξ.ne (wt_pos ξ)

/-- The spectral measure is even. -/
theorem rieszSpectral_even (c α : ℝ) : IsEven (rieszSpectral c α) :=
  EndpointLemmas.isEven_withDensity (measurable_spectralDensity c α) fun ξ => by
    simp [spectralDensity, gaussK, norm_neg]

/-! ### The spectral identity -/

/-- The inner integral `F(ξ) = ∫ φ(x) e^{iξx} dx` of the spectral identity. -/
def innerF (φ : SchwartzMap (Rd 1) ℂ) (ξ : Rd 1) : ℂ :=
  ∫ x, φ x * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))

/-- Auxiliary to the Lean proof route: `F(ξ) = 𝓕φ(-ξ/(2π))` is continuous and
`|F(ξ)| ≤ M (1+|ξ|)^{-2}` (Schwartz decay of the Fourier transform). -/
theorem innerF_decay (φ : SchwartzMap (Rd 1) ℂ) :
    Continuous (innerF φ) ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ ξ, ‖innerF φ ξ‖ ≤ M * (1 + ‖ξ‖) ^ (-((2 : ℕ) : ℝ)) := by
  have hF : ∀ ξ, innerF φ ξ = (𝓕 φ) (-(2 * π)⁻¹ • ξ) := by
    intro ξ
    rw [innerF, WhiteModel.inner_integral_eq_fourier (φ : Rd 1 → ℂ), SchwartzMap.fourier_coe]
  refine ⟨?_, ?_⟩
  · have : innerF φ = fun ξ => (𝓕 φ) (-(2 * π)⁻¹ • ξ) := funext hF
    rw [this]
    exact (𝓕 φ).continuous.comp (continuous_const_smul _)
  obtain ⟨B, hB0, hB⟩ := schwartz_bound (𝓕 φ) 2
  refine ⟨(2 * π) ^ 2 * B, by positivity, fun ξ => ?_⟩
  have hpi : 0 < 2 * π := by positivity
  have hpi1 : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
  have hη : ‖-(2 * π)⁻¹ • ξ‖ = ‖ξ‖ / (2 * π) := by
    rw [norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg hpi.le]; ring
  have h1 : 1 + ‖ξ‖ ≤ 2 * π * (1 + ‖-(2 * π)⁻¹ • ξ‖) := by
    rw [hη, mul_add, mul_div_cancel₀ _ hpi.ne']; linarith
  have hx : 0 < 1 + ‖ξ‖ := by positivity
  rw [hF, Real.rpow_neg hx.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖(𝓕 φ) (-(2 * π)⁻¹ • ξ)‖ * (1 + ‖ξ‖) ^ 2
      ≤ ‖(𝓕 φ) (-(2 * π)⁻¹ • ξ)‖ * (2 * π * (1 + ‖-(2 * π)⁻¹ • ξ‖)) ^ 2 := by gcongr
    _ = (2 * π) ^ 2 * ((1 + ‖-(2 * π)⁻¹ • ξ‖) ^ 2 * ‖(𝓕 φ) (-(2 * π)⁻¹ • ξ)‖) := by ring
    _ ≤ (2 * π) ^ 2 * B := by gcongr; exact hB _

/-- Step 1 (subordination and Fubini in `(x, s)`):
`∫ φ dΓ = ∫ ρ(ds) ∫ e^{-s|x|²} φ(x) dx`. -/
theorem step_one {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1)
    (φ : SchwartzMap (Rd 1) ℂ) :
    ∫ x, φ x ∂(volume : Measure (Rd 1)).withDensity (riesz c α) =
      ∫ s, (∫ x : Rd 1, Real.exp (-s * ‖x‖ ^ 2) • φ x) ∂mixR c α := by
  have hnull : ∀ᵐ x : Rd 1, x ≠ 0 := by
    rw [ae_iff]; simp
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_riesz c α)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hcongr : ∀ᵐ x : Rd 1, (riesz c α x).toReal • φ x =
      ∫ s, Real.exp (-s * ‖x‖ ^ 2) • φ x ∂mixR c α := by
    filter_upwards [hnull] with x hx
    rw [integral_smul_const, (riesz_mix hc hα0 hx).2, riesz,
      ENNReal.toReal_ofReal (mul_nonneg hc (Real.rpow_nonneg (norm_nonneg _) _))]
  rw [integral_congr_ae hcongr]
  refine integral_integral_swap ?_
  -- integrability on `Leb × ρ`
  have hcont : Continuous fun p : Rd 1 × ℝ => Real.exp (-p.2 * ‖p.1‖ ^ 2) • φ p.1 := by
    fun_prop
  change Integrable (fun p : Rd 1 × ℝ => Real.exp (-p.2 * ‖p.1‖ ^ 2) • φ p.1) _
  rw [integrable_prod_iff hcont.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · filter_upwards [hnull] with x hx
    exact (riesz_mix hc hα0 hx).1.smul_const (φ x)
  · obtain ⟨B, hB0, hB⟩ := schwartz_bound φ 2
    have hI := (integrable_norm_rpow_wt hα0.le hα1).const_mul (c * B)
    refine hI.mono' ?_ ?_
    · exact (hcont.norm.stronglyMeasurable.integral_prod_right' (ν := mixR c α) :
        StronglyMeasurable fun x : Rd 1 => ∫ s, ‖Real.exp (-s * ‖x‖ ^ 2) • φ x‖ ∂mixR c α)
        |>.aestronglyMeasurable
    filter_upwards [hnull] with x hx
    have hval : ∫ s, ‖Real.exp (-s * ‖x‖ ^ 2) • φ x‖ ∂mixR c α = c * ‖x‖ ^ (-α) * ‖φ x‖ := by
      simp_rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      rw [integral_mul_const, (riesz_mix hc hα0 hx).2]
    rw [hval, Real.norm_of_nonneg (by positivity)]
    have hx1 : 0 < 1 + ‖x‖ := by positivity
    have hφ : ‖φ x‖ ≤ B * (1 + ‖x‖) ^ (-((2 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg hx1.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity),
        mul_comm]
      exact hB x
    have h0 : 0 ≤ c * ‖x‖ ^ (-α) := mul_nonneg hc (Real.rpow_nonneg (norm_nonneg _) _)
    calc c * ‖x‖ ^ (-α) * ‖φ x‖ ≤ c * ‖x‖ ^ (-α) * (B * (1 + ‖x‖) ^ (-((2 : ℕ) : ℝ))) := by
          gcongr
      _ = _ := by ring

/-- Step 2 (Gaussian Fourier integral and Fubini in `(x, ξ)`), for `s > 0`:
`∫ e^{-s|x|²} φ(x) dx = ∫ g_s(ξ) F(ξ) dξ`. -/
theorem step_two {s : ℝ} (hs : 0 < s) (φ : SchwartzMap (Rd 1) ℂ) :
    ∫ x : Rd 1, Real.exp (-s * ‖x‖ ^ 2) • φ x = ∫ ξ : Rd 1, (gaussK s ξ : ℂ) * innerF φ ξ := by
  have h1 : ∀ x : Rd 1, Real.exp (-s * ‖x‖ ^ 2) • φ x =
      ∫ ξ : Rd 1, (gaussK s ξ : ℂ) * (φ x * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ))) := by
    intro x
    rw [Complex.real_smul, ← gaussK_charfun hs x, ← integral_mul_const]
    congr 1; ext ξ; ring
  simp_rw [h1, innerF, ← integral_const_mul]
  refine integral_integral_swap ?_
  have hcont : Continuous fun p : Rd 1 × Rd 1 => (gaussK s p.2 : ℂ) *
      (φ p.1 * Complex.exp (Complex.I * (inner ℝ p.2 p.1 : ℝ))) := by
    unfold gaussK; fun_prop
  refine ((φ.integrable.norm).mul_prod (integrable_gaussK hs)).mono'
    hcont.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  change ‖(gaussK s p.2 : ℂ) * (φ p.1 * Complex.exp (Complex.I * (inner ℝ p.2 p.1 : ℝ)))‖ ≤ _
  rw [norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, Complex.norm_real,
    Real.norm_of_nonneg (gaussK_nonneg hs _)]
  simp only [mul_one]
  exact le_of_eq (mul_comm _ _)

/-- Step 3 (Fubini in `(s, ξ)`):
`∫ ρ(ds) ∫ g_s(ξ) F(ξ) dξ = ∫ F dμ`. -/
theorem step_three {c α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (φ : SchwartzMap (Rd 1) ℂ) :
    ∫ s, (∫ ξ : Rd 1, (gaussK s ξ : ℂ) * innerF φ ξ) ∂mixR c α =
      ∫ ξ, innerF φ ξ ∂rieszSpectral c α := by
  obtain ⟨hFc, M, hM0, hM⟩ := innerF_decay φ
  have hpos := mixR_pos (c := c) hα0.ne'
  rw [rieszSpectral, integral_withDensity_eq_integral_toReal_smul (measurable_spectralDensity c α)
    (spectralDensity_lt_top hα0 hα1)]
  have hfm : Measurable fun p : ℝ × Rd 1 => (gaussK p.1 p.2 : ℂ) * innerF φ p.2 :=
    (Complex.measurable_ofReal.comp measurable_gaussK).mul (hFc.measurable.comp measurable_snd)
  rw [integral_integral_swap (f := fun s ξ => (gaussK s ξ : ℂ) * innerF φ ξ) ?_]
  · refine integral_congr_ae ?_
    filter_upwards with ξ
    rw [integral_mul_const, integral_complex_ofReal, Complex.real_smul]
    congr 2
    unfold spectralDensity
    have hξm : Measurable fun s : ℝ => gaussK s ξ :=
      measurable_gaussK.comp (measurable_id.prodMk measurable_const)
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun s => gaussK s ξ) ?_ hξm.aestronglyMeasurable]
    filter_upwards [hpos] with s hs using gaussK_nonneg hs ξ
  -- integrability on `ρ × Leb`
  refine ⟨hfm.aestronglyMeasurable, ?_⟩
  have hbd : ∀ᵐ p ∂(mixR c α).prod (volume : Measure (Rd 1)),
      ‖(gaussK p.1 p.2 : ℂ) * innerF φ p.2‖ₑ ≤
        ENNReal.ofReal M * (ENNReal.ofReal (gaussK p.1 p.2) * wt p.2) := by
    have : ∀ᵐ p ∂(mixR c α).prod (volume : Measure (Rd 1)), 0 < p.1 :=
      Measure.quasiMeasurePreserving_fst.ae hpos
    filter_upwards [this] with p hp
    rw [← ofReal_norm, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (gaussK_nonneg hp _), wt,
      ← ENNReal.ofReal_mul (gaussK_nonneg hp _), ← ENNReal.ofReal_mul hM0]
    refine ENNReal.ofReal_le_ofReal ?_
    calc gaussK p.1 p.2 * ‖innerF φ p.2‖ ≤ gaussK p.1 p.2 *
          (M * (1 + ‖p.2‖) ^ (-((2 : ℕ) : ℝ))) := by
          gcongr
          · exact gaussK_nonneg hp _
          · exact hM _
      _ = _ := by ring
  refine lt_of_le_of_lt (lintegral_mono_ae hbd) ?_
  have hmeas : Measurable fun p : ℝ × Rd 1 => ENNReal.ofReal (gaussK p.1 p.2) * wt p.2 :=
    (ENNReal.measurable_ofReal.comp measurable_gaussK).mul (measurable_wt.comp measurable_snd)
  rw [lintegral_const_mul (ENNReal.ofReal M) hmeas, lintegral_prod _ hmeas.aemeasurable]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_mix_wt_lt_top hα0 hα1)

/-- The spectral identity of `H:homog` (TeX 384-401) for `Γ = c|x|^{-α} dx` on `ℝ`:
`∫ φ dΓ = ∫ (∫ φ(x) e^{iξx} dx) μ(dξ)` for every Schwartz `φ` (`c ≥ 0`, `0 < α < 1`). -/
theorem isSpectralMeasure_riesz {c α : ℝ} (hc : 0 ≤ c) (hα0 : 0 < α) (hα1 : α < 1) :
    IsSpectralMeasure ((volume : Measure (Rd 1)).withDensity (riesz c α)) (rieszSpectral c α) := by
  intro φ
  rw [step_one hc hα0 hα1 φ]
  have hpos := mixR_pos (c := c) hα0.ne'
  rw [integral_congr_ae (hpos.mono fun s hs => step_two hs φ)]
  exact step_three hα0 hα1 φ

/-! ### The instance -/

/-- **`E:d1-covariances` (Riesz case) is an instance of `H:homog`** (TeX lines 5317-5322 with
384-401 at revision edf7085f (book 1.1.3)), with the explicit spectral measure
`rieszSpectral c α`: for `0 < α₀ < 1`, `c > 0` and `0 < α < 1`. -/
theorem riesz_homogCovariance_one_spectral {c α α₀ : ℝ} (hα₀0 : 0 < α₀) (hα₀1 : α₀ < 1)
    (hc : 0 < c) (hα0 : 0 < α) (hα1 : α < 1) :
    HomogCovariance 1 α α₀ ((volume : Measure (Rd 1)).withDensity (riesz c α))
      (rieszSpectral c α) where
  dim := Or.inl rfl
  alpha0_pos := hα₀0
  alpha0_lt_one := hα₀1
  Γ_radon := EndpointLemmas.isLocallyFiniteMeasure_of_tempered (riesz_tempered hc.le hα0.le hα1)
  Γ_even := EndpointLemmas.isEven_withDensity (measurable_riesz c α) fun x => by simp [riesz]
  Γ_tempered := riesz_tempered hc.le hα0.le hα1
  Γ_posdef := riesz_posdef_one hc.le hα0 (riesz_tempered hc.le hα0.le hα1)
  μ_radon := EndpointLemmas.isLocallyFiniteMeasure_of_tempered (rieszSpectral_tempered hα0 hα1)
  μ_even := rieszSpectral_even c α
  μ_tempered := rieszSpectral_tempered hα0 hα1
  spectral := isSpectralMeasure_riesz hc.le hα0 hα1
  scaling := by
    have := EndpointLemmas.scaling_withDensity (n := 1) (measurable_riesz c α)
      fun r hr x => RieszFourDiagrams.riesz_smul c α hr x
    simpa [EndpointLemmas.Scaling] using this
  threshold := by linarith
  alpha_range := Or.inl ⟨hα0, by simpa using hα1⟩

/-- **`E:d1-covariances` (Riesz case) is an instance of `H:homog`** (TeX lines 5317-5322 with
384-401 at revision edf7085f (book 1.1.3)): for `0 < α₀ < 1`, `c > 0` and `0 < α < 1` the
covariance `c|y|^{-α} dy` on `ℝ` has a spectral measure `μ` with
`HomogCovariance 1 α α₀ (volume.withDensity (riesz c α)) μ`.  The target of item L20-R. -/
theorem riesz_homogCovariance_one {c α α₀ : ℝ} (hα₀0 : 0 < α₀) (hα₀1 : α₀ < 1) (hc : 0 < c)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ μ : Measure (Rd 1), HomogCovariance 1 α α₀ (volume.withDensity (riesz c α)) μ :=
  ⟨rieszSpectral c α, riesz_homogCovariance_one_spectral hα₀0 hα₀1 hc hα0 hα1⟩

end StratonovichHAMSecondMoment.RieszInstanceOne
