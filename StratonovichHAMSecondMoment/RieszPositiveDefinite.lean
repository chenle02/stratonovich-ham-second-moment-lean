module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Positive definiteness of the Riesz-type covariance measures of Section `S:three-endpoints` of
the main TeX file `notes/notes_stratonovich_ham_second_moment.tex` at revision edf7085f (all
line numbers below are at edf7085f).  This module proves the three inputs that wave L14-3D
supplied as named hypotheses:
* `EndpointLemmas.RieszProductPD` (`c ∏_j |x_j|^{-e_j} dx` on `ℝ³`, `c ≥ 0`, `0 ≤ e_j < 1`;
  the Gaussian-mixture argument in the proof of `L:product-endpoints`, lines 7251-7265);
* `EndpointLemmas.PlaneRieszPD` (`c ∏_j |y_j|^{-e_j} dy δ₀(dz)`, `c ≥ 0`, `0 ≤ e_j < 1`; proof
  of `L:plane-endpoints`, lines 7353-7384, including the low endpoint `e = 0`);
* `EndpointCorollaries.RieszIsoPD` (`c|x|^{-e} dx` on `ℝ³`, `c ≥ 0`, `0 < e < 3`; proof of
  `C:three-product-riesz`, lines 7971-7980),
and re-issues the four wrappers that consumed them without these inputs:
`product_endpoints_paper_proved` (`L:product-endpoints`), `plane_endpoints_paper_proved`
(`L:plane-endpoints`), `three_product_riesz_paper_proved` (`C:three-product-riesz`) and
`three_finite_images_paper_proved` (`C:three-finite-images`).  The existing statements are
unchanged; the new ones are the old ones with the positive-definiteness hypotheses removed.

Positive definiteness is the package's `HomogHypothesis.IsPosDefDistr`: for every complex
Schwartz `φ`, `∫ (φ ⋆ φ̃) dΓ` is a nonnegative real (`φ ⋆ φ̃ = acorr φ` below).

Proof route (the TeX's Gaussian subordination, with two Lean-route changes):
* Mixture.  `|u|^{-e} = Γ(e/2)^{-1} ∫_0^∞ s^{e/2-1} e^{-su²} ds` for `e > 0`, `u ≠ 0`
  (`mixOne_spec`, from Mathlib's `Real.integral_rpow_mul_exp_neg_mul_Ioi`); a zero exponent
  uses the Dirac mixing measure at `s = 0` (the constant one, no Gamma factor, as at TeX line
  7265).  Products over the coordinates use the product mixing measure (`prodRiesz_mixture`),
  the isotropic power the diagonal image (`riesz_mixture`); the identities hold off the
  Lebesgue-null coordinate hyperplanes (resp. off `0`).
* Gaussian positivity, without Fourier transforms (Lean-route change 1): for `s_j > 0` the
  Gaussian `g_s(x) = ∏ e^{-s_j x_j²}` is, up to a positive constant, the autocorrelation
  `∫ h(x+v) h(v) dv` of `h = g_{2s}` (`gauss_autocorr`); its form against `acorr φ ∘ ι`
  becomes `∫∫ h(a) h(b) acorr φ(ι a - ι b) da db = ∫ |∫ h(a) φ(ι a + w) da|² dw`
  (`gauss_form_eq`, `autocorr_form_nnr`).  With `ι` the plane embedding this is the TeX's
  tangential quadratic form integrated in `z`.
* Degenerate Gaussians (Lean-route change 2): a zero mixing parameter (zero exponent) gives a
  Gaussian constant in that coordinate.  Instead of a separate argument, the density is
  damped by `e^{-δ|x|²}` (all parameters shifted by `δ > 0`), Fubini over the mixing measure
  is applied, and `δ → 0` by dominated convergence (`nnr_of_mixture`).
* Absolute integrability.  `|acorr φ(x)| ≤ C_k (1+|x|)^{-k}` for every `k` (`acorr_decay`),
  and the measures are tempered (`EndpointLemmas.prodRieszMeasure_tempered`,
  `EndpointCorollaries.riesz_props`); this replaces the TeX's coordinatewise bound
  `C_N ∏(1+|x_j|)^{-N}` by the radial one.

Class: the three inputs are proved (no supplied input, nothing added); the four re-issued
wrappers have exactly the hypotheses of the originals minus the discharged inputs.  The two
corollary wrappers remain narrower for the reasons recorded in `EndpointCorollaries`
(`ThreeTransfer` supplied, abstract `ThreeMomentModel`).  Lemmas marked "Auxiliary to the Lean
proof route" have no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.EndpointLemmas
public import StratonovichHAMSecondMoment.EndpointCorollaries

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter
open scoped ENNReal NNReal Topology

namespace StratonovichHAMSecondMoment.RieszPositiveDefinite

open HomogHypothesis (Rd IsTempered IsPosDefDistr)
open EndpointLemmas
open EndpointCorollaries

/-! ### Nonnegative reals, Gaussians, autocorrelations -/

/-- Auxiliary to the Lean proof route: a complex number is a nonnegative real. -/
def NNR (z : ℂ) : Prop := z.im = 0 ∧ 0 ≤ z.re

/-- Auxiliary to the Lean proof route: `NNR` is preserved by nonnegative real factors. -/
theorem nnr_ofReal_mul {C : ℝ} (hC : 0 ≤ C) {z : ℂ} (hz : NNR z) : NNR ((C : ℂ) * z) := by
  refine ⟨?_, ?_⟩
  · simp [Complex.mul_im, hz.1]
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hC hz.2

/-- Auxiliary to the Lean proof route: the integral of an a.e. `NNR` function is `NNR`. -/
theorem nnr_integral {X : Type*} [MeasurableSpace X] {μ : Measure X} {G : X → ℂ}
    (hG : ∀ᵐ x ∂μ, NNR (G x)) : NNR (∫ x, G x ∂μ) := by
  have h : ∫ x, G x ∂μ = ∫ x, ((G x).re : ℂ) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hG] with x hx
    exact Complex.ext (by simp) (by simp [hx.1])
  rw [h, integral_complex_ofReal]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact integral_nonneg_of_ae (by filter_upwards [hG] with x hx; exact hx.2)

/-- Auxiliary to the Lean proof route: `NNR` is closed under limits. -/
theorem nnr_of_tendsto {u : ℕ → ℂ} {z : ℂ} (hu : Tendsto u atTop (𝓝 z)) (h : ∀ k, NNR (u k)) :
    NNR z := by
  refine ⟨?_, ?_⟩
  · have h1 := (Complex.continuous_im.tendsto z).comp hu
    have h2 : (Complex.im ∘ u) = fun _ => (0 : ℝ) := funext fun k => (h k).1
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  · exact ge_of_tendsto' ((Complex.continuous_re.tendsto z).comp hu) fun k => (h k).2

/-- The anisotropic Gaussian `g_s(x) = ∏_j e^{-s_j x_j²}` on `ℝ^m` (the Gaussians of the
mixtures at main TeX lines 7255-7260, 7360-7367, 7975-7978). -/
def gauss {m : ℕ} (s : Fin m → ℝ) (x : Rd m) : ℝ := ∏ j, Real.exp (-s j * x j ^ 2)

/-- Auxiliary to the Lean proof route. -/
theorem gauss_pos {m : ℕ} (s : Fin m → ℝ) (x : Rd m) : 0 < gauss s x :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

/-- Auxiliary to the Lean proof route. -/
theorem gauss_add {m : ℕ} (s t : Fin m → ℝ) (x : Rd m) :
    gauss (s + t) x = gauss s x * gauss t x := by
  simp only [gauss, ← Finset.prod_mul_distrib, ← Real.exp_add, Pi.add_apply]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring_nf

/-- Auxiliary to the Lean proof route: a Gaussian with nonnegative parameters is at most one. -/
theorem gauss_le_one {m : ℕ} {s : Fin m → ℝ} (hs : ∀ j, 0 ≤ s j) (x : Rd m) : gauss s x ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => (Real.exp_pos _).le) fun j _ =>
    Real.exp_le_one_iff.2 (by nlinarith [hs j, sq_nonneg (x j)])

/-- Auxiliary to the Lean proof route. -/
theorem continuous_gauss_joint {m : ℕ} :
    Continuous fun p : Rd m × (Fin m → ℝ) => gauss p.2 p.1 := by
  unfold gauss
  refine continuous_finsetProd _ fun j _ => ?_
  have h1 : Continuous fun p : Rd m × (Fin m → ℝ) => p.1 j :=
    (EuclideanSpace.proj j).continuous.comp continuous_fst
  have h2 : Continuous fun p : Rd m × (Fin m → ℝ) => p.2 j :=
    (continuous_apply j).comp continuous_snd
  exact Real.continuous_exp.comp ((h2.neg).mul (h1.pow 2))

/-- Auxiliary to the Lean proof route. -/
theorem continuous_gauss {m : ℕ} (s : Fin m → ℝ) : Continuous (gauss s) :=
  continuous_gauss_joint.comp (continuous_id.prodMk continuous_const)

/-- Auxiliary to the Lean proof route: Gaussians with positive parameters are integrable. -/
theorem integrable_gauss {m : ℕ} {s : Fin m → ℝ} (hs : ∀ j, 0 < s j) :
    Integrable (gauss s) :=
  integrable_prod_coord (g := fun j t => Real.exp (-s j * t ^ 2))
    fun j => integrable_exp_neg_mul_sq (hs j)

/-- The autocorrelation `(φ ⋆ φ̃)(x) = ∫ φ(x + y) conj φ(y) dy` of the definition of
`IsPosDefDistr`. -/
def acorr {d : ℕ} (φ : SchwartzMap (Rd d) ℂ) (x : Rd d) : ℂ :=
  ∫ y, φ (x + y) * (starRingEnd ℂ) (φ y)

/-- Auxiliary to the Lean proof route. -/
theorem stronglyMeasurable_acorr {d : ℕ} (φ : SchwartzMap (Rd d) ℂ) :
    StronglyMeasurable (acorr φ) := by
  have hc : Continuous fun p : Rd d × Rd d => φ (p.1 + p.2) * (starRingEnd ℂ) (φ p.2) :=
    (φ.continuous.comp (continuous_fst.add continuous_snd)).mul
      (Complex.continuous_conj.comp (φ.continuous.comp continuous_snd))
  exact hc.stronglyMeasurable.integral_prod_right'

/-- Auxiliary to the Lean proof route: Schwartz decay, `(1+|z|)^k |φ(z)| ≤ B`. -/
theorem schwartz_bound {d : ℕ} (φ : SchwartzMap (Rd d) ℂ) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, (1 + ‖z‖) ^ k * ‖φ z‖ ≤ B := by
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) φ,
    by positivity, fun z => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl φ z
  rwa [norm_iteratedFDeriv_zero] at h

/-- Auxiliary to the Lean proof route: `(1+|y|)^k |φ(y)|` is integrable. -/
theorem integrable_weight {d : ℕ} (φ : SchwartzMap (Rd d) ℂ) (k : ℕ) :
    Integrable fun y : Rd d => (1 + ‖y‖) ^ k * ‖φ y‖ := by
  obtain ⟨B, -, hB⟩ := schwartz_bound φ (k + (d + 1))
  have hI : Integrable fun y : Rd d => B * (1 + ‖y‖) ^ (-((d + 1 : ℕ) : ℝ)) :=
    (integrable_one_add_norm (E := Rd d)
      (by rw [finrank_euclideanSpace_fin]; push_cast; linarith)).const_mul B
  refine hI.mono' (by fun_prop) (Eventually.of_forall fun y => ?_)
  have hy : 0 < 1 + ‖y‖ := by positivity
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg hy.le, Real.rpow_natCast]
  rw [le_mul_inv_iff₀ (by positivity)]
  calc (1 + ‖y‖) ^ k * ‖φ y‖ * (1 + ‖y‖) ^ (d + 1) = (1 + ‖y‖) ^ (k + (d + 1)) * ‖φ y‖ := by
        ring
    _ ≤ B := hB y

/-- Auxiliary to the Lean proof route: the autocorrelation of a Schwartz function decays
faster than every power, `|acorr φ(x)| ≤ C (1+|x|)^{-k}`. -/
theorem acorr_decay {d : ℕ} (φ : SchwartzMap (Rd d) ℂ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖acorr φ x‖ ≤ C * ((1 + ‖x‖) ^ k)⁻¹ := by
  obtain ⟨B, hB0, hB⟩ := schwartz_bound φ k
  set J := ∫ y, (1 + ‖y‖) ^ k * ‖φ y‖
  refine ⟨B * J, mul_nonneg hB0 (integral_nonneg fun y => by positivity), fun x => ?_⟩
  have hx : 0 < (1 + ‖x‖) ^ k := by positivity
  have hI := (integrable_weight φ k).const_mul (B * ((1 + ‖x‖) ^ k)⁻¹)
  have hle := norm_integral_le_of_norm_le (f := fun y => φ (x + y) * (starRingEnd ℂ) (φ y)) hI
    (Eventually.of_forall fun y => ?_)
  · rw [integral_const_mul] at hle
    unfold acorr
    refine hle.trans (le_of_eq ?_)
    ring
  · have hxy : 0 < (1 + ‖x + y‖) ^ k := by positivity
    have h1 : ‖φ (x + y)‖ ≤ B * ((1 + ‖x + y‖) ^ k)⁻¹ := by
      rw [le_mul_inv_iff₀ hxy, mul_comm]; exact hB _
    have h2 : (1 + ‖x‖) ^ k ≤ (1 + ‖x + y‖) ^ k * (1 + ‖y‖) ^ k := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ k
      have : ‖x‖ ≤ ‖x + y‖ + ‖y‖ := by
        calc ‖x‖ = ‖(x + y) - y‖ := by rw [add_sub_cancel_right]
          _ ≤ ‖x + y‖ + ‖y‖ := norm_sub_le _ _
      nlinarith [norm_nonneg (x + y), norm_nonneg y, mul_nonneg (norm_nonneg (x + y))
        (norm_nonneg y)]
    have h3 : ((1 + ‖x + y‖) ^ k)⁻¹ ≤ ((1 + ‖x‖) ^ k)⁻¹ * (1 + ‖y‖) ^ k := by
      rw [inv_le_iff_one_le_mul₀ hxy]
      calc (1 : ℝ) = ((1 + ‖x‖) ^ k)⁻¹ * (1 + ‖x‖) ^ k := by field_simp
        _ ≤ ((1 + ‖x‖) ^ k)⁻¹ * ((1 + ‖x + y‖) ^ k * (1 + ‖y‖) ^ k) := by gcongr
        _ = _ := by ring
    rw [norm_mul, Complex.norm_conj]
    calc ‖φ (x + y)‖ * ‖φ y‖ ≤ B * ((1 + ‖x + y‖) ^ k)⁻¹ * ‖φ y‖ := by gcongr
      _ ≤ B * (((1 + ‖x‖) ^ k)⁻¹ * (1 + ‖y‖) ^ k) * ‖φ y‖ := by gcongr
      _ = _ := by ring

/-- Auxiliary to the Lean proof route: the autocorrelation is bounded. -/
theorem acorr_bounded {d : ℕ} (φ : SchwartzMap (Rd d) ℂ) :
    ∃ M : ℝ, ∀ x, ‖acorr φ x‖ ≤ M := by
  obtain ⟨C, -, hC⟩ := acorr_decay φ 0
  exact ⟨C, fun x => by simpa using hC x⟩

/-! ### Gaussian positivity without Fourier transforms -/

/-- Auxiliary to the Lean proof route: the one-dimensional Gaussian autocorrelation,
`∫ e^{-2s(u+t)²} e^{-2st²} dt = √(π/(4s)) e^{-su²}` (used for `s > 0`). -/
theorem gauss_autocorr_one (s u : ℝ) :
    ∫ t : ℝ, Real.exp (-(2 * s) * (u + t) ^ 2) * Real.exp (-(2 * s) * t ^ 2) =
      √(π / (4 * s)) * Real.exp (-s * u ^ 2) := by
  have hpt : ∀ t : ℝ, Real.exp (-(2 * s) * (u + t) ^ 2) * Real.exp (-(2 * s) * t ^ 2) =
      Real.exp (-s * u ^ 2) * Real.exp (-(4 * s) * (t + u / 2) ^ 2) := by
    intro t
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [hpt]
  rw [integral_const_mul,
    integral_add_right_eq_self (fun t : ℝ => Real.exp (-(4 * s) * t ^ 2)) (u / 2),
    integral_gaussian, mul_comm]

/-- Auxiliary to the Lean proof route: for `s_j > 0`, `g_s` is a positive multiple of the
autocorrelation of `h = g_{2s}`: `∫ h(x + v) h(v) dv = P g_s(x)`, `P = ∏ √(π/(4 s_j))`
(positive when `s_j > 0`). -/
theorem gauss_autocorr {m : ℕ} (s : Fin m → ℝ) (x : Rd m) :
    ∫ v, gauss (fun j => 2 * s j) (x + v) * gauss (fun j => 2 * s j) v =
      (∏ j, √(π / (4 * s j))) * gauss s x := by
  have hpt : ∀ v : Rd m, gauss (fun j => 2 * s j) (x + v) * gauss (fun j => 2 * s j) v =
      ∏ j, (Real.exp (-(2 * s j) * (x j + v j) ^ 2) * Real.exp (-(2 * s j) * v j ^ 2)) := by
    intro v
    simp only [gauss, ← Finset.prod_mul_distrib, PiLp.add_apply]
  simp_rw [hpt]
  rw [integral_prod_coord (g := fun j t =>
    Real.exp (-(2 * s j) * (x j + t) ^ 2) * Real.exp (-(2 * s j) * t ^ 2))]
  simp only [gauss_autocorr_one, gauss, ← Finset.prod_mul_distrib]

/-- Auxiliary to the Lean proof route: the Gaussian form against a bounded strongly
measurable `F` is a nonnegative multiple of the double integral
`∫∫ h(a) h(b) F(a - b) da db`, `h = g_{2s}` (written over pairs `q = (b, a)`). -/
theorem gauss_form_eq {m : ℕ} {s : Fin m → ℝ} (hs : ∀ j, 0 < s j) (F : Rd m → ℂ)
    (hF : StronglyMeasurable F) {M : ℝ} (hM : ∀ x, ‖F x‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∫ x, (gauss s x : ℂ) * F x =
      (C : ℂ) * ∫ q : Rd m × Rd m, ((gauss (fun j => 2 * s j) q.2 *
        gauss (fun j => 2 * s j) q.1 : ℝ) : ℂ) * F (q.2 - q.1) := by
  set h := gauss (fun j => 2 * s j) with hh
  have h2s : ∀ j, 0 < 2 * s j := fun j => by linarith [hs j]
  have hI : Integrable h := integrable_gauss h2s
  have hhc : Continuous h := continuous_gauss _
  set P : ℝ := ∏ j, √(π / (4 * s j)) with hP
  have hP0 : 0 < P := Finset.prod_pos fun j _ => Real.sqrt_pos.2 (by have := hs j; positivity)
  -- the two integrable kernels
  set G : Rd m × Rd m → ℂ := fun q => ((h q.1 * h q.2 : ℝ) : ℂ) * F (q.1 - q.2) with hG
  have hGm : StronglyMeasurable G := by
    refine (Complex.continuous_ofReal.comp
      ((hhc.comp continuous_fst).mul (hhc.comp continuous_snd))).stronglyMeasurable.mul ?_
    exact hF.comp_measurable (measurable_fst.sub measurable_snd)
  have hGb : ∀ q, ‖G q‖ ≤ M * (h q.1 * h q.2) := by
    intro q
    simp only [hG, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (gauss_pos _ _).le, abs_of_nonneg (gauss_pos _ _).le, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM _) (mul_nonneg (gauss_pos _ _).le (gauss_pos _ _).le)
  have hGi : Integrable G (volume.prod volume) :=
    ((hI.mul_prod hI).const_mul M).mono' hGm.aestronglyMeasurable (Eventually.of_forall hGb)
  -- the sheared kernel
  have hKi : Integrable (fun p : Rd m × Rd m => ((h (p.1 + p.2) * h p.2 : ℝ) : ℂ) * F p.1)
      (volume.prod volume) := by
    have := (measurePreserving_add_prod (volume : Measure (Rd m)) volume
      ).integrable_comp_of_integrable hGi
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp [hG, Function.comp]
  refine ⟨P⁻¹, (inv_pos.2 hP0).le, ?_⟩
  have hpt : ∀ x, (gauss s x : ℂ) * F x =
      (P⁻¹ : ℂ) * ∫ v, ((h (x + v) * h v : ℝ) : ℂ) * F x := by
    intro x
    have h1 : gauss s x = P⁻¹ * ∫ v, h (x + v) * h v := by
      rw [hh, gauss_autocorr s x, ← hP]; field_simp
    rw [h1, integral_mul_const, integral_complex_ofReal]
    push_cast; ring
  simp_rw [hpt]
  rw [integral_const_mul, Complex.ofReal_inv]
  congr 1
  rw [integral_integral_swap hKi]
  have hin : ∀ v, ∫ x, ((h (x + v) * h v : ℝ) : ℂ) * F x =
      ∫ a, ((h v * h a : ℝ) : ℂ) * F (a - v) := by
    intro v
    rw [← integral_add_right_eq_self (fun a => ((h v * h a : ℝ) : ℂ) * F (a - v)) v]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [add_sub_cancel_right]
    push_cast; ring
  simp_rw [hin]
  have hGi' : Integrable (fun q : Rd m × Rd m => ((h q.2 * h q.1 : ℝ) : ℂ) * F (q.2 - q.1))
      (volume.prod volume) := by
    have := hGi.swap
    refine this.congr (Eventually.of_forall fun q => ?_)
    simp [hG, mul_comm]
  rw [Measure.volume_eq_prod, integral_prod _ hGi']
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  simp only
  push_cast; ring

/-- Auxiliary to the Lean proof route (the quadratic form of a measure autocorrelation): for
`h ≥ 0` integrable and continuous, a linear isometry `ι` and Schwartz `φ`,
`∫∫ h(a) h(b) acorr φ(ι a - ι b) da db = ∫ |∫ h(a) φ(ι a + w) da|² dw` is a nonnegative real.
For `ι` the plane embedding this is the TeX's tangential form integrated in `z` (lines
7368-7373). -/
theorem autocorr_form_nnr {m d : ℕ} (ι : Rd m →ₗᵢ[ℝ] Rd d) (φ : SchwartzMap (Rd d) ℂ)
    {h : Rd m → ℝ} (hI : Integrable h) (hhc : Continuous h) (h0 : ∀ a, 0 ≤ h a) :
    NNR (∫ q : Rd m × Rd m, ((h q.2 * h q.1 : ℝ) : ℂ) * acorr φ (ι q.2 - ι q.1)) := by
  obtain ⟨B, hB0, hB⟩ := schwartz_bound φ 0
  simp only [pow_zero, one_mul] at hB
  have hφI : Integrable (fun w : Rd d => ‖φ w‖) := φ.integrable.norm
  set K : (Rd m × Rd m) × Rd d → ℂ := fun r =>
    ((h r.1.2 * h r.1.1 : ℝ) : ℂ) * (φ (ι r.1.2 + r.2) * (starRingEnd ℂ) (φ (ι r.1.1 + r.2)))
    with hK
  have hιc : Continuous ι := ι.continuous
  have hKc : Continuous K := by
    refine (Complex.continuous_ofReal.comp ((hhc.comp (continuous_snd.comp continuous_fst)).mul
      (hhc.comp (continuous_fst.comp continuous_fst)))).mul ?_
    refine (φ.continuous.comp ((hιc.comp (continuous_snd.comp continuous_fst)).add
      continuous_snd)).mul (Complex.continuous_conj.comp (φ.continuous.comp
      ((hιc.comp (continuous_fst.comp continuous_fst)).add continuous_snd)))
  have hKb : ∀ r, ‖K r‖ ≤ B * (h r.1.2 * h r.1.1) * ‖φ (ι r.1.2 + r.2)‖ := by
    intro r
    simp only [hK, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
    rw [abs_of_nonneg (h0 _), abs_of_nonneg (h0 _)]
    have := hB (ι r.1.1 + r.2)
    have hn := norm_nonneg (φ (ι r.1.2 + r.2))
    have hh := mul_nonneg (h0 r.1.2) (h0 r.1.1)
    calc h r.1.2 * h r.1.1 * (‖φ (ι r.1.2 + r.2)‖ * ‖φ (ι r.1.1 + r.2)‖)
        ≤ h r.1.2 * h r.1.1 * (‖φ (ι r.1.2 + r.2)‖ * B) := by gcongr
      _ = _ := by ring
  have hKi : Integrable K ((volume.prod volume).prod volume) := by
    rw [integrable_prod_iff hKc.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun p => ?_, ?_⟩
    · refine ((φ.integrable.norm.comp_add_left (ι p.2)).const_mul
        (B * (h p.2 * h p.1))).mono' (hKc.comp (continuous_const.prodMk
        continuous_id)).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
      exact hKb (p, w)
    · have hb : Integrable (fun p : Rd m × Rd m => B * (∫ w, ‖φ w‖) * (h p.2 * h p.1))
          (volume.prod volume) := by
        have := (hI.mul_prod hI).const_mul (B * ∫ w, ‖φ w‖)
        refine this.congr (Eventually.of_forall fun p => ?_)
        simp only; ring
      refine hb.mono' hKc.aestronglyMeasurable.norm.integral_prod_right'
        (Eventually.of_forall fun p => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun w => norm_nonneg _)]
      have hint : Integrable (fun w => B * (h p.2 * h p.1) * ‖φ (ι p.2 + w)‖) :=
        (φ.integrable.norm.comp_add_left (ι p.2)).const_mul _
      calc ∫ w, ‖K (p, w)‖ ≤ ∫ w, B * (h p.2 * h p.1) * ‖φ (ι p.2 + w)‖ :=
            integral_mono_of_nonneg (Eventually.of_forall fun w => norm_nonneg _) hint
              (Eventually.of_forall fun w => hKb (p, w))
        _ = B * (∫ w, ‖φ w‖) * (h p.2 * h p.1) := by
            rw [integral_const_mul,
              integral_add_left_eq_self (fun w => ‖φ w‖) (ι p.2)]
            ring
  -- rewrite the autocorrelation by the translation `y = w + ι b`
  have hpt : ∀ q : Rd m × Rd m, ((h q.2 * h q.1 : ℝ) : ℂ) * acorr φ (ι q.2 - ι q.1) =
      ∫ w, K (q, w) := by
    intro q
    unfold acorr
    rw [← integral_add_right_eq_self
      (fun y => φ (ι q.2 - ι q.1 + y) * (starRingEnd ℂ) (φ y)) (ι q.1), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [hK]
    rw [show ι q.2 - ι q.1 + (w + ι q.1) = ι q.2 + w by abel, add_comm w (ι q.1)]
  simp_rw [hpt]
  rw [Measure.volume_eq_prod, integral_integral_swap (f := fun q w => K (q, w)) hKi]
  refine nnr_integral (Eventually.of_forall fun w => ?_)
  set Ψ : ℂ := ∫ a, (h a : ℂ) * φ (ι a + w) with hΨ
  have hu : Integrable fun a => (h a : ℂ) * φ (ι a + w) := by
    refine (hI.const_mul B).mono' ((Complex.continuous_ofReal.comp hhc).mul
      (φ.continuous.comp (hιc.add continuous_const))).aestronglyMeasurable
      (Eventually.of_forall fun a => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h0 a), mul_comm B]
    exact mul_le_mul_of_nonneg_left (hB _) (h0 a)
  have hsplit : ∀ q : Rd m × Rd m, K (q, w) =
      (starRingEnd ℂ) ((h q.1 : ℂ) * φ (ι q.1 + w)) * ((h q.2 : ℂ) * φ (ι q.2 + w)) := by
    intro q
    simp only [hK, map_mul, Complex.conj_ofReal]
    push_cast; ring
  simp_rw [hsplit]
  rw [integral_prod_mul (fun b => (starRingEnd ℂ) ((h b : ℂ) * φ (ι b + w)))
    (fun a => (h a : ℂ) * φ (ι a + w)), integral_conj, ← hΨ, ← Complex.normSq_eq_conj_mul_self]
  exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact Complex.normSq_nonneg _⟩

/-! ### Mixtures: Fubini over the mixing measure and the limit `δ → 0` -/

/-- Auxiliary to the Lean proof route (the mixture step, main TeX lines 7261-7264, 7379-7382,
7979-7980, with the damping `e^{-δ|x|²}` and `δ → 0` added for the degenerate Gaussians): let
`ν` be an s-finite mixing measure carried by `s ≥ 0` and `f(x) = ∫ g_s(x) ν(ds)` a.e.  If
`∫ f |F| < ∞` and every nondegenerate Gaussian form `∫ g_s F` (`s_j > 0`) is a nonnegative
real, then so is `∫ f F`. -/
theorem nnr_of_mixture {m : ℕ} (ν : Measure (Fin m → ℝ)) [SFinite ν]
    (hν : ∀ᵐ s ∂ν, ∀ j, 0 ≤ s j) {f : Rd m → ℝ≥0∞} (hfm : Measurable f)
    (hf : ∀ᵐ x, f x = ∫⁻ s, ENNReal.ofReal (gauss s x) ∂ν) {F : Rd m → ℂ}
    (hF : AEStronglyMeasurable F) (hint : ∫⁻ x, f x * ‖F x‖ₑ < ∞)
    (hpos : ∀ s : Fin m → ℝ, (∀ j, 0 < s j) → NNR (∫ x, (gauss s x : ℂ) * F x)) :
    NNR (∫ x, ((f x).toReal : ℂ) * F x) := by
  have hgx : ∀ x : Rd m, Measurable fun s : Fin m → ℝ => gauss s x := fun x =>
    (continuous_gauss_joint.comp (continuous_const.prodMk continuous_id)).measurable
  -- the damped forms
  have hdamp : ∀ δ : ℝ, 0 < δ →
      NNR (∫ x, (((f x).toReal * gauss (fun _ => δ) x : ℝ) : ℂ) * F x) := by
    intro δ hδ
    set G : Rd m × (Fin m → ℝ) → ℂ := fun p => (gauss (p.2 + fun _ => δ) p.1 : ℂ) * F p.1
      with hG
    have hgc : Continuous fun p : Rd m × (Fin m → ℝ) => gauss (p.2 + fun _ => δ) p.1 :=
      continuous_gauss_joint.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))
    have hGm : AEStronglyMeasurable G (volume.prod ν) :=
      (Complex.continuous_ofReal.comp hgc).aestronglyMeasurable.mul hF.comp_fst
    have hGi : Integrable G (volume.prod ν) := by
      refine ⟨hGm, ?_⟩
      unfold HasFiniteIntegral
      rw [lintegral_prod _ hGm.enorm]
      refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint
      filter_upwards [hf] with x hx
      calc ∫⁻ s, ‖G (x, s)‖ₑ ∂ν ≤ ∫⁻ s, ENNReal.ofReal (gauss s x) * ‖F x‖ₑ ∂ν := by
            refine lintegral_mono fun s => ?_
            simp only [hG, enorm_mul]
            gcongr
            rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (gauss_pos _ _).le]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [gauss_add]
            exact mul_le_of_le_one_right (gauss_pos _ _).le (gauss_le_one (fun _ => hδ.le) x)
        _ = f x * ‖F x‖ₑ := by
            rw [lintegral_mul_const _ (hgx x).ennreal_ofReal, hx]
    have hswap := integral_integral_swap (f := fun x s => G (x, s)) hGi
    have hleft : ∀ᵐ x, ∫ s, G (x, s) ∂ν =
        (((f x).toReal * gauss (fun _ => δ) x : ℝ) : ℂ) * F x := by
      filter_upwards [hf] with x hx
      have hreal : ∫ s, gauss (s + fun _ => δ) x ∂ν = (f x).toReal * gauss (fun _ => δ) x := by
        simp_rw [gauss_add]
        rw [integral_mul_const, integral_eq_lintegral_of_nonneg_ae
          (ae_of_all _ fun s => (gauss_pos _ _).le) (hgx x).aestronglyMeasurable, ← hx]
      simp only [hG]
      rw [integral_mul_const, integral_complex_ofReal, hreal]
    have hright : ∀ᵐ s ∂ν, NNR (∫ x, G (x, s)) := by
      filter_upwards [hν] with s hs
      exact hpos (s + fun _ => δ) fun j => show 0 < s j + δ by linarith [hs j]
    have h := nnr_integral hright
    rw [← hswap, integral_congr_ae hleft] at h
    exact h
  -- the limit `δ → 0`
  set δk : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hδk
  have hδpos : ∀ k, 0 < δk k := fun k => by positivity
  have hD : ∀ x : Rd m, Tendsto (fun k => gauss (fun _ => δk k) x) atTop (𝓝 1) := by
    intro x
    have hc : Continuous fun δ : ℝ => gauss (fun _ => δ) x :=
      continuous_gauss_joint.comp (continuous_const.prodMk (continuous_pi fun _ => continuous_id))
    have h0 : gauss (fun _ => (0 : ℝ)) x = 1 := by simp [gauss]
    have := (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    rwa [h0] at this
  have hlim : Tendsto (fun k => ∫ x, (((f x).toReal * gauss (fun _ => δk k) x : ℝ) : ℂ) * F x)
      atTop (𝓝 (∫ x, ((f x).toReal : ℂ) * F x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (f x).toReal * ‖F x‖)
      (fun k => ?_) ?_ (fun k => ?_) ?_
    · exact (Complex.continuous_ofReal.measurable.comp (hfm.ennreal_toReal.mul
        (continuous_gauss _).measurable)).aestronglyMeasurable.mul hF
    · refine ⟨hfm.ennreal_toReal.aestronglyMeasurable.mul hF.norm, ?_⟩
      unfold HasFiniteIntegral
      refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hint
      rw [enorm_mul, enorm_norm, Real.enorm_of_nonneg ENNReal.toReal_nonneg]
      gcongr
      exact ENNReal.ofReal_toReal_le
    · refine Eventually.of_forall fun x => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
        (mul_nonneg ENNReal.toReal_nonneg (gauss_pos _ _).le)]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right ENNReal.toReal_nonneg
        (gauss_le_one (fun _ => (hδpos k).le) x)) (norm_nonneg _)
    · refine Eventually.of_forall fun x => ?_
      have := ((Complex.continuous_ofReal.tendsto _).comp
        ((tendsto_const_nhds (x := (f x).toReal)).mul (hD x))).mul_const (F x)
      simpa using this
  exact nnr_of_tendsto hlim fun k => hdamp _ (hδpos k)

/-! ### The one-dimensional mixing measures -/

/-- The mixing measure of `|u|^{-e}` (main TeX lines 7255-7258, 7361-7364, 7975-7978):
`Γ(e/2)^{-1} s^{e/2-1} ds` on `(0, ∞)` for `e ≠ 0`, and the Dirac measure at `0` for `e = 0`
(the constant one, with no Gamma factor; TeX line 7265). -/
def mixOne (e : ℝ) : Measure ℝ :=
  if e = 0 then Measure.dirac 0 else
    (volume.restrict (Ioi (0 : ℝ))).withDensity fun s =>
      ENNReal.ofReal (s ^ (e / 2 - 1) / Real.Gamma (e / 2))

/-- Auxiliary to the Lean proof route. -/
instance mixOne_sigmaFinite (e : ℝ) : SigmaFinite (mixOne e) := by
  unfold mixOne; split_ifs <;> infer_instance

/-- Auxiliary to the Lean proof route: the mixing measure is carried by `s ≥ 0`. -/
theorem mixOne_nonneg (e : ℝ) : ∀ᵐ s ∂mixOne e, 0 ≤ s := by
  unfold mixOne
  split_ifs
  · exact (ae_dirac_iff (measurableSet_le measurable_const measurable_id)).2 le_rfl
  · refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs using le_of_lt hs

/-- The Gaussian mixture `|u|^{-e} = Γ(e/2)^{-1} ∫_0^∞ s^{e/2-1} e^{-su²} ds` for `e > 0`,
`u ≠ 0` (main TeX lines 7255-7258), and `|u|^0 = 1` for `e = 0`; with integrability. -/
theorem mixOne_spec {e : ℝ} (he : 0 ≤ e) {u : ℝ} (hu : u ≠ 0) :
    Integrable (fun s => Real.exp (-s * u ^ 2)) (mixOne e) ∧
      ∫ s, Real.exp (-s * u ^ 2) ∂mixOne e = |u| ^ (-e) := by
  have hval : ∫ s, Real.exp (-s * u ^ 2) ∂mixOne e = |u| ^ (-e) := by
    unfold mixOne
    split_ifs with h0
    · subst h0; simp
    · have hepos : 0 < e := lt_of_le_of_ne he (Ne.symm h0)
      have hG : 0 < Real.Gamma (e / 2) := Real.Gamma_pos_of_pos (by linarith)
      have hu2 : 0 < u ^ 2 := by positivity
      rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      have hcongr : ∫ s in Ioi 0, (ENNReal.ofReal (s ^ (e / 2 - 1) / Real.Gamma (e / 2))).toReal •
          Real.exp (-s * u ^ 2) =
          ∫ s in Ioi 0, s ^ (e / 2 - 1) * Real.exp (-(u ^ 2 * s)) / Real.Gamma (e / 2) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
        rw [ENNReal.toReal_ofReal (div_nonneg (Real.rpow_nonneg (le_of_lt hs) _) hG.le),
          smul_eq_mul, show -s * u ^ 2 = -(u ^ 2 * s) by ring]
        ring
      rw [hcongr, integral_div, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hu2,
        mul_div_assoc, div_self hG.ne', mul_one, ← sq_abs u, one_div,
        Real.inv_rpow (by positivity), Real.rpow_neg (abs_nonneg u)]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg u)]
      ring_nf
  refine ⟨Integrable.of_integral_ne_zero ?_, hval⟩
  rw [hval]
  exact (Real.rpow_pos_of_pos (abs_pos.2 hu) _).ne'

/-- Auxiliary to the Lean proof route: the product mixing measure is carried by `s ≥ 0`. -/
theorem piMix_nonneg {m : ℕ} (c : ℝ≥0∞) (e : Fin m → ℝ) :
    ∀ᵐ s ∂(c • Measure.pi fun j => mixOne (e j)), ∀ j, 0 ≤ s j :=
  Measure.ae_smul_measure (ae_all_iff.2 fun j =>
    (Measure.tendsto_eval_ae_ae (μ := fun j => mixOne (e j)) (i := j)).eventually
      (mixOne_nonneg (e j))) c

/-- Auxiliary to the Lean proof route: the coordinate hyperplanes are Lebesgue-null. -/
theorem ae_coord_ne {m : ℕ} : ∀ᵐ x : Rd m, ∀ j, x j ≠ 0 := by
  rw [ae_all_iff]
  intro j
  set L : Rd m →ₗ[ℝ] ℝ := ContinuousLinearMap.toLinearMap (EuclideanSpace.proj j)
  have hker : LinearMap.ker L ≠ ⊤ := by
    intro h
    have hmem : EuclideanSpace.single j (1 : ℝ) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
    simp [L] at hmem
  have h0 := Measure.addHaar_submodule (volume : Measure (Rd m)) _ hker
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) h0
  simp only [Set.mem_ofPred_eq, not_not] at hx
  simp [L, hx]

/-- The product mixture (main TeX lines 7258-7260): off the coordinate hyperplanes,
`∏_j |x_j|^{-e_j} = ∫ g_s(x) ν_e(ds)` with `ν_e = ⊗_j mixOne e_j` (`e_j ≥ 0`). -/
theorem prod_mixture {m : ℕ} {e : Fin m → ℝ} (he : ∀ j, 0 ≤ e j) {x : Rd m}
    (hx : ∀ j, x j ≠ 0) :
    ENNReal.ofReal (∏ j, |x j| ^ (-e j)) =
      ∫⁻ s, ENNReal.ofReal (gauss s x) ∂(Measure.pi fun j => mixOne (e j)) := by
  have hI : Integrable (fun s : Fin m → ℝ => gauss s x) (Measure.pi fun j => mixOne (e j)) :=
    Integrable.fintype_prod (f := fun j t => Real.exp (-t * x j ^ 2))
      fun j => (mixOne_spec (he j) (hx j)).1
  have hv : ∫ s, gauss s x ∂(Measure.pi fun j => mixOne (e j)) = ∏ j, |x j| ^ (-e j) := by
    rw [show (fun s : Fin m → ℝ => gauss s x) = fun s => ∏ j, Real.exp (-s j * x j ^ 2) from rfl,
      integral_fintype_prod_eq_prod (f := fun j t => Real.exp (-t * x j ^ 2))]
    exact Finset.prod_congr rfl fun j _ => (mixOne_spec (he j) (hx j)).2
  rw [← hv, ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun s => (gauss_pos s x).le)]

/-- The product density is a Gaussian mixture a.e.: `c ∏_j |x_j|^{-e_j} = ∫ g_s(x) ν(ds)`,
`ν = c ⊗_j mixOne e_j`. -/
theorem prodRiesz_mixture {m : ℕ} {c : ℝ} (hc : 0 ≤ c) {e : Fin m → ℝ} (he : ∀ j, 0 ≤ e j) :
    ∀ᵐ x : Rd m, prodRiesz c e x = ∫⁻ s, ENNReal.ofReal (gauss s x)
      ∂(ENNReal.ofReal c • Measure.pi fun j => mixOne (e j)) := by
  filter_upwards [ae_coord_ne] with x hx
  rw [lintegral_smul_measure, ← prod_mixture he hx, prodRiesz, prodRieszReal,
    ENNReal.ofReal_mul hc, smul_eq_mul]

/-- The isotropic mixture (main TeX lines 7975-7978): for `x ≠ 0` and `e > 0`,
`c|x|^{-e} = ∫ g_s(x) ν(ds)`, `ν = c (t ↦ (t, t, t))_* mixOne e`. -/
theorem riesz_mixture {c e : ℝ} (hc : 0 ≤ c) (he : 0 < e) :
    ∀ᵐ x : Rd 3, HigherRieszTwo.riesz c e x = ∫⁻ s, ENNReal.ofReal (gauss s x)
      ∂(ENNReal.ofReal c • (mixOne e).map fun t => fun _ : Fin 3 => t) := by
  have hnull : ∀ᵐ x : Rd 3, x ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [hnull] with x hx
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  obtain ⟨hI, hv⟩ := mixOne_spec he.le hn
  have hg : ∀ t : ℝ, gauss (fun _ : Fin 3 => t) x = Real.exp (-t * ‖x‖ ^ 2) := by
    intro t
    simp only [gauss]
    rw [← Real.exp_sum, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  have hm : Measurable fun s : Fin 3 → ℝ => ENNReal.ofReal (gauss s x) :=
    ENNReal.measurable_ofReal.comp
      (continuous_gauss_joint.comp (continuous_const.prodMk continuous_id)).measurable
  have hmap : Measurable fun t : ℝ => fun _ : Fin 3 => t :=
    (continuous_pi fun _ => continuous_id).measurable
  rw [lintegral_smul_measure, lintegral_map hm hmap]
  simp_rw [hg]
  rw [← ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ fun _ => (Real.exp_pos _).le), hv,
    abs_norm, HigherRieszTwo.riesz, ENNReal.ofReal_mul hc, smul_eq_mul]

/-! ### Positive definiteness -/

/-- Positive definiteness of a Gaussian mixture (the common core of main TeX lines 7251-7265,
7353-7384, 7975-7980): for a linear isometry `ι : ℝ^m → ℝ^d`, a mixture density
`f = ∫ g_s ν(ds)` (a.e., `ν` carried by `s ≥ 0`), finite and tempered, the image
`ι_*(f dx)` is positive definite. -/
theorem posdef_of_mixture {m d : ℕ} (ι : Rd m →ₗᵢ[ℝ] Rd d) (ν : Measure (Fin m → ℝ))
    [SFinite ν] (hν : ∀ᵐ s ∂ν, ∀ j, 0 ≤ s j) {f : Rd m → ℝ≥0∞} (hfm : Measurable f)
    (hfin : ∀ x, f x < ∞) (hf : ∀ᵐ x, f x = ∫⁻ s, ENNReal.ofReal (gauss s x) ∂ν)
    (ht : IsTempered ((volume : Measure (Rd m)).withDensity f)) :
    IsPosDefDistr (((volume : Measure (Rd m)).withDensity f).map ι) := by
  intro φ
  have hemb : MeasurableEmbedding (ι : Rd m → Rd d) :=
    ι.isometry.isClosedEmbedding.measurableEmbedding
  obtain ⟨k, hk⟩ := ht
  obtain ⟨C, hC0, hC⟩ := acorr_decay φ k
  obtain ⟨M, hM⟩ := acorr_bounded φ
  have hFm : StronglyMeasurable fun x => acorr φ (ι x) :=
    (stronglyMeasurable_acorr φ).comp_measurable ι.continuous.measurable
  have hgk : Measurable fun x : Rd m => ENNReal.ofReal ((1 + ‖x‖) ^ (-(k : ℝ))) := by fun_prop
  have key : NNR (∫ x, ((f x).toReal : ℂ) * acorr φ (ι x)) := by
    refine nnr_of_mixture ν hν hfm hf hFm.aestronglyMeasurable ?_ ?_
    · have hk' : ∫⁻ x, f x * ENNReal.ofReal ((1 + ‖x‖) ^ (-(k : ℝ))) < ∞ := by
        rw [lintegral_withDensity_eq_lintegral_mul _ hfm hgk] at hk
        exact hk
      calc ∫⁻ x, f x * ‖acorr φ (ι x)‖ₑ
          ≤ ∫⁻ x, ENNReal.ofReal C * (f x * ENNReal.ofReal ((1 + ‖x‖) ^ (-(k : ℝ)))) := by
            refine lintegral_mono fun x => ?_
            have h1 : ‖acorr φ (ι x)‖ₑ ≤
                ENNReal.ofReal C * ENNReal.ofReal ((1 + ‖x‖) ^ (-(k : ℝ))) := by
              rw [← ENNReal.ofReal_mul hC0, ← ofReal_norm]
              refine ENNReal.ofReal_le_ofReal ?_
              rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
              simpa [LinearIsometry.norm_map] using hC (ι x)
            calc f x * ‖acorr φ (ι x)‖ₑ
                ≤ f x * (ENNReal.ofReal C * ENNReal.ofReal ((1 + ‖x‖) ^ (-(k : ℝ)))) := by
                  gcongr
              _ = _ := by ring
        _ = ENNReal.ofReal C * ∫⁻ x, f x * ENNReal.ofReal ((1 + ‖x‖) ^ (-(k : ℝ))) :=
            lintegral_const_mul _ (hfm.mul hgk)
        _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hk'
    · intro s hs
      obtain ⟨C', hC', heq⟩ := gauss_form_eq hs _ hFm (fun x => hM (ι x))
      rw [heq]
      refine nnr_ofReal_mul hC' ?_
      simp only [map_sub]
      exact autocorr_form_nnr ι φ (integrable_gauss fun j => by linarith [hs j])
        (continuous_gauss _) fun a => (gauss_pos _ _).le
  show NNR _
  rw [hemb.integral_map, integral_withDensity_eq_integral_toReal_smul hfm (ae_of_all _ hfin)]
  simp_rw [Complex.real_smul]
  exact key

/-- Positive definiteness of the image of a product Riesz measure under a linear isometry
(`c ≥ 0`, `0 ≤ e_j < 1`). -/
theorem prodRieszMeasure_map_posdef {m d : ℕ} (ι : Rd m →ₗᵢ[ℝ] Rd d) {c : ℝ} (hc : 0 ≤ c)
    {e : Fin m → ℝ} (he : ∀ j, 0 ≤ e j ∧ e j < 1) :
    IsPosDefDistr ((prodRieszMeasure c e).map ι) :=
  posdef_of_mixture ι _ (piMix_nonneg _ e) (measurable_prodRiesz c e)
    (fun _ => ENNReal.ofReal_lt_top) (prodRiesz_mixture hc fun j => (he j).1)
    (prodRieszMeasure_tempered hc he)

/-- **`RieszProductPD` proved** (main TeX lines 7251-7265): `c ∏_j |x_j|^{-e_j} dx` on `ℝ³` is
positive definite for `c ≥ 0`, `0 ≤ e_j < 1`. -/
theorem rieszProductPD_proved : RieszProductPD := by
  intro c e hc he
  have h := prodRieszMeasure_map_posdef (LinearIsometry.id : Rd 3 →ₗᵢ[ℝ] Rd 3) hc he
  rwa [LinearIsometry.coe_id, Measure.map_id] at h

/-- **`PlaneRieszPD` proved** (main TeX lines 7353-7384, including the low endpoint `e = 0`):
`c ∏_j |y_j|^{-e_j} dy δ₀(dz)` on `ℝ³` is positive definite for `c ≥ 0`, `0 ≤ e_j < 1`. -/
theorem planeRieszPD_proved : PlaneRieszPD := fun _ _ hc he =>
  prodRieszMeasure_map_posdef planeEmb hc he

/-- **`RieszIsoPD` proved** (main TeX lines 7975-7980): `c|x|^{-e} dx` on `ℝ³` is positive
definite for `c ≥ 0`, `0 < e < 3`. -/
theorem rieszIsoPD_proved : RieszIsoPD := by
  intro c e hc he0 he3
  have hν : ∀ᵐ s ∂(ENNReal.ofReal c • (mixOne e).map fun t => fun _ : Fin 3 => t),
      ∀ j, 0 ≤ s j := by
    refine Measure.ae_smul_measure ?_ _
    have hmeas : Measurable fun t : ℝ => fun _ : Fin 3 => t :=
      (continuous_pi fun _ => continuous_id).measurable
    have hset : MeasurableSet {s : Fin 3 → ℝ | ∀ j, 0 ≤ s j} := by
      rw [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => measurableSet_le measurable_const (measurable_pi_apply j)
    rw [ae_map_iff hmeas.aemeasurable hset]
    filter_upwards [mixOne_nonneg e] with t ht using fun _ => ht
  have h := posdef_of_mixture (LinearIsometry.id : Rd 3 →ₗᵢ[ℝ] Rd 3) _ hν
    (HigherRieszTwo.measurable_riesz c e) (fun _ => ENNReal.ofReal_lt_top) (riesz_mixture hc he0)
    (riesz_props hc he0 he3).2.2.1
  rwa [LinearIsometry.coe_id, Measure.map_id] at h

/-! ### The wrappers without the discharged inputs -/

/-- `L:product-endpoints` (main TeX lines 7170-7204; proof 7206-7280), all conclusions of
`EndpointLemmas.product_endpoints_paper`, with the manuscript's hypotheses only: the input
`RieszProductPD` is discharged by `rieszProductPD_proved`.  Whole. -/
theorem product_endpoints_paper_proved {a : Fin 3 → ℝ} {θ c : ℝ}
    (ha0 : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j < 1) (hα1 : 1 < ∑ j, a j) (hα2 : ∑ j, a j < 2)
    (hθ0 : 0 < θ) (hθ : θ < 2 - ∑ j, a j) (hc : 0 < c) :
    ((0 < lam θ a ∧ lam θ a < 1) ∧ ∑ j, bVec θ a j = 1 ∧
      ∑ j, vVec θ a j = chi (∑ j, a j) θ ∧
      (∀ j, a j = θ * bVec θ a j + (1 - θ) * vVec θ a j) ∧
      (∀ j, 0 < a j → (0 < bVec θ a j ∧ bVec θ a j < 1) ∧
        (0 < vVec θ a j ∧ vVec θ a j < 1)) ∧
      (∀ j, a j = 0 → bVec θ a j = 0 ∧ vVec θ a j = 0)) ∧
    ((IsCov (prodRieszMeasure c a) ∧ LocallyIntegrable (prodRieszReal c a) ∧
        Scaling (prodRieszMeasure c a) (3 - ∑ j, a j)) ∧
      (IsCov (prodRieszMeasure c (bVec θ a)) ∧ LocallyIntegrable (prodRieszReal c (bVec θ a)) ∧
        Scaling (prodRieszMeasure c (bVec θ a)) 2) ∧
      (IsCov (prodRieszMeasure c (vVec θ a)) ∧ LocallyIntegrable (prodRieszReal c (vVec θ a)) ∧
        Scaling (prodRieszMeasure c (vVec θ a)) (3 - chi (∑ j, a j) θ)) ∧
      (∑ j, a j < chi (∑ j, a j) θ ∧ chi (∑ j, a j) θ < 2)) ∧
    GaussComparison θ (prodRieszMeasure c a) (prodRieszMeasure c (bVec θ a))
      (prodRieszMeasure c (vVec θ a)) ∧
    EndpointPair θ (chi (∑ j, a j) θ) (prodRieszMeasure c a) (prodRieszMeasure c (bVec θ a))
      (prodRieszMeasure c (vVec θ a)) :=
  product_endpoints_paper rieszProductPD_proved ha0 ha1 hα1 hα2 hθ0 hθ hc

/-- `L:plane-endpoints` (main TeX lines 7316-7332; proof 7334-7415), all conclusions of
`EndpointLemmas.plane_endpoints_paper`, with the manuscript's hypotheses only: the input
`PlaneRieszPD` is discharged by `planeRieszPD_proved`.  Whole.  Carried but unused, as in the
original: `α₀ < 1` and `α < 2 - α₀`. -/
theorem plane_endpoints_paper_proved {α₀ α θ c : ℝ} {a : Fin 2 → ℝ}
    (hα₀ : 0 < α₀) (hα₀1 : α₀ < 1) (hα1 : 1 < α) (hα2 : α < 2 - α₀) (hθ0 : α₀ < θ)
    (hθ : θ < 2 - α) (hc : 0 < c) (ha : ∀ j, 0 ≤ a j) (hs : a 0 + a 1 = α - 1) :
    ((∀ j, 0 ≤ a j ∧ a j < 1) ∧ (∀ j, 0 ≤ a j / (1 - θ) ∧ a j / (1 - θ) < 1) ∧
      a 0 / (1 - θ) + a 1 / (1 - θ) = chi α θ - 1 ∧ chi α θ - 1 < 1) ∧
    (IsCov (planeMeasure c a) ∧ Scaling (planeMeasure c a) (3 - α)) ∧
    EndpointPair θ (chi α θ) (planeMeasure c a) (planeMeasure c 0)
      (planeMeasure c fun j => a j / (1 - θ)) ∧
    planeMeasure c 0 = ENNReal.ofReal c • (volume : Measure (Rd 2)).map planeEmb ∧
    (HomogHypothesis.IsSpectralMeasure (planeMeasure c 0) (planeLowSpectral c) ∧
      planeLowSpectral c (Metric.closedBall 0 1) = ENNReal.ofReal (c / π) ∧
      planeLowSpectral c (Metric.ball 0 1) = ENNReal.ofReal (c / π) ∧
      π * (c / π) / 2 = c / 2) :=
  plane_endpoints_paper planeRieszPD_proved hα₀ hα₀1 hα1 hα2 hθ0 hθ hc ha hs

/-- `C:three-product-riesz` (main TeX lines 7944-7959), as
`EndpointCorollaries.three_product_riesz_paper` without the inputs `RieszProductPD` and
`RieszIsoPD` (discharged here).  NARROWER as the original: the moment statements concern the
abstract `ThreeMomentModel` and rest on the supplied input `ThreeTransfer`. -/
theorem three_product_riesz_paper_proved (Mdl : ThreeMomentModel) {α₀ α c : ℝ}
    (hT : ThreeTransfer Mdl α₀ (midTheta α₀ α))
    (hα₀ : 0 < α₀) (hα₀1 : α₀ < 1) (hα1 : 1 < α) (hα2 : α < 2 - α₀) (hc : 0 < c) :
    (∀ a : Fin 3 → ℝ, (∀ j, 0 ≤ a j ∧ a j < 1) → ∑ j, a j = α →
      TransferConclusion Mdl α₀ α (midTheta α₀ α) (prodRieszMeasure c a)
        (prodRieszMeasure c (bVec (midTheta α₀ α) a))
        (prodRieszMeasure c (vVec (midTheta α₀ α) a))) ∧
    TransferConclusion Mdl α₀ α (midTheta α₀ α) (rieszMeasure c α) (rieszMeasure c 1)
      (rieszMeasure c (chi α (midTheta α₀ α))) :=
  three_product_riesz_paper rieszProductPD_proved rieszIsoPD_proved Mdl hT hα₀ hα₀1 hα1 hα2 hc

/-- `C:three-finite-images` (main TeX lines 7991-8010), as
`EndpointCorollaries.three_finite_images_paper` without the inputs `RieszProductPD`,
`RieszIsoPD` and `PlaneRieszPD` (discharged here).  NARROWER as the original
(`ThreeTransfer` supplied, abstract `ThreeMomentModel`). -/
theorem three_finite_images_paper_proved (Mdl : ThreeMomentModel) {α₀ α : ℝ}
    (hT : ThreeTransfer Mdl α₀ (midTheta α₀ α)) (hα₀ : 0 < α₀) (hα₀1 : α₀ < 1) (hα1 : 1 < α)
    (hα2 : α < 2 - α₀) {N : ℕ} (X : Fin N → Component) (hX : ∀ i, (X i).Valid α)
    (T : Fin N → Rd 3 ≃L[ℝ] Rd 3) {w : Fin N → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hwpos : 0 < ∑ i, w i) :
    (IsCov (wsum w fun i => ((X i).meas α).map (T i)) ∧
      Scaling (wsum w fun i => ((X i).meas α).map (T i)) (3 - α) ∧
      (wsum w fun i => ((X i).meas α).map (T i)) ≠ 0) ∧
    EndpointPair (midTheta α₀ α) (chi α (midTheta α₀ α))
      (wsum w fun i => ((X i).meas α).map (T i))
      (wsum w fun i => ((X i).low (midTheta α₀ α)).map (T i))
      (wsum w fun i => ((X i).st α (midTheta α₀ α)).map (T i)) ∧
    TransferConclusion Mdl α₀ α (midTheta α₀ α)
      (wsum w fun i => ((X i).meas α).map (T i))
      (wsum w fun i => ((X i).low (midTheta α₀ α)).map (T i))
      (wsum w fun i => ((X i).st α (midTheta α₀ α)).map (T i)) :=
  three_finite_images_paper rieszProductPD_proved rieszIsoPD_proved planeRieszPD_proved Mdl hT
    hα₀ hα₀1 hα1 hα2 X hX T hw hwpos

end StratonovichHAMSecondMoment.RieszPositiveDefinite
