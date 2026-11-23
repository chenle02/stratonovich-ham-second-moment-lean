module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Wave L18, item B (approved by Le on 2026-11-21): Step 1 of `L:spatial-wick-measures`, TeX lines
1704-1722 at revision edf7085f (book 1.1.3), main file
`notes/notes_stratonovich_ham_second_moment.tex`.

Step 1 (TeX 1704-1709): orient each pair `e = {j, h}` as `j < h` and let `η_l(ξ)` be the
coefficient of `z_l` in `Σ_e ξ_e · (x_j - x_h)` (M4's `freq`).  "Finite heat-weighted spectral
measures and the finite damped Green masses justify Fourier and Laplace Fubini.  The wave
Laplace transform gives, for `λ_l ≥ 0`, `E:spatial-positive-laplace`" (TeX 1710-1719).  "The
integrand is nonnegative.  Thus, the transforms increase when any spatial width decreases"
(TeX 1720-1722).

Proved here (no supplied input, no fallback):
* `spectral_spatial_w`: `SpectralSpatialWTarget d`, the spectral form of `J_{ε,D}(r)` with
  vertexwise widths, for the Green-smoothed kernels `p_η * G_s` (`η ≥ 0`; `η = 0` is the TeX's
  `J`, `greenS_zero`);
* `smoothed_laplace`: `SmoothedLaplaceTarget d`, `L_{ε,D}(λ)` for the kernels `p_η * G_s`
  equals `laplaceRHS μ η` (route variant of decision 8, used by the d = 3 Green-width removal);
* `spatial_positive_laplace`: `SpatialPositiveLaplaceTarget d`, exactly the display
  `E:spatial-positive-laplace` (TeX 1710-1719), from `smoothed_laplace` at `η = 0`;
* `spectralSpatial_homog`: M4's recorded identity `DiagramModel.SpectralSpatial d Γ μ` (wave L13),
  for every label count `N` (including `N = 0` and odd `N`) and every pairing;
* `wickL_anti_width`: transform monotonicity (TeX 1720-1722): `L_{ε,D}(λ) ≤ L_{ε',D}(λ)` when
  `ε' ≤ ε` vertexwise.

Route (as the TeX): `covEps Γ b = ofReal (γ_b)` (`LowAlphaUpper.covEps_eq_ofReal`),
`γ_b(x) = ∫ e^{iξ·x} e^{-b|ξ|²/2} μ(dξ)` (`LowAlphaConvolution.gammaEps_spectral`), the product
over pairs as one integral over `μ^{⊗k}` (`integral_fintype_prod_eq_prod`), Fubini over the
finite product `⊗_l G_{r_l} ⊗ μ^{⊗k}` (the integrand has modulus `∏_e e^{-b_e|ξ_e|²/2}`, which is
`μ^{⊗k}`-integrable because `μ` is tempered: "finite heat-weighted spectral measures"), the
phase identity `Σ_e ξ_e · (x_j - x_h) = Σ_l η_l · z_l` (`phase_eq`) and
`∫ e^{iη·z} (p_η * G_s)(dz) = e^{-η|η|²/2} Ĝ_s(η)` (`charFun_greenS`, from
`DampedMultiplier.charFun_gaussKernel_conv` and `WaveGreenFourier.greenFourier`).  The Laplace
step is a second Fubini over `(0,∞)^{2k} × μ^{⊗k}`, dominated by
`∏_l e^{-(1+λ_l) r_l} r_l ∏_e e^{-b_e|ξ_e|²/2}` (`|Ĝ_r| ≤ r`: "the finite damped Green
masses"), and the wave Laplace transform `∫_0^∞ e^{-as} Ĝ_s(ξ) ds = (a² + |ξ|²)⁻¹`
(`WaveKernel.waveHat_laplace`).  The identities hold for every map `D` (no pairing property is
used); the targets' hypotheses `m + n = 2k`, `1 ≤ k`, `D ∈ Pi2 m n` are carried and unused.
No route difference from the TeX.  The measurability of `r ↦ J_{ε,D}(r)` needed for the
`withDensity` calculus comes from the spectral form (`measurable_spatialSpecW`, a parametric
integral of a jointly continuous integrand) and the identity on the orthant.

Lemmas marked "Auxiliary" serve only the Lean route.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.WickInterface
public import StratonovichHAMSecondMoment.WaveGreenFourier
public import StratonovichHAMSecondMoment.LowAlphaUpper

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Real Pointwise BoundedContinuousFunction Nat

namespace StratonovichHAMSecondMoment.WickSpectral

open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open LowAlphaConvolution (gaussFactor smoothedGreen gammaEps heatDens gaussFactor_pos
  integrable_gaussFactor gammaEps_spectral gammaEps_continuous_bounded gammaEps_nonneg)
open DiagramModel (Pi2 openers covEps pos freq spatialSpec spatial SpectralSpatial SameChain)
open WaveGreen (waveGreen)
open WaveKernel (waveHat)
open WickInterface

variable {d : ℕ}

/-! ### The Green-smoothed kernels -/

/-- Auxiliary.  The Green-smoothed kernels `p_η * G_s` are finite measures. -/
instance instIsFiniteMeasureGreenS (d : ℕ) (η s : ℝ) : IsFiniteMeasure (greenS d η s) := by
  have := WaveGreen.isFiniteMeasure_waveGreen d s
  unfold greenS smoothedGreen
  infer_instance

/-- The transform of the Green-smoothed kernel (TeX 1652-1655 with the wave transform):
`∫ e^{iξ·z} (p_η * G_s)(dz) = e^{-η|ξ|²/2} Ĝ_s(ξ)` for `η ≥ 0` and `s ≥ 0` (at `s = 0` both
sides vanish: `G_0 = 0`, `Ĝ_0 = 0`). -/
theorem charFun_greenS (hd : d = 1 ∨ d = 2 ∨ d = 3) {η : ℝ} (hη : 0 ≤ η) {s : ℝ} (hs : 0 ≤ s)
    (ξ : Rd d) : charFun (greenS d η s) ξ = ((gaussFactor η ξ * waveHat s ξ : ℝ) : ℂ) := by
  have := WaveGreen.isFiniteMeasure_waveGreen d s
  have hG : charFun (waveGreen d s) ξ = (waveHat s ξ : ℂ) := by
    rcases hs.lt_or_eq with hs | hs
    · exact (WaveGreenFourier.greenFourier d hd).fourier s hs ξ
    · subst hs
      rw [WaveGreen.waveGreen_of_nonpos d 0 le_rfl, charFun_zero_measure]
      simp [WaveKernel.waveHat]
  rw [greenS, smoothedGreen, DampedMultiplier.charFun_gaussKernel_conv η hη, hG, gaussFactor,
    Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  ring_nf

/-! ### The phase identity and the Fourier Fubini step -/

/-- Auxiliary.  The positions are continuous in the increments. -/
theorem continuous_pos (m : ℕ) {N : ℕ} (i : Fin N) :
    Continuous fun w : Fin N → Rd d => pos m w i := by
  unfold pos
  exact continuous_finsetSum _ fun j _ => continuous_apply j

/-- Auxiliary.  The frequencies `η_l(ξ)` are continuous in `ξ`. -/
theorem continuous_freq (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (l : Fin N) :
    Continuous fun ξ : openers D → Rd d => freq m D ξ l := by
  unfold freq
  exact continuous_finsetSum _ fun e _ => by fun_prop

/-- **The phase identity** (TeX 1705-1706): `η_l(ξ)` is the coefficient of `z_l` in
`Σ_e ξ_e · (x_j - x_h)`, i.e. `Σ_e ξ_e · (x_j - x_h) = Σ_l η_l(ξ) · z_l` at the positions
`x = pos m z`. -/
theorem phase_eq (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (ξ : openers D → Rd d)
    (w : Fin N → Rd d) :
    ∑ e : openers D, inner ℝ (ξ e) (pos m w e - pos m w (D e)) =
      ∑ l, inner ℝ (freq m D ξ l) (w l) := by
  have hpos : ∀ i, pos m w i =
      ∑ l, (if SameChain m l i ∧ l ≤ i then (1 : ℝ) else 0) • w l := by
    intro i
    unfold pos
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs <;> simp
  simp_rw [hpos, freq, ← Finset.sum_sub_distrib, ← sub_smul, inner_sum, sum_inner,
    real_inner_smul_left, real_inner_smul_right]
  rw [Finset.sum_comm]

/-- Auxiliary.  The increment integral of the phases is the product of the transforms of the
increment laws at the frequencies `η_l(ξ)`. -/
theorem integral_phase (m : ℕ) {N : ℕ} (D : Fin N → Fin N) (G : Fin N → Measure (Rd d))
    [∀ i, IsFiniteMeasure (G i)] (ξ : openers D → Rd d) :
    ∫ w, ∏ e : openers D,
        Complex.exp (Complex.I * (inner ℝ (ξ e) (pos m w e - pos m w (D e)) : ℝ))
      ∂Measure.pi G = ∏ l, charFun (G l) (freq m D ξ l) := by
  have h : ∀ w : Fin N → Rd d, ∏ e : openers D,
      Complex.exp (Complex.I * (inner ℝ (ξ e) (pos m w e - pos m w (D e)) : ℝ)) =
        ∏ l, Complex.exp ((inner ℝ (w l) (freq m D ξ l) : ℝ) * Complex.I) := by
    intro w
    rw [← Complex.exp_sum, ← Complex.exp_sum]
    congr 1
    rw [← Finset.mul_sum, ← Finset.sum_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sum,
      phase_eq, mul_comm]
    congr 2
    exact Finset.sum_congr rfl fun l _ => real_inner_comm _ _
  simp_rw [h]
  rw [integral_fintype_prod_eq_prod (f := fun l v =>
    Complex.exp ((inner ℝ v (freq m D ξ l) : ℝ) * Complex.I))]
  rfl

/-- Auxiliary.  A product of smoothed covariances as one spectral integral over `μ^{⊗k}`. -/
theorem prod_gammaEps_spectral {Γ μ : Measure (Rd d)} [SigmaFinite μ]
    (hsp : IsSpectralMeasure Γ μ) {ι : Type*} [Fintype ι] {b : ι → ℝ} (hb : ∀ e, 0 < b e)
    (x : ι → Rd d) :
    ((∏ e, gammaEps Γ (b e) (x e) : ℝ) : ℂ) =
      ∫ ξ, ∏ e, (Complex.exp (Complex.I * (inner ℝ (ξ e) (x e) : ℝ)) *
          (gaussFactor (b e) (ξ e) : ℂ)) ∂Measure.pi fun _ : ι => μ := by
  rw [integral_fintype_prod_eq_prod (f := fun e ξ =>
    Complex.exp (Complex.I * (inner ℝ ξ (x e) : ℝ)) * (gaussFactor (b e) ξ : ℂ)),
    Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun e _ => gammaEps_spectral hsp (hb e) (x e)

section Core

variable {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}

/-- **The spectral form as a real identity** (TeX 1705-1708): for positive vertex widths,
`η ≥ 0` and nonnegative gaps, `∫ ∏_e γ_{ε_j+ε_h}(x_j - x_h) ⊗_l (p_η * G_{r_l})(dz_l)` (a real
Bochner integral) is the spectral integral `spatialSpecW`.  Holds for every map `D`. -/
theorem spatialSpecW_eq_integral (hH : HomogCovariance d alpha α₀ Γ μ) {η : ℝ} (hη : 0 ≤ η)
    (m : ℕ) {N : ℕ} (D : Fin N → Fin N) {ε : Fin N → ℝ} (hε : ∀ i, 0 < ε i)
    {r : Fin N → ℝ} (hr : ∀ i, 0 ≤ r i) :
    spatialSpecW μ η ε m D r =
      ∫ w, ∏ e : openers D, gammaEps Γ (ε e + ε (D e)) (pos m w e - pos m w (D e))
        ∂Measure.pi fun i => greenS d η (r i) := by
  have := hH.μ_radon
  have hb : ∀ e : openers D, 0 < ε e + ε (D e) := fun e => add_pos (hε _) (hε _)
  set P := Measure.pi fun i => greenS d η (r i) with hP
  set μk := Measure.pi fun _ : openers D => μ with hμk
  set Φ : (Fin N → Rd d) → (openers D → Rd d) → ℂ := fun w ξ =>
    ∏ e : openers D, (Complex.exp (Complex.I * (inner ℝ (ξ e) (pos m w e - pos m w (D e)) : ℝ)) *
      (gaussFactor (ε e + ε (D e)) (ξ e) : ℂ)) with hΦ
  set g : (openers D → Rd d) → ℝ := fun ξ =>
    ∏ e : openers D, gaussFactor (ε e + ε (D e)) (ξ e) with hg
  have hgint : Integrable g μk :=
    Integrable.fintype_prod (f := fun (e : openers D) ξ => gaussFactor (ε e + ε (D e)) ξ)
      fun e => integrable_gaussFactor hH.μ_tempered (hb e)
  have hnorm : ∀ w ξ, ‖Φ w ξ‖ = g ξ := by
    intro w ξ
    simp only [hΦ, hg, norm_prod, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (gaussFactor_pos _ _)]
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hcont : Continuous (Function.uncurry Φ) := by
    simp only [hΦ, gaussFactor, Function.uncurry_def]
    refine continuous_finsetProd _ fun e _ => ?_
    have h1 : Continuous fun p : (Fin N → Rd d) × (openers D → Rd d) => p.2 e :=
      (continuous_apply e).comp continuous_snd
    have h2 : Continuous fun p : (Fin N → Rd d) × (openers D → Rd d) =>
        pos m p.1 e - pos m p.1 (D e) :=
      ((continuous_pos m _).comp continuous_fst).sub ((continuous_pos m _).comp continuous_fst)
    fun_prop
  have hprod : Integrable (Function.uncurry Φ) (P.prod μk) :=
    Integrable.mono' (hgint.comp_snd P) hcont.aestronglyMeasurable
      (Eventually.of_forall fun p => (hnorm p.1 p.2).le)
  have hinner : ∀ ξ, ∫ w, Φ w ξ ∂P = ((g ξ * ∏ l, (gaussFactor η (freq m D ξ l) *
      waveHat (r l) (freq m D ξ l)) : ℝ) : ℂ) := by
    intro ξ
    have h : ∀ w, Φ w ξ = (∏ e : openers D,
        Complex.exp (Complex.I * (inner ℝ (ξ e) (pos m w e - pos m w (D e)) : ℝ))) *
          (g ξ : ℂ) := by
      intro w
      simp only [hΦ, hg, Finset.prod_mul_distrib, Complex.ofReal_prod]
    simp_rw [h]
    rw [integral_mul_const, hP, integral_phase, Complex.ofReal_mul, mul_comm _ ((g ξ : ℝ) : ℂ)]
    congr 1
    rw [Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun l _ => charFun_greenS hH.dim hη (hr l) _
  apply Complex.ofReal_injective
  calc ((spatialSpecW μ η ε m D r : ℝ) : ℂ)
      = ∫ ξ, ((g ξ * ∏ l, (gaussFactor η (freq m D ξ l) *
          waveHat (r l) (freq m D ξ l)) : ℝ) : ℂ) ∂μk := by
        unfold spatialSpecW; exact integral_ofReal.symm
    _ = ∫ ξ, ∫ w, Φ w ξ ∂P ∂μk := by simp_rw [hinner]
    _ = ∫ w, ∫ ξ, Φ w ξ ∂μk ∂P := (integral_integral_swap hprod).symm
    _ = ∫ w, ((∏ e : openers D, gammaEps Γ (ε e + ε (D e)) (pos m w e - pos m w (D e)) : ℝ) : ℂ)
          ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        exact (prod_gammaEps_spectral hH.spectral hb _).symm
    _ = _ := integral_ofReal

/-- **`J_{ε,D}(r)` in spectral form** (TeX 1705-1708), with its nonnegativity: for positive
vertex widths, `η ≥ 0` and nonnegative gaps, `J_{ε,D}(r)` for the kernels `p_η * G` is
`ofReal (spatialSpecW μ η ε m D r)` and `spatialSpecW μ η ε m D r ≥ 0`.  For every map `D`. -/
theorem wickJ_greenS_eq (hH : HomogCovariance d alpha α₀ Γ μ) {η : ℝ} (hη : 0 ≤ η) (m : ℕ)
    {N : ℕ} (D : Fin N → Fin N) {ε : Fin N → ℝ} (hε : ∀ i, 0 < ε i) {r : Fin N → ℝ}
    (hr : ∀ i, 0 ≤ r i) :
    wickJ (greenS d η) Γ ε m D r = ENNReal.ofReal (spatialSpecW μ η ε m D r) ∧
      0 ≤ spatialSpecW μ η ε m D r := by
  rw [spatialSpecW_eq_integral hH hη m D hε hr]
  have := hH.μ_radon
  have hb : ∀ e : openers D, 0 < ε e + ε (D e) := fun e => add_pos (hε _) (hε _)
  have hf0 : ∀ w : Fin N → Rd d,
      0 ≤ ∏ e : openers D, gammaEps Γ (ε e + ε (D e)) (pos m w e - pos m w (D e)) :=
    fun w => Finset.prod_nonneg fun e _ => gammaEps_nonneg Γ (hb e).le _
  have hfc : Continuous fun w : Fin N → Rd d =>
      ∏ e : openers D, gammaEps Γ (ε e + ε (D e)) (pos m w e - pos m w (D e)) :=
    continuous_finsetProd _ fun e _ =>
      (gammaEps_continuous_bounded hH.μ_tempered hH.spectral (hb e)).1.comp
        ((continuous_pos m _).sub (continuous_pos m _))
  have hint : Integrable (fun w : Fin N → Rd d =>
      ∏ e : openers D, gammaEps Γ (ε e + ε (D e)) (pos m w e - pos m w (D e)))
      (Measure.pi fun i => greenS d η (r i)) := by
    refine Integrable.of_bound hfc.aestronglyMeasurable
      (∏ e : openers D, ∫ ξ, gaussFactor (ε e + ε (D e)) ξ ∂μ)
      (Eventually.of_forall fun w => ?_)
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun e _ => norm_nonneg _) fun e _ =>
      (gammaEps_continuous_bounded hH.μ_tempered hH.spectral (hb e)).2 _
  refine ⟨?_, integral_nonneg hf0⟩
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hf0)]
  unfold wickJ covW
  refine lintegral_congr fun w => ?_
  rw [ENNReal.ofReal_prod_of_nonneg (fun e _ => gammaEps_nonneg Γ (hb e).le _),
    ← Finset.prod_coe_sort (openers D)]
  refine Finset.prod_congr rfl fun e _ => ?_
  exact LowAlphaUpper.covEps_eq_ofReal (hb e).le
    (LowAlphaConvolution.integrable_heatDens hH.Γ_tempered (hb e)) _

/-- Auxiliary.  `r ↦ spatialSpecW μ η ε m D r` is measurable (a parametric integral of a jointly
continuous integrand). -/
theorem measurable_spatialSpecW (hH : HomogCovariance d alpha α₀ Γ μ) (η : ℝ) (m : ℕ) {N : ℕ}
    (D : Fin N → Fin N) (ε : Fin N → ℝ) :
    Measurable fun r : Fin N → ℝ => spatialSpecW μ η ε m D r := by
  have := hH.μ_radon
  have hc : Continuous (Function.uncurry fun (r : Fin N → ℝ) (ξ : openers D → Rd d) =>
      (∏ e : openers D, gaussFactor (ε e + ε (D e)) (ξ e)) *
        ∏ l, gaussFactor η (freq m D ξ l) * waveHat (r l) (freq m D ξ l)) := by
    simp only [Function.uncurry_def]
    refine Continuous.mul (continuous_finsetProd _ fun e _ => ?_)
      (continuous_finsetProd _ fun l _ => ?_)
    · have h1 : Continuous fun p : (Fin N → ℝ) × (openers D → Rd d) => p.2 e :=
        (continuous_apply e).comp continuous_snd
      simp only [gaussFactor]
      fun_prop
    · have hf : Continuous fun p : (Fin N → ℝ) × (openers D → Rd d) => freq m D p.2 l :=
        (continuous_freq m D l).comp continuous_snd
      have hw : Continuous fun p : (Fin N → ℝ) × (openers D → Rd d) =>
          waveHat (p.1 l) (freq m D p.2 l) :=
        WaveKernel.waveHat_continuous.comp (((continuous_apply l).comp continuous_fst).prodMk hf)
      simp only [gaussFactor]
      fun_prop
  exact (hc.stronglyMeasurable.integral_prod_right
    (ν := Measure.pi fun _ : openers D => μ)).measurable

/-- **`E:spatial-positive-laplace` with the Green multiplier** (TeX 1710-1719; the `p_η * G`
variant of decision 8): for positive vertex widths, `η ≥ 0` and `λ_l ≥ 0`, the Laplace transform
`L_{ε,D}(λ)` of `ν_{ε,D}` built on the kernels `p_η * G` is `laplaceRHS μ η ε m D λ`.  For every
map `D`. -/
theorem wickL_greenS_eq (hH : HomogCovariance d alpha α₀ Γ μ) {η : ℝ} (hη : 0 ≤ η) (m : ℕ)
    {N : ℕ} (D : Fin N → Fin N) {ε : Fin N → ℝ} (hε : ∀ i, 0 < ε i) {lam : Fin N → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) :
    wickL (greenS d η) Γ ε m D lam = laplaceRHS μ η ε m D lam := by
  have := hH.μ_radon
  set S : (Fin N → ℝ) → ℝ := fun r => spatialSpecW μ η ε m D r with hS
  set a : Fin N → ℝ := fun l => 1 + lam l with ha_def
  have ha : ∀ l, 0 < a l := fun l => by simp only [ha_def]; linarith [hlam l]
  have hO : MeasurableSet (posOrthant N) := MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have hmemO : ∀ r ∈ posOrthant N, ∀ i, 0 ≤ r i := fun r hr i => le_of_lt (hr i (mem_univ i))
  have hJ : wickJ (greenS d η) Γ ε m D =ᵐ[volume.restrict (posOrthant N)]
      fun r => ENNReal.ofReal (S r) :=
    (ae_restrict_iff' hO).2 (Eventually.of_forall fun r hr =>
      (wickJ_greenS_eq hH hη m D hε (hmemO r hr)).1)
  have hSm : Measurable S := measurable_spatialSpecW hH η m D ε
  have hE1 : Measurable fun r : Fin N → ℝ => ENNReal.ofReal (Real.exp (-∑ i, r i)) := by
    fun_prop
  have hEl : Measurable fun r : Fin N → ℝ => ENNReal.ofReal (Real.exp (-∑ i, lam i * r i)) := by
    fun_prop
  set K : (Fin N → ℝ) → ℝ := fun r => Real.exp (-∑ l, a l * r l) * S r with hK
  -- Step 1: the Laplace transform as a set integral of `ofReal K` over the orthant
  have hstep1 : wickL (greenS d η) Γ ε m D lam =
      ∫⁻ r in posOrthant N, ENNReal.ofReal (K r) := by
    unfold wickL wickNu wickRho
    rw [withDensity_congr_ae hJ, lintegral_withDensity_eq_lintegral_mul _ hE1 hEl,
      lintegral_withDensity_eq_lintegral_mul _ (hSm.ennreal_ofReal)
        (hE1.mul hEl)]
    refine setLIntegral_congr_fun hO fun r hr => ?_
    have hS0 : 0 ≤ S r := (wickJ_greenS_eq hH hη m D hε (hmemO r hr)).2
    have he : Real.exp (-∑ l, a l * r l) =
        Real.exp (-∑ i, r i) * Real.exp (-∑ i, lam i * r i) := by
      rw [← Real.exp_add]
      congr 1
      simp only [ha_def, add_mul, one_mul, Finset.sum_add_distrib]
      ring
    simp only [Pi.mul_apply, hK]
    rw [he, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    ring
  -- Step 2: Fubini over `(0,∞)^N × μ^{⊗k}`
  set L0 : Measure (Fin N → ℝ) := Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ)) with hL0
  have hvol : (volume : Measure (Fin N → ℝ)).restrict (posOrthant N) = L0 := by
    rw [hL0, volume_pi]
    exact Measure.restrict_pi_pi _ _
  set μk := Measure.pi fun _ : openers D => μ with hμk
  have hb : ∀ e : openers D, 0 < ε e + ε (D e) := fun e => add_pos (hε _) (hε _)
  set g : (openers D → Rd d) → ℝ := fun ξ =>
    ∏ e : openers D, gaussFactor (ε e + ε (D e)) (ξ e) with hg
  have hg0 : ∀ ξ, 0 ≤ g ξ := fun ξ => Finset.prod_nonneg fun e _ => (gaussFactor_pos _ _).le
  have hgint : Integrable g μk :=
    Integrable.fintype_prod (f := fun (e : openers D) ξ => gaussFactor (ε e + ε (D e)) ξ)
      fun e => integrable_gaussFactor hH.μ_tempered (hb e)
  set H : (Fin N → ℝ) → (openers D → Rd d) → ℝ := fun r ξ =>
    g ξ * ∏ l, (gaussFactor η (freq m D ξ l) *
      (Real.exp (-(a l * r l)) * waveHat (r l) (freq m D ξ l))) with hH_def
  have hφint : Integrable (fun r : Fin N → ℝ => ∏ l, (Real.exp (-(a l * r l)) * |r l|)) L0 := by
    refine Integrable.fintype_prod (f := fun l s => Real.exp (-(a l * s)) * |s|) fun l => ?_
    have h := TimeFractional.subKernel_integrable 2 (a l) two_pos (ha l)
    refine h.congr ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_))
    simp only [TimeFractional.subKernel]
    rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, abs_of_pos (show (0 : ℝ) < s from hs),
      mul_comm]
  have hHc : Continuous (Function.uncurry H) := by
    simp only [hH_def, hg, Function.uncurry_def]
    refine Continuous.mul (continuous_finsetProd _ fun e _ => ?_)
      (continuous_finsetProd _ fun l _ => ?_)
    · have h1 : Continuous fun p : (Fin N → ℝ) × (openers D → Rd d) => p.2 e :=
        (continuous_apply e).comp continuous_snd
      simp only [gaussFactor]
      fun_prop
    · have hf : Continuous fun p : (Fin N → ℝ) × (openers D → Rd d) => freq m D p.2 l :=
        (continuous_freq m D l).comp continuous_snd
      have hw : Continuous fun p : (Fin N → ℝ) × (openers D → Rd d) =>
          waveHat (p.1 l) (freq m D p.2 l) :=
        WaveKernel.waveHat_continuous.comp (((continuous_apply l).comp continuous_fst).prodMk hf)
      have hr : Continuous fun p : (Fin N → ℝ) × (openers D → Rd d) => p.1 l :=
        (continuous_apply l).comp continuous_fst
      simp only [gaussFactor]
      fun_prop
  have hprod : Integrable (Function.uncurry H) (L0.prod μk) := by
    refine Integrable.mono' (hφint.mul_prod hgint) hHc.aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry_def, hH_def, Real.norm_eq_abs, abs_mul, Finset.abs_prod,
      abs_of_nonneg (hg0 _)]
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right (Finset.prod_le_prod₀ (fun l _ => by positivity)
      fun l _ => ?_) (hg0 _)
    rw [abs_of_pos (gaussFactor_pos _ _), abs_of_pos (Real.exp_pos _)]
    calc gaussFactor η (freq m D p.2 l) * (Real.exp (-(a l * p.1 l)) *
          |waveHat (p.1 l) (freq m D p.2 l)|)
        ≤ 1 * (Real.exp (-(a l * p.1 l)) * |p.1 l|) := by
          refine mul_le_mul (LowAlphaConvolution.gaussFactor_le_one hη _)
            (mul_le_mul_of_nonneg_left (WaveKernel.abs_waveHat_le _ _) (Real.exp_pos _).le)
            (by positivity) zero_le_one
      _ = Real.exp (-(a l * p.1 l)) * |p.1 l| := one_mul _
  -- `K` is the inner `ξ`-integral of `H`
  have hKH : ∀ r, K r = ∫ ξ, H r ξ ∂μk := by
    intro r
    simp only [hK, hS, hH_def]
    unfold spatialSpecW
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    have he : Real.exp (-∑ l, a l * r l) = ∏ l, Real.exp (-(a l * r l)) := by
      rw [← Real.exp_sum, Finset.sum_neg_distrib]
    simp only [hg]
    rw [he]
    have hp : ∏ l, (gaussFactor η (freq m D ξ l) *
        (Real.exp (-(a l * r l)) * waveHat (r l) (freq m D ξ l))) =
        (∏ l, Real.exp (-(a l * r l))) *
          ∏ l, (gaussFactor η (freq m D ξ l) * waveHat (r l) (freq m D ξ l)) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun l _ => by ring
    rw [hp]
    ring
  -- the inner `r`-integral of `H`: the wave Laplace transform
  set R : (openers D → Rd d) → ℝ := fun ξ =>
    g ξ * ∏ l, gaussFactor η (freq m D ξ l) / ((1 + lam l) ^ 2 + ‖freq m D ξ l‖ ^ 2) with hR
  have hHR : ∀ ξ, ∫ r, H r ξ ∂L0 = R ξ := by
    intro ξ
    simp only [hH_def, hR]
    rw [integral_const_mul, hL0, integral_fintype_prod_eq_prod (f := fun l s =>
      gaussFactor η (freq m D ξ l) * (Real.exp (-(a l * s)) * waveHat s (freq m D ξ l)))]
    congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [integral_const_mul, (WaveKernel.waveHat_laplace (a l) (ha l) _).2, mul_one_div]
  have hR0 : ∀ ξ, 0 ≤ R ξ := fun ξ =>
    mul_nonneg (hg0 ξ) (Finset.prod_nonneg fun l _ =>
      div_nonneg (gaussFactor_pos _ _).le (by positivity))
  have hRint : Integrable R μk := by
    have := hprod.integral_prod_right
    exact this.congr (Eventually.of_forall fun ξ => hHR ξ)
  have hKint : Integrable K L0 := by
    have := hprod.integral_prod_left
    exact this.congr (Eventually.of_forall fun r => (hKH r).symm)
  have hK0 : 0 ≤ᵐ[L0] K := by
    rw [← hvol]
    exact (ae_restrict_iff' hO).2 (Eventually.of_forall fun r hr =>
      mul_nonneg (Real.exp_pos _).le (wickJ_greenS_eq hH hη m D hε (hmemO r hr)).2)
  rw [hstep1, hvol, ← ofReal_integral_eq_lintegral_ofReal hKint hK0]
  have hswap : ∫ r, K r ∂L0 = ∫ ξ, R ξ ∂μk := by
    calc ∫ r, K r ∂L0 = ∫ r, ∫ ξ, H r ξ ∂μk ∂L0 := integral_congr_ae
          (Eventually.of_forall hKH)
      _ = ∫ ξ, ∫ r, H r ξ ∂L0 ∂μk := integral_integral_swap hprod
      _ = ∫ ξ, R ξ ∂μk := integral_congr_ae (Eventually.of_forall hHR)
  rw [hswap, ofReal_integral_eq_lintegral_ofReal hRint (Eventually.of_forall hR0)]
  rfl

end Core

/-! ### The frozen targets of item B -/

/-- **B: the spectral identity of `J_{ε,D}` with vertexwise widths and the Green multiplier**
(Step 1, TeX lines 1705-1708 at revision edf7085f (book 1.1.3)). -/
theorem spectral_spatial_w (d : ℕ) : SpectralSpatialWTarget d := by
  intro alpha α₀ Γ μ hH η hη m n k _ _ D _ ε hε r hr
  exact (wickJ_greenS_eq hH hη m D hε hr).1

/-- **B: `E:spatial-positive-laplace` with the Green multiplier** (TeX lines 1710-1719 and
1652-1655 at revision edf7085f (book 1.1.3); the route variant of decision 8). -/
theorem smoothed_laplace (d : ℕ) : SmoothedLaplaceTarget d := by
  intro alpha α₀ Γ μ hH η hη m n k _ _ D _ ε hε lam hlam
  exact wickL_greenS_eq hH hη m D hε hlam

/-- **B: `E:spatial-positive-laplace`** (TeX lines 1710-1719 at revision edf7085f (book 1.1.3)),
exactly the display: `smoothed_laplace` at Green width `η = 0` (`greenS_zero`,
`laplaceRHS_zero`). -/
theorem spatial_positive_laplace (d : ℕ) : SpatialPositiveLaplaceTarget d := by
  intro alpha α₀ Γ μ hH m n k _ _ D _ ε hε lam hlam
  rw [← greenS_zero d, wickL_greenS_eq hH le_rfl m D hε hlam, laplaceRHS_zero]

/-- **M4's recorded spectral identity `DiagramModel.SpectralSpatial`** (wave L13; TeX lines
1705-1708 at revision edf7085f (book 1.1.3) at the common pair width `ε`): under `H:homog`,
`spatial (waveGreen d) (covEps Γ ε) m D h = ofReal (spatialSpec μ ε m D h)` for `ε > 0`,
`h ≥ 0`, every label count `N` (also `N = 0`, and odd `N`, where `Π` is empty) and every
pairing.  From `wickJ_greenS_eq` at the common vertex width `ε/2` and `η = 0` (`wickJ_half`,
`wickJ_greenS_zero`, `spatialSpecW_half`). -/
theorem spectralSpatial_homog {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) : SpectralSpatial d Γ μ := by
  intro ε hε m N D _ h hh
  rw [← wickJ_half, ← wickJ_greenS_zero,
    (wickJ_greenS_eq hH le_rfl m D (fun _ => half_pos hε) hh).1, spatialSpecW_half]

/-- **Transform monotonicity** (TeX lines 1720-1722 at revision edf7085f (book 1.1.3)): the
integrand of `E:spatial-positive-laplace` is nonnegative and decreasing in every width, so
`L_{ε,D}(λ) ≤ L_{ε',D}(λ)` when `0 < ε' ≤ ε` vertexwise ("the transforms increase when any
spatial width decreases"; not pointwise monotonicity of the covariances). -/
theorem wickL_anti_width {d : ℕ} {alpha α₀ : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha α₀ Γ μ) {m n k : ℕ} (hmn : m + n = 2 * k) (hk : 1 ≤ k)
    {D : Fin (m + n) → Fin (m + n)} (hD : D ∈ Pi2 m n) {ε ε' : Fin (m + n) → ℝ}
    (hε' : ∀ i, 0 < ε' i) (hle : ∀ i, ε' i ≤ ε i) {lam : Fin (m + n) → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) :
    wickL (waveGreen d) Γ ε m D lam ≤ wickL (waveGreen d) Γ ε' m D lam := by
  rw [spatial_positive_laplace d hH m n k hmn hk D hD ε (fun i => (hε' i).trans_le (hle i))
      lam hlam,
    spatial_positive_laplace d hH m n k hmn hk D hD ε' hε' lam hlam]
  refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun l _ => by positivity)
  refine Finset.prod_le_prod₀ (fun e _ => (gaussFactor_pos _ _).le) fun e _ => ?_
  unfold gaussFactor
  refine Real.exp_le_exp.2 ?_
  have h1 := hle e
  have h2 := hle (D e)
  have h3 := sq_nonneg ‖ξ e‖
  nlinarith

end StratonovichHAMSecondMoment.WickSpectral
