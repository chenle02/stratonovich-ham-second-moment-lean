module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The Fourier identities of the wave Green measures `G_s` in `d = 2, 3`, of the
main TeX file `notes/notes_stratonovich_ham_second_moment.tex` (revision
a284420), Archimedes' law for the sphere measure, and the extension of the
Green-smoothing identification of `L:damped-homogeneous-norms` (L8-b,
`DampedMultiplier`) to every `d ∈ {1,2,3}`.

Sources at a284420 (main TeX):
* `Ĝ_s(ξ) = sin(s|ξ|)/|ξ|`, value `s` at `ξ = 0` (lines 777-778, before
  `E:damped-norm-definitions`);
* the display `Ĝ_h(ξ) = sin(h|ξ|)/|ξ|`, `G_h(ℝ^d) = h` (lines 4738-4744, in
  the proof of `L:low-alpha-convolution`, lines 4702-4757), quoted from the
  source's (2.3)-(2.5), p. 7; the identity is also used in the proof of
  `L:alpha-one-convolution` (lines 4760-4818, the factor `sin(hr)/r` at
  4787-4794) and in `E:phase-trace` of `L:phase-contractions` (lines
  2072-2137; `T_ε(a,q) = ∫ Ĝ_a(q+ξ) e^{-ε|ξ|²} μ(dξ)`, lines 2081-2084, d = 3).
  The TeX states the identity without proof (it is imported from the source).
* the measures `G_h^{(2)}`, `G_h^{(3)}` (lines 5179-5187), formalized as
  `WaveGreen.waveGreen` (unchanged).  The `d = 3` measure is the recorded
  DEFINITIONAL CHOICE of `WaveGreen` (Le's decision 4 for wave L6):
  `(s/(4π)) · map (ω ↦ sω) σ` with `σ = volume.toSphere`; this module proves
  facts about that measure and does not identify `σ` with a Hausdorff or
  Riemannian surface measure.

Formalized (all proved, nothing supplied):
* `waveGreen_fourier_two`, `waveGreen_fourier_three`: `∫ e^{iξ·x} G_s(dx) =
  waveHat s ξ` for `s > 0`, every `ξ`, with integrability;
* `waveGreen_fourier`: the same for `d ∈ {1,2,3}` (with
  `WaveGreen.waveGreen_fourier_one`), and `waveGreen_fourier_paper`, the display
  at lines 4740-4744 with the right side written as in the TeX
  (`sin(h|ξ|)/|ξ|`, value `h` at `ξ = 0`) together with `G_h(ℝ^d) = h`;
* `sphere_fourier`: `∫_{S²} e^{iξ·ω} σ(dω) = 4π sinc|ξ|`;
* `archimedes`: the image of `σ` under `ω ↦ ⟪e,ω⟫` (`‖e‖ = 1`) is
  `2π · Lebesgue` on `[-1,1]`, with the integral forms
  `lintegral_sphere_inner`, `integral_sphere_inner`, `integrable_sphere_inner`;
* `greenFourier`: `DampedMultiplier.GreenFourier (waveGreen d)` for
  `d ∈ {1,2,3}` (L8-b proved it for `d = 1` only, `greenFourier_one`);
* `damped_homogeneous_norms_fourier_wave`: the conclusions of
  `DampedMultiplier.damped_homogeneous_norms_fourier_paper` with
  `G := waveGreen d` under `H:homog` alone (`HomogCovariance`; `d` from `h.dim`,
  no `Γ ≠ 0`), i.e. the Green-smoothing identification (main TeX lines 845-847,
  915-917) in every `d`, generalizing `damped_homogeneous_norms_fourier_one`.

Not formalized: the three lemmas that use the identity (`L:low-alpha-convolution`,
`L:alpha-one-convolution`, `L:phase-contractions`) and the spherical computations
that use Archimedes' law (lines 2125-2131, 5189-5194).

Proof route (the TeX has no proof; no Bessel functions are used):
* `d = 2`: rotate `ξ` to `|ξ|e₀` by a reflection (`Submodule.reflection_sub`;
  Lebesgue measure is invariant, `LinearIsometryEquiv.measurePreserving`), slice
  along `x₀` (Fubini), and use `∫_{-a}^{a}(a²-u²)^{-1/2} du = π` (`arcsin`); the
  remaining `½∫_{-s}^{s} e^{i|ξ|t} dt` is `Ĝ_s(ξ)`.
* `d = 3`: compute `∫_{|x|<R} e^{iξ·x} dx` (i) in polar coordinates,
  `∫_0^R r² Φ_ξ(r) dr` with `Φ_ξ(r) = ∫ e^{irξ·ω} σ(dω)`
  (`Measure.measurePreserving_homeomorphUnitSphereProd`), and (ii) by rotation and
  slicing, `π∫_{-R}^{R}(R²-t²)e^{i|ξ|t} dt` (`EuclideanSpace.volume_ball_fin_two`);
  differentiate both in `R` at `R = 1` to get `Φ_ξ(1) = 4π sinc|ξ|`.
* Archimedes: `Measure.ext_of_charFun` with `sphere_fourier`.
Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.

Hypotheses of `H:homog`: only `damped_homogeneous_norms_fourier_wave` takes
`HomogCovariance`; it uses `h.dim` directly (for `greenFourier`) and passes `h`
to `DampedMultiplier.damped_homogeneous_norms_fourier_paper`, which uses the
fields documented in `DampedMultiplier`.  The Fourier identities and
Archimedes' law are statements about the measures alone and take only
`d ∈ {1,2,3}` (or nothing).

Junk values: `radial2 s r = (2π√(s²-r²))⁻¹` is `0` for `r ≥ s` by the
conventions `√(negative) = 0` and `0⁻¹ = 0`; it is used only where it equals the
density of `waveGreen 2 s` (`waveGreen_two_eq`, proved for `s > 0`) or inside the
slice integral, whose value (`integral_slice_two`) holds exactly as stated.  The
Fourier conclusions are complex Bochner integrals whose integrability is part of
each statement, so no non-integrable junk value enters.  `Real.sinc 0 = 1` gives
the TeX's value `s` at `ξ = 0`.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.TimeFractional
public import StratonovichHAMSecondMoment.WaveKernel
public import StratonovichHAMSecondMoment.DampedNorms
public import StratonovichHAMSecondMoment.DampedNormsHomog
public import StratonovichHAMSecondMoment.WaveGreen
public import StratonovichHAMSecondMoment.DampedMultiplier

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Metric Filter ProbabilityTheory
open scoped ENNReal NNReal Pointwise Topology

namespace StratonovichHAMSecondMoment.WaveGreenFourier

open HomogHypothesis TimeFractional WaveKernel DampedNorms DampedNormsHomog WaveGreen
  DampedMultiplier

/-! ### Rotation and slicing -/
/-- A linear isometry `ρ` of `ℝ^{n+1}` with `⟪ξ, ρx⟫ = ‖ξ‖ x₀` (the reflection
exchanging `ξ` and `‖ξ‖e₀`, `Submodule.reflection_sub`).  Auxiliary to the Lean proof route. -/
theorem exists_rotation (n : ℕ) (ξ : Rd (n + 1)) :
    ∃ ρ : Rd (n + 1) ≃ₗᵢ[ℝ] Rd (n + 1), ∀ x, inner ℝ ξ (ρ x) = ‖ξ‖ * x 0 := by
  set e0 : Rd (n + 1) := EuclideanSpace.single 0 1 with he0
  have hn : ‖ξ‖ = ‖‖ξ‖ • e0‖ := by simp [e0, norm_smul]
  set K := (ℝ ∙ (ξ - ‖ξ‖ • e0))ᗮ
  refine ⟨K.reflection, fun x => ?_⟩
  have h1 : K.reflection ξ = ‖ξ‖ • e0 := Submodule.reflection_sub hn
  calc inner ℝ ξ (K.reflection x)
      = inner ℝ (K.reflection ξ) (K.reflection (K.reflection x)) :=
        (K.reflection.inner_map_map _ _).symm
    _ = ‖ξ‖ * x 0 := by
        rw [Submodule.reflection_reflection, h1, real_inner_smul_left, he0,
          EuclideanSpace.inner_single_left]
        simp

/-- Rotation: `∫ g(⟪ξ,x⟫, ‖x‖) dx = ∫ g(‖ξ‖x₀, ‖x‖) dx` on `ℝ^{n+1}` (Lebesgue
measure is invariant under linear isometries; no integrability needed, both
sides are Bochner integrals of functions exchanged by a measure-preserving
equivalence).  Auxiliary to the Lean proof route. -/
theorem integral_inner_norm (n : ℕ) (ξ : Rd (n + 1)) (g : ℝ → ℝ → ℂ) :
    ∫ x : Rd (n + 1), g (inner ℝ ξ x) ‖x‖ = ∫ x : Rd (n + 1), g (‖ξ‖ * x 0) ‖x‖ := by
  obtain ⟨ρ, hρ⟩ := exists_rotation n ξ
  rw [← ρ.measurePreserving.integral_comp ρ.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun x => g (inner ℝ ξ x) ‖x‖)]
  simp [hρ]

/-- Integrability form of `integral_inner_norm`.  Auxiliary to the Lean proof route. -/
theorem integrable_inner_norm (n : ℕ) (ξ : Rd (n + 1)) (g : ℝ → ℝ → ℂ) :
    Integrable (fun x : Rd (n + 1) => g (inner ℝ ξ x) ‖x‖) ↔
      Integrable (fun x : Rd (n + 1) => g (‖ξ‖ * x 0) ‖x‖) := by
  obtain ⟨ρ, hρ⟩ := exists_rotation n ξ
  rw [← ρ.measurePreserving.integrable_comp_emb
    ρ.toHomeomorph.toMeasurableEquiv.measurableEmbedding]
  simp [Function.comp_def, hρ]

/-- `ℝ^{n+1} ≃ ℝ × ℝ^n`, `x ↦ (x₀, (x₁,…,xₙ))`.  Auxiliary to the Lean proof route. -/
def splitFirst (n : ℕ) : Rd (n + 1) ≃ᵐ ℝ × Rd n :=
  ((MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin n → ℝ)))

/-- `splitFirst` preserves Lebesgue measure.  Auxiliary to the Lean proof route. -/
theorem splitFirst_mp (n : ℕ) : MeasurePreserving (splitFirst n) (volume : Measure (Rd (n + 1)))
    (volume : Measure (ℝ × Rd n)) := by
  refine ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n + 1))).trans
    (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0)).trans ?_
  exact (MeasurePreserving.id volume).prod
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).symm

/-- Auxiliary to the Lean proof route. -/
theorem splitFirst_fst (n : ℕ) (x : Rd (n + 1)) : (splitFirst n x).1 = x 0 := rfl

/-- `‖x‖ = √(x₀² + ‖(x₁,…,xₙ)‖²)`.  Auxiliary to the Lean proof route. -/
theorem norm_splitFirst (n : ℕ) (x : Rd (n + 1)) :
    ‖x‖ = √((x 0) ^ 2 + ‖(splitFirst n x).2‖ ^ 2) := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Fin.sum_univ_succ]
  simp [splitFirst, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  rfl

/-- Slicing (Fubini) along the first coordinate: for `g(x₀,‖x‖)` integrable on
`ℝ^{n+1}`, `∫ g(x₀,‖x‖) dx = ∫ dt ∫_{ℝ^n} g(t, √(t²+‖y‖²)) dy`.  Auxiliary to the
Lean proof route. -/
theorem integral_slice (n : ℕ) (g : ℝ → ℝ → ℂ)
    (hg : Integrable (fun x : Rd (n + 1) => g (x 0) ‖x‖)) :
    ∫ x : Rd (n + 1), g (x 0) ‖x‖ = ∫ t, ∫ y : Rd n, g t √(t ^ 2 + ‖y‖ ^ 2) := by
  set G : ℝ × Rd n → ℂ := fun p => g p.1 √(p.1 ^ 2 + ‖p.2‖ ^ 2)
  have key : (fun x : Rd (n + 1) => g (x 0) ‖x‖) = G ∘ splitFirst n := by
    funext x; simp only [G, Function.comp_apply, splitFirst_fst]; rw [← norm_splitFirst]
  have hG : Integrable G := by
    rw [← (splitFirst_mp n).integrable_comp_emb (splitFirst n).measurableEmbedding, ← key]; exact hg
  rw [key, Function.comp_def, (splitFirst_mp n).integral_comp (splitFirst n).measurableEmbedding G]
  exact integral_prod G hG


/-- `∫_{-1}^{1} (1-x²)^{-1/2} dx = π` (antiderivative `arcsin`).  Auxiliary to the Lean
proof route. -/
theorem integral_inv_sqrt_one_sub_sq : ∫ x in (-1 : ℝ)..1, (√(1 - x ^ 2))⁻¹ = π := by
  have hcont : ContinuousOn arcsin (Icc (-1) 1) := continuous_arcsin.continuousOn
  have hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt arcsin ((√(1 - x ^ 2))⁻¹) x := fun x hx => by
    simpa [one_div] using hasDerivAt_arcsin (by linarith [hx.1]) (by linarith [hx.2])
  have hint : IntervalIntegrable (fun x => (√(1 - x ^ 2))⁻¹) volume (-1) 1 := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := arcsin)
    · simpa [uIcc_of_le (show (-1 : ℝ) ≤ 1 by norm_num)] using hcont
    · intro x hx; simp at hx
      exact hd x ⟨hx.1, hx.2⟩
    · intro x _; positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hd hint]
  simp [arcsin_one, arcsin_neg]

/-- `∫_{-a}^{a} (a²-u²)^{-1/2} du = π` for `a > 0`.  Auxiliary to the Lean proof route. -/
theorem integral_inv_sqrt (a : ℝ) (ha : 0 < a) : ∫ u in (-a)..a, (√(a ^ 2 - u ^ 2))⁻¹ = π := by
  have h := intervalIntegral.integral_comp_mul_left (a := -1) (b := 1)
    (fun u => (√(a ^ 2 - u ^ 2))⁻¹) ha.ne'
  simp only [mul_neg, mul_one] at h
  have e : ∀ x : ℝ, (√(a ^ 2 - (a * x) ^ 2))⁻¹ = a⁻¹ * (√(1 - x ^ 2))⁻¹ := by
    intro x
    rw [show a ^ 2 - (a * x) ^ 2 = a ^ 2 * (1 - x ^ 2) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq ha.le, mul_inv]
  simp_rw [e] at h
  rw [intervalIntegral.integral_const_mul, integral_inv_sqrt_one_sub_sq, smul_eq_mul] at h
  exact (mul_left_cancel₀ (inv_ne_zero ha.ne') h).symm

/-- The `d = 2` slice: `∫_ℝ (2π√(c-u²))⁻¹ du` is `1/2` for `c > 0` and `0` for
`c ≤ 0` (the integrand vanishes where `c - u² ≤ 0` by the conventions
`√(negative) = 0`, `0⁻¹ = 0`; on `(-√c, √c)` it is the genuine density).  Auxiliary to
the Lean proof route. -/
theorem integral_slice_two (c : ℝ) :
    ∫ u : ℝ, (2 * π * √(c - u ^ 2))⁻¹ = if 0 < c then 1 / 2 else 0 := by
  split_ifs with hc
  · set a := √c with ha_def
    have ha : 0 < a := Real.sqrt_pos.2 hc
    have hca : c = a ^ 2 := (Real.sq_sqrt hc.le).symm
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (-a) a)]
    · rw [← intervalIntegral.integral_of_le (by linarith)]
      simp_rw [mul_inv, hca]
      rw [intervalIntegral.integral_const_mul, integral_inv_sqrt a ha]
      field_simp
    · intro u hu
      have : a ^ 2 ≤ u ^ 2 := by
        simp only [mem_Ioc, not_and_or, not_lt, not_le] at hu
        rcases hu with h | h <;> nlinarith
      rw [Real.sqrt_eq_zero'.2 (by linarith)]; simp
  · have : ∀ u : ℝ, (2 * π * √(c - u ^ 2))⁻¹ = 0 := fun u => by
      rw [Real.sqrt_eq_zero'.2 (by nlinarith [sq_nonneg u])]; simp
    simp [this]

/-- Auxiliary to the Lean proof route. -/
theorem measurable_radial2 (s : ℝ) : Measurable (radial2 s) := by
  unfold radial2
  exact (measurable_const.mul (measurable_const.sub (measurable_id.pow_const 2)).sqrt).inv

/-- The `d = 2` density `x ↦ (2π√(s²-‖x‖²))⁻¹ 1_{‖x‖<s}` is Lebesgue
integrable, `s > 0`.  Auxiliary to the Lean proof route. -/
theorem integrable_radial2 (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : Rd 2 => radial2 s ‖x‖) := by
  have hint : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ (Rd 2) - 1) • radial2 s y)
      (Ioi 0) := by
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
    have := (integral_radial2 s hs).1
    rw [show Ioi (0 : ℝ) = Ioc 0 s ∪ Ioi s from (Ioc_union_Ioi_eq_Ioi hs.le).symm]
    refine this.congr_fun (fun y _ => by simp) measurableSet_Ioc |>.union ?_
    refine integrableOn_zero.congr_fun (fun y hy => ?_) measurableSet_Ioi
    simp [radial2_eq_zero s y hs.le (le_of_lt hy)]
  exact (integrable_fun_norm_addHaar volume).2 hint

/-- `waveGreen 2 s` as a density measure with the radial density `radial2 s ‖x‖`
(equal to the indicator form of the definition, `s > 0`).  Auxiliary to the Lean proof route. -/
theorem waveGreen_two_eq (s : ℝ) (hs : 0 < s) :
    waveGreen 2 s = volume.withDensity fun x : Rd 2 => ENNReal.ofReal (radial2 s ‖x‖) := by
  show volume.withDensity _ = _
  congr 1
  funext x
  by_cases hx : x ∈ ball (0 : Rd 2) s
  · simp [hx, radial2]
  · rw [indicator_of_notMem hx, radial2_eq_zero s _ hs.le (by simpa using hx)]; simp

/-- Auxiliary to the Lean proof route. -/
theorem radial2_sqrt (s t u : ℝ) :
    radial2 s √(t ^ 2 + u ^ 2) = (2 * π * √((s ^ 2 - t ^ 2) - u ^ 2))⁻¹ := by
  unfold radial2
  rw [Real.sq_sqrt (by positivity)]; ring_nf

/-- The Fourier identity in `d = 2`: `∫ e^{iξ·x} G_s(dx) = Ĝ_s(ξ) =
sin(s|ξ|)/|ξ|` (`WaveKernel.waveHat`; main TeX lines 777-778, quoted at 4741
from the source's (2.3)-(2.5)) for `s > 0`, with integrability.  Proof route:
rotation of `ξ` to `|ξ|e₀`, slicing, and `∫_{-a}^{a}(a²-u²)^{-1/2} du = π`. -/
theorem waveGreen_fourier_two (s : ℝ) (hs : 0 < s) (ξ : Rd 2) :
    Integrable (fun x : Rd 2 => Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))
        (waveGreen 2 s) ∧
      ∫ x, Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) ∂(waveGreen 2 s) =
        (waveHat s ξ : ℂ) := by
  refine ⟨Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    (Filter.Eventually.of_forall fun x => ?_), ?_⟩
  · rw [Complex.norm_exp]; simp
  set k := ‖ξ‖
  rw [waveGreen_two_eq s hs, integral_withDensity_eq_integral_toReal_smul
    (show Measurable fun x : Rd 2 => ENNReal.ofReal (radial2 s ‖x‖) from
      ((measurable_radial2 s).comp measurable_norm).ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (radial2_nonneg _ _)]
  set g : ℝ → ℝ → ℂ := fun a r => (radial2 s r : ℂ) * Complex.exp (Complex.I * (a : ℂ))
  have h1 : (fun x : Rd 2 => radial2 s ‖x‖ • Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))
      = fun x => g (inner ℝ ξ x) ‖x‖ := by
    funext x; simp [g, Complex.real_smul]
  rw [h1, integral_inner_norm 1 ξ g]
  have hint : Integrable (fun x : Rd 2 => g (k * x 0) ‖x‖) := by
    refine Integrable.mono' (integrable_radial2 s hs) (by
      simp only [g]; have := measurable_radial2 s; fun_prop) (Filter.Eventually.of_forall
      fun x => ?_)
    simp only [g, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (radial2_nonneg _ _)]
    rw [show Complex.I * ((k * x 0 : ℝ) : ℂ) = ((k * x 0 : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  rw [integral_slice 1 (fun t r => g (k * t) r) hint]
  have hin : ∀ t : ℝ, ∫ y : Rd 1, g (k * t) √(t ^ 2 + ‖y‖ ^ 2) =
      (if 0 < s ^ 2 - t ^ 2 then (1 / 2 : ℂ) else 0) *
        Complex.exp (Complex.I * ((k * t : ℝ) : ℂ)) := by
    intro t
    simp only [g]
    rw [integral_mul_const, integral_complex_ofReal]
    congr 1
    have := coordOne_mp.integral_comp coordOne.measurableEmbedding
      (fun u : ℝ => radial2 s √(t ^ 2 + u ^ 2))
    simp only [coordOne_apply] at this
    have e2 : ∀ y : Rd 1, ‖y‖ ^ 2 = (y 0) ^ 2 := fun y => by rw [norm_coord_one, sq_abs]
    simp_rw [e2, this, radial2_sqrt, integral_slice_two]
    split_ifs <;> simp
  simp_rw [hin]
  have hset : (fun t : ℝ => (if 0 < s ^ 2 - t ^ 2 then (1 / 2 : ℂ) else 0) *
      Complex.exp (Complex.I * ((k * t : ℝ) : ℂ))) =
      (Ioo (-s) s).indicator
        fun t => (1 / 2 : ℂ) * Complex.exp (Complex.I * ((k * t : ℝ) : ℂ)) := by
    funext t
    by_cases ht : t ∈ Ioo (-s) s
    · have h : 0 < s ^ 2 - t ^ 2 := by have := ht.1; have := ht.2; nlinarith
      rw [indicator_of_mem ht]; simp [h]
    · have h : ¬ 0 < s ^ 2 - t ^ 2 := by
        simp only [mem_Ioo, not_and_or, not_lt] at ht
        rcases ht with h | h <;> nlinarith
      rw [indicator_of_notMem ht]; simp [h]
  rw [hset, integral_indicator measurableSet_Ioo, integral_const_mul, integral_exp_Ioo k s hs]
  have hn : ‖EuclideanSpace.single (0 : Fin 1) k‖ = k := by simp [k]
  simp only [waveHat, hn]
  push_cast; ring


/-- Auxiliary to the Lean proof route. -/
theorem norm_cexp_I (a : ℝ) : ‖Complex.exp (Complex.I * (a : ℂ))‖ = 1 := by
  rw [mul_comm, Complex.norm_exp_ofReal_mul_I]

/-- Polar coordinates in `ℝ³` with Mathlib's sphere measure:
`∫ f = ∫_{S²} ∫_0^∞ r² f(rω) dr σ(dω)` for integrable `f`
(`Measure.measurePreserving_homeomorphUnitSphereProd`, Fubini).  Auxiliary to the Lean
proof route. -/
theorem integral_polar3 (f : Rd 3 → ℂ) (hf : Integrable f) :
    ∫ x, f x = ∫ ω : sphere (0 : Rd 3) 1,
      (∫ r in Ioi (0 : ℝ), r ^ 2 • f (r • (ω : Rd 3))) ∂(volume : Measure (Rd 3)).toSphere := by
  have hmp : MeasurePreserving (homeomorphUnitSphereProd (Rd 3))
      ((volume : Measure (Rd 3)).comap Subtype.val)
      ((volume : Measure (Rd 3)).toSphere.prod (Measure.volumeIoiPow 2)) := by
    simpa using (volume : Measure (Rd 3)).measurePreserving_homeomorphUnitSphereProd
  set g : sphere (0 : Rd 3) 1 × Ioi (0 : ℝ) → ℂ := fun p => f (p.2.1 • (p.1 : Rd 3)) with hg_def
  have hcomp : g ∘ homeomorphUnitSphereProd (Rd 3) = fun x => f x.1 := by
    funext x
    have hx : ‖(x : Rd 3)‖ ≠ 0 := norm_ne_zero_iff.2 x.2
    simp [g, smul_smul, hx]
  have hint : Integrable g ((volume : Measure (Rd 3)).toSphere.prod (Measure.volumeIoiPow 2)) := by
    rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _), hcomp]
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).1 hf.integrableOn
  calc ∫ x, f x = ∫ x : ({(0 : Rd 3)}ᶜ : Set (Rd 3)), f x.1 ∂(volume.comap Subtype.val) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl fun x => f x,
          restrict_compl_singleton]
    _ = ∫ p, g p ∂((volume : Measure (Rd 3)).toSphere.prod (Measure.volumeIoiPow 2)) := by
        rw [← hmp.integral_comp (Homeomorph.measurableEmbedding _) g]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => (congrFun hcomp x).symm)
    _ = ∫ ω, ∫ r, g (ω, r) ∂(Measure.volumeIoiPow 2) ∂(volume : Measure (Rd 3)).toSphere :=
        integral_prod g hint
    _ = _ := by
        congr 1; funext ω
        simp only [Measure.volumeIoiPow, ENNReal.ofReal, g]
        rw [integral_withDensity_eq_integral_smul
          (measurable_subtype_coe.pow_const _).real_toNNReal,
          integral_subtype_comap measurableSet_Ioi
            fun a => Real.toNNReal (a ^ 2) • f (a • (ω : Rd 3))]
        refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
        rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _)]

/-- `Φ_ξ(r) = ∫_{S²} e^{i r ⟪ξ,ω⟫} σ(dω)`, `σ = volume.toSphere`.  Auxiliary to the Lean
proof route. -/
def spherePhi (ξ : Rd 3) (r : ℝ) : ℂ :=
  ∫ ω : sphere (0 : Rd 3) 1, Complex.exp (Complex.I * ((r * inner ℝ ξ (ω : Rd 3) : ℝ) : ℂ))
    ∂(volume : Measure (Rd 3)).toSphere

/-- Auxiliary to the Lean proof route. -/
theorem continuous_spherePhi (ξ : Rd 3) : Continuous (spherePhi ξ) := by
  refine continuous_of_dominated (bound := fun _ => 1) (fun r => by fun_prop)
    (fun r => Filter.Eventually.of_forall fun ω => ?_) (integrable_const _)
    (Filter.Eventually.of_forall fun ω => by fun_prop)
  rw [norm_cexp_I]

/-- The ball integral in polar coordinates:
`∫_{|x|<R} e^{iξ·x} dx = ∫_0^R r² Φ_ξ(r) dr`, `R > 0`.  Auxiliary to the Lean proof route. -/
theorem ball_polar (ξ : Rd 3) (R : ℝ) (hR : 0 < R) :
    ∫ x, (ball (0 : Rd 3) R).indicator
        (fun x => Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ))) x =
      ∫ r in (0 : ℝ)..R, ((r ^ 2 : ℝ) : ℂ) * spherePhi ξ r := by
  have hf : Integrable ((ball (0 : Rd 3) R).indicator
      (fun x => Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))) := by
    rw [integrable_indicator_iff measurableSet_ball]
    have : IsFiniteMeasure (volume.restrict (ball (0 : Rd 3) R)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_cexp_I]
  rw [integral_polar3 _ hf]
  set F : sphere (0 : Rd 3) 1 → ℝ → ℂ := fun ω r =>
    ((r ^ 2 : ℝ) : ℂ) * Complex.exp (Complex.I * ((r * inner ℝ ξ (ω : Rd 3) : ℝ) : ℂ))
  have hin : ∀ ω : sphere (0 : Rd 3) 1, ∫ r in Ioi (0 : ℝ), r ^ 2 •
      (ball (0 : Rd 3) R).indicator
        (fun x => Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ))) (r • (ω : Rd 3)) =
      ∫ r in Icc 0 R, F ω r := by
    intro ω
    have hω : ‖(ω : Rd 3)‖ = 1 := by simp
    rw [integral_Icc_eq_integral_Ioo, ← Ioi_inter_Iio, ← setIntegral_indicator measurableSet_Iio]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 < r := hr
    by_cases hrR : r < R
    · have hb : r • (ω : Rd 3) ∈ ball (0 : Rd 3) R := by
        simp [norm_smul, hω, abs_of_pos hr0, hrR]
      rw [indicator_of_mem hb, indicator_of_mem (show r ∈ Iio R from hrR)]
      simp [F, Complex.real_smul, real_inner_smul_right]
    · have hb : r • (ω : Rd 3) ∉ ball (0 : Rd 3) R := by
        simp [norm_smul, hω, abs_of_pos hr0]; linarith [not_lt.1 hrR]
      rw [indicator_of_notMem hb, indicator_of_notMem (show r ∉ Iio R from hrR)]
      simp
  simp_rw [hin]
  have hFint : Integrable (Function.uncurry F)
      (((volume : Measure (Rd 3)).toSphere).prod (volume.restrict (Icc (0 : ℝ) R))) := by
    refine Integrable.mono' (integrable_const (R ^ 2)) (by
      simp only [F]; exact (by fun_prop : Continuous (Function.uncurry F)).aestronglyMeasurable) ?_
    rw [← Measure.restrict_univ (μ := (volume : Measure (Rd 3)).toSphere), Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (MeasurableSet.univ.prod measurableSet_Icc) fun p hp => ?_
    simp only [F, Function.uncurry, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_I,
      mul_one]
    have := hp.2
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ this.1 this.2 2
  rw [integral_integral_swap hFint, intervalIntegral.integral_of_le hR.le,
    ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
  simp only [F, spherePhi]
  rw [integral_const_mul]


/-- The ball integral by rotation and slicing:
`∫_{|x|<R} e^{iξ·x} dx = ∫_{-R}^{R} π(R²-t²) e^{i|ξ|t} dt`, `R > 0` (the slice at
height `t` is a disc of area `π(R²-t²)`).  Auxiliary to the Lean proof route. -/
theorem ball_slice (ξ : Rd 3) (R : ℝ) (hR : 0 < R) :
    ∫ x, (ball (0 : Rd 3) R).indicator
        (fun x => Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ))) x =
      ∫ t in (-R)..R, ((π * (R ^ 2 - t ^ 2) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((‖ξ‖ * t : ℝ) : ℂ)) := by
  set k := ‖ξ‖
  set g : ℝ → ℝ → ℂ := fun a r => if r < R then Complex.exp (Complex.I * (a : ℂ)) else 0
  have h1 : (ball (0 : Rd 3) R).indicator
      (fun x => Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ))) =
      fun x => g (inner ℝ ξ x) ‖x‖ := by
    funext x
    by_cases hx : x ∈ ball (0 : Rd 3) R
    · rw [indicator_of_mem hx]; simp [g, show ‖x‖ < R by simpa using hx]
    · rw [indicator_of_notMem hx]; simp [g, show ¬ ‖x‖ < R by simpa using hx]
  have hint : Integrable (fun x : Rd 3 => g (k * x 0) ‖x‖) := by
    have : IsFiniteMeasure (volume.restrict (ball (0 : Rd 3) R)) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have e : (fun x : Rd 3 => g (k * x 0) ‖x‖) = (ball (0 : Rd 3) R).indicator
        (fun x => Complex.exp (Complex.I * ((k * x 0 : ℝ) : ℂ))) := by
      funext x
      by_cases hx : x ∈ ball (0 : Rd 3) R
      · rw [indicator_of_mem hx]; simp [g, show ‖x‖ < R by simpa using hx]
      · rw [indicator_of_notMem hx]; simp [g, show ¬ ‖x‖ < R by simpa using hx]
    rw [e, integrable_indicator_iff measurableSet_ball]
    refine Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_cexp_I]
  rw [h1, integral_inner_norm 2 ξ g, integral_slice 2 (fun t r => g (k * t) r) hint]
  have hin : ∀ t : ℝ, ∫ y : Rd 2, g (k * t) √(t ^ 2 + ‖y‖ ^ 2) =
      ((π * (√(R ^ 2 - t ^ 2)) ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((k * t : ℝ) : ℂ)) := by
    intro t
    have e : (fun y : Rd 2 => g (k * t) √(t ^ 2 + ‖y‖ ^ 2)) =
        (ball (0 : Rd 2) √(R ^ 2 - t ^ 2)).indicator
          (fun _ => Complex.exp (Complex.I * ((k * t : ℝ) : ℂ))) := by
      funext y
      have hiff : √(t ^ 2 + ‖y‖ ^ 2) < R ↔ y ∈ ball (0 : Rd 2) √(R ^ 2 - t ^ 2) := by
        rw [mem_ball_zero_iff, Real.sqrt_lt' hR, Real.lt_sqrt (norm_nonneg y)]
        constructor <;> intro h <;> linarith
      by_cases hy : y ∈ ball (0 : Rd 2) √(R ^ 2 - t ^ 2)
      · rw [indicator_of_mem hy]; simp [g, hiff.2 hy]
      · rw [indicator_of_notMem hy]; simp [g, show ¬ _ from fun h => hy (hiff.1 h)]
    rw [e, integral_indicator_const _ measurableSet_ball, measureReal_def,
      EuclideanSpace.volume_ball_fin_two]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ENNReal.toReal_ofReal Real.pi_pos.le,
      Complex.real_smul]
    push_cast; ring
  simp_rw [hin]
  rw [intervalIntegral.integral_of_le (by linarith),
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioc (-R) R)]
  · refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have : 0 ≤ R ^ 2 - t ^ 2 := by have := ht.1; have := ht.2; nlinarith
    simp only [Real.sq_sqrt this]
  · intro t ht
    have : R ^ 2 - t ^ 2 ≤ 0 := by
      simp only [mem_Ioc, not_and_or, not_lt, not_le] at ht
      rcases ht with h | h <;> nlinarith
    simp [Real.sqrt_eq_zero'.2 this]


/-- `∫_{-R}^{R} e^{ikt} dt = 2R sinc(kR)`, `k ≥ 0`, `R > 0`.  Auxiliary to the Lean proof route. -/
theorem integral_exp_sym (k R : ℝ) (hk : 0 ≤ k) (hR : 0 < R) :
    ∫ t in (-R)..R, Complex.exp (Complex.I * ((k * t : ℝ) : ℂ)) =
      ((2 * R * Real.sinc (k * R) : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
    integral_exp_Ioo k R hR]
  have hn : ‖EuclideanSpace.single (0 : Fin 1) k‖ = k := by simp [abs_of_nonneg hk]
  simp only [waveHat, hn]
  push_cast; ring_nf

/-- `R ↦ ∫_{-R}^{R} π(R²-t²)e^{ikt} dt` has derivative `4πR² sinc(kR)` at
`R > 0`, `k ≥ 0`.  Auxiliary to the Lean proof route. -/
theorem hasDerivAt_ballSlice (k R : ℝ) (hk : 0 ≤ k) (hR : 0 < R) :
    HasDerivAt (fun R => ∫ t in (-R)..R, ((π * (R ^ 2 - t ^ 2) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((k * t : ℝ) : ℂ)))
      ((4 * π * R ^ 2 * Real.sinc (k * R) : ℝ) : ℂ) R := by
  set e : ℝ → ℂ := fun t => Complex.exp (Complex.I * ((k * t : ℝ) : ℂ)) with he_def
  have he : Continuous e := by fun_prop
  have he2 : Continuous fun t : ℝ => ((t ^ 2 : ℝ) : ℂ) * e t := by fun_prop
  set F0 : ℝ → ℂ := fun u => ∫ t in (0 : ℝ)..u, e t
  set F2 : ℝ → ℂ := fun u => ∫ t in (0 : ℝ)..u, ((t ^ 2 : ℝ) : ℂ) * e t
  have hF0 : ∀ u, HasDerivAt F0 (e u) u := fun u =>
    (he.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hF2 : ∀ u, HasDerivAt F2 (((u ^ 2 : ℝ) : ℂ) * e u) u := fun u =>
    (he2.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hs0 : ∀ R, F0 R - F0 (-R) = ∫ t in (-R)..R, e t := fun R =>
    intervalIntegral.integral_interval_sub_left (he.intervalIntegrable 0 R)
      (he.intervalIntegrable 0 (-R))
  have hs2 : ∀ R, F2 R - F2 (-R) = ∫ t in (-R)..R, ((t ^ 2 : ℝ) : ℂ) * e t := fun R =>
    intervalIntegral.integral_interval_sub_left (he2.intervalIntegrable 0 R)
      (he2.intervalIntegrable 0 (-R))
  have hsplit : (fun R : ℝ => ∫ t in (-R)..R, ((π * (R ^ 2 - t ^ 2) : ℝ) : ℂ) * e t) =
      fun R => ((π * R ^ 2 : ℝ) : ℂ) * (F0 R - F0 (-R)) - (π : ℂ) * (F2 R - F2 (-R)) := by
    funext R
    rw [hs0, hs2, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((he.const_mul _).intervalIntegrable _ _)
        ((he2.const_mul _).intervalIntegrable _ _)]
    congr 1; funext t; push_cast; ring
  rw [hsplit]
  have hq : HasDerivAt (fun R : ℝ => ((π * R ^ 2 : ℝ) : ℂ)) ((2 * π * R : ℝ) : ℂ) R := by
    have := ((hasDerivAt_pow 2 R).const_mul π).ofReal_comp
    convert this using 2; push_cast; ring
  have hn0 : HasDerivAt (fun R => F0 (-R)) ((-1 : ℝ) • e (-R)) R :=
    (hF0 (-R)).scomp R (hasDerivAt_neg R)
  have hn2 : HasDerivAt (fun R => F2 (-R)) ((-1 : ℝ) • ((((-R) ^ 2 : ℝ) : ℂ) * e (-R))) R :=
    (hF2 (-R)).scomp R (hasDerivAt_neg R)
  have hd := (hq.mul ((hF0 R).sub hn0)).sub (((hF2 R).sub hn2).const_mul (π : ℂ))
  refine hd.congr_deriv ?_
  simp only [Pi.sub_apply]
  rw [hs0, integral_exp_sym k R hk hR]
  simp only [Complex.real_smul]
  push_cast; ring

/-- `Φ_ξ(1) = 4π sinc|ξ|`: the two ball integrals agree for `R > 0`, so their
`R`-derivatives at `R = 1` agree.  Auxiliary to the Lean proof route. -/
theorem sphere_fourier_aux (ξ : Rd 3) : spherePhi ξ 1 = ((4 * π * Real.sinc ‖ξ‖ : ℝ) : ℂ) := by
  have hc : Continuous fun r : ℝ => ((r ^ 2 : ℝ) : ℂ) * spherePhi ξ r := by
    have := continuous_spherePhi ξ; fun_prop
  have hA := (hc.integral_hasStrictDerivAt 0 1).hasDerivAt
  have hB := hasDerivAt_ballSlice ‖ξ‖ 1 (norm_nonneg _) one_pos
  have heq : (fun R => ∫ r in (0 : ℝ)..R, ((r ^ 2 : ℝ) : ℂ) * spherePhi ξ r) =ᶠ[𝓝 1]
      (fun R => ∫ t in (-R)..R, ((π * (R ^ 2 - t ^ 2) : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((‖ξ‖ * t : ℝ) : ℂ))) := by
    filter_upwards [Ioi_mem_nhds one_pos] with R hR
    rw [← ball_polar ξ R hR, ball_slice ξ R hR]
  have := hA.unique (hB.congr_of_eventuallyEq heq)
  simpa using this

/-- The Fourier transform of Mathlib's unit-sphere measure in `ℝ³`:
`∫_{S²} e^{iξ·ω} σ(dω) = 4π sinc|ξ|` (`sinc 0 = 1`), with integrability, for
every `ξ`, where `σ = volume.toSphere`.  No rotation invariance of `toSphere`
is used (Mathlib has none); the identity comes from computing
`∫_{|x|<R} e^{iξ·x} dx` in polar coordinates and by slicing.  This is the
`d = 3` core of the Fourier identity (main TeX lines 777-778, 4741). -/
theorem sphere_fourier (ξ : Rd 3) :
    Integrable (fun ω : sphere (0 : Rd 3) 1 =>
        Complex.exp (Complex.I * ((inner ℝ ξ (ω : Rd 3) : ℝ) : ℂ)))
        (volume : Measure (Rd 3)).toSphere ∧
      ∫ ω : sphere (0 : Rd 3) 1, Complex.exp (Complex.I * ((inner ℝ ξ (ω : Rd 3) : ℝ) : ℂ))
          ∂(volume : Measure (Rd 3)).toSphere = ((4 * π * Real.sinc ‖ξ‖ : ℝ) : ℂ) := by
  refine ⟨Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    (Filter.Eventually.of_forall fun x => by rw [norm_cexp_I]), ?_⟩
  rw [← sphere_fourier_aux ξ]
  simp [spherePhi]

/-- The Fourier identity in `d = 3`: `∫ e^{iξ·x} G_s(dx) = Ĝ_s(ξ) =
sin(s|ξ|)/|ξ|` (`WaveKernel.waveHat`; main TeX lines 777-778, quoted at 4741
from the source's (2.3)-(2.5)) for `s > 0`, with integrability.  `G_s =
waveGreen 3 s` is the definitional choice `(s/(4π)) · map (ω ↦ sω) toSphere`
recorded in `WaveGreen`. -/
theorem waveGreen_fourier_three (s : ℝ) (hs : 0 < s) (ξ : Rd 3) :
    Integrable (fun x : Rd 3 => Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))
        (waveGreen 3 s) ∧
      ∫ x, Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) ∂(waveGreen 3 s) =
        (waveHat s ξ : ℂ) := by
  refine ⟨Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    (Filter.Eventually.of_forall fun x => by rw [norm_cexp_I]), ?_⟩
  show ∫ x, _ ∂(ENNReal.ofReal (s / (4 * π)) •
      ((volume : Measure (Rd 3)).toSphere.map fun ω : sphere (0 : Rd 3) 1 => s • (ω : Rd 3))) = _
  rw [integral_smul_measure, integral_map (by fun_prop) (by fun_prop)]
  have e : ∀ ω : sphere (0 : Rd 3) 1, inner ℝ ξ (s • (ω : Rd 3)) = inner ℝ (s • ξ) (ω : Rd 3) :=
    fun ω => by rw [real_inner_smul_left, real_inner_smul_right]
  simp_rw [e]
  rw [(sphere_fourier (s • ξ)).2, ENNReal.toReal_ofReal (by positivity)]
  simp only [waveHat, norm_smul, Real.norm_eq_abs, abs_of_pos hs, Complex.real_smul]
  have := Real.pi_pos.ne'
  push_cast; field_simp

/-- Archimedes' law for Mathlib's unit-sphere measure in `ℝ³`: for a unit
vector `e`, the image of `σ = volume.toSphere` under `ω ↦ ⟪e,ω⟫` is `2π` times
Lebesgue measure on `[-1,1]`.  Proof: equality of characteristic functions
(`Measure.ext_of_charFun`), both being `4π sinc t` by `sphere_fourier`.  This
is the image law behind the computations "direct integration over its normal
coordinate" (main TeX lines 2125-2131, proof of `L:phase-contractions`) and
"In dimension three spherical coordinates give" (lines 5189-5194, proof of
`L:higher-riesz`); neither computation is formalized here. -/
theorem archimedes (e : Rd 3) (he : ‖e‖ = 1) :
    ((volume : Measure (Rd 3)).toSphere).map
        (fun ω : sphere (0 : Rd 3) 1 => inner ℝ e (ω : Rd 3)) =
      ENNReal.ofReal (2 * π) • (volume : Measure ℝ).restrict (Icc (-1) 1) := by
  have : IsFiniteMeasure (ENNReal.ofReal (2 * π) • (volume : Measure ℝ).restrict (Icc (-1) 1)) :=
    ⟨by simp [Measure.smul_apply, ENNReal.mul_lt_top]⟩
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_apply_real, charFun_apply_real, integral_map (by fun_prop) (by fun_prop),
    integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    integral_Icc_eq_integral_Ioo]
  have h1 : ∀ ω : sphere (0 : Rd 3) 1, Complex.exp (t * (inner ℝ e (ω : Rd 3) : ℝ) * Complex.I) =
      Complex.exp (Complex.I * ((inner ℝ (t • e) (ω : Rd 3) : ℝ) : ℂ)) := fun ω => by
    rw [real_inner_smul_left]; push_cast; ring_nf
  have h2 : ∀ x : ℝ, Complex.exp (t * x * Complex.I) =
      Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) := fun x => by push_cast; ring_nf
  simp_rw [h1, h2]
  rw [(sphere_fourier (t • e)).2, integral_exp_Ioo t 1 one_pos]
  have hn : ‖EuclideanSpace.single (0 : Fin 1) t‖ = |t| := by simp
  have hs : Real.sinc |t| = Real.sinc t := by
    rcases abs_choice t with h | h <;> rw [h]; exact Real.sinc_neg t
  simp only [waveHat, hn, norm_smul, Real.norm_eq_abs, he, mul_one, one_mul, hs,
    Complex.real_smul]
  push_cast; ring

/-! ### Integral forms of Archimedes' law -/

/-- Archimedes' law, lower-integral form: for a unit vector `e` and measurable
`f : ℝ → [0,∞]`, `∫_{S²} f(⟪e,ω⟫) σ(dω) = 2π ∫_{-1}^{1} f(t) dt`. -/
theorem lintegral_sphere_inner (e : Rd 3) (he : ‖e‖ = 1) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ ω : sphere (0 : Rd 3) 1, f (inner ℝ e (ω : Rd 3)) ∂(volume : Measure (Rd 3)).toSphere =
      ENNReal.ofReal (2 * π) * ∫⁻ t in Icc (-1 : ℝ) 1, f t := by
  rw [← lintegral_map hf (by fun_prop), archimedes e he, lintegral_smul_measure, smul_eq_mul]

/-- Archimedes' law, integrability form: if `f` is integrable on `[-1,1]`, then
`ω ↦ f(⟪e,ω⟫)` is `σ`-integrable (`‖e‖ = 1`). -/
theorem integrable_sphere_inner (e : Rd 3) (he : ‖e‖ = 1) {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (hf : IntegrableOn f (Icc (-1 : ℝ) 1)) :
    Integrable (fun ω : sphere (0 : Rd 3) 1 => f (inner ℝ e (ω : Rd 3)))
      (volume : Measure (Rd 3)).toSphere := by
  have hm : AEMeasurable (fun ω : sphere (0 : Rd 3) 1 => inner ℝ e (ω : Rd 3))
      (volume : Measure (Rd 3)).toSphere := by fun_prop
  have : Integrable f (((volume : Measure (Rd 3)).toSphere).map
      fun ω : sphere (0 : Rd 3) 1 => inner ℝ e (ω : Rd 3)) := by
    rw [archimedes e he]; exact hf.smul_measure ENNReal.ofReal_ne_top
  exact this.comp_aemeasurable hm

/-- Archimedes' law, Bochner form: for a unit vector `e` and `f` integrable on
`[-1,1]`, `∫_{S²} f(⟪e,ω⟫) σ(dω) = 2π ∫_{-1}^{1} f(t) dt`, with integrability
(`integrable_sphere_inner`). -/
theorem integral_sphere_inner (e : Rd 3) (he : ‖e‖ = 1) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (hf : IntegrableOn f (Icc (-1 : ℝ) 1)) :
    Integrable (fun ω : sphere (0 : Rd 3) 1 => f (inner ℝ e (ω : Rd 3)))
        (volume : Measure (Rd 3)).toSphere ∧
      ∫ ω : sphere (0 : Rd 3) 1, f (inner ℝ e (ω : Rd 3)) ∂(volume : Measure (Rd 3)).toSphere =
        (2 * π) • ∫ t in Icc (-1 : ℝ) 1, f t := by
  refine ⟨integrable_sphere_inner e he f hf, ?_⟩
  have hm : AEMeasurable (fun ω : sphere (0 : Rd 3) 1 => inner ℝ e (ω : Rd 3))
      (volume : Measure (Rd 3)).toSphere := by fun_prop
  have hfm : AEStronglyMeasurable f (((volume : Measure (Rd 3)).toSphere).map
      fun ω : sphere (0 : Rd 3) 1 => inner ℝ e (ω : Rd 3)) := by
    rw [archimedes e he]; exact hf.aestronglyMeasurable.smul_measure _
  rw [← integral_map hm hfm, archimedes e he, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)]

/-! ### The Fourier identity in `d ∈ {1,2,3}` -/

/-- The Fourier identity of the wave Green measures for `d ∈ {1,2,3}`:
`∫ e^{iξ·x} G_s(dx) = Ĝ_s(ξ) = s sinc(s|ξ|)` (`WaveKernel.waveHat`, main TeX lines
777-778 and 4741) for `s > 0` and every `ξ`, with integrability.  `d = 1` is
`WaveGreen.waveGreen_fourier_one`; the `d = 3` measure is the definitional choice
of `WaveGreen`. -/
theorem waveGreen_fourier (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (s : ℝ) (hs : 0 < s)
    (ξ : Rd d) :
    Integrable (fun x : Rd d => Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))
        (waveGreen d s) ∧
      ∫ x, Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) ∂(waveGreen d s) =
        (waveHat s ξ : ℂ) := by
  rcases hd with rfl | rfl | rfl
  · exact waveGreen_fourier_one s hs ξ
  · exact waveGreen_fourier_two s hs ξ
  · exact waveGreen_fourier_three s hs ξ

/-- `waveHat h ξ = sin(h|ξ|)/|ξ|` for `ξ ≠ 0` and `= h` at `ξ = 0` (`h > 0`), the
form written at main TeX lines 777-778 and 4741.  Auxiliary to the Lean proof
route. -/
theorem waveHat_eq_sin_div (d : ℕ) (h : ℝ) (hh : 0 < h) (ξ : Rd d) :
    waveHat h ξ = if ξ = 0 then h else Real.sin (h * ‖ξ‖) / ‖ξ‖ := by
  unfold waveHat
  split_ifs with hξ
  · simp [hξ]
  · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
    rw [Real.sinc_of_ne_zero (mul_ne_zero hh.ne' hn)]
    field_simp

/-- The display at main TeX lines 4740-4744 (proof of `L:low-alpha-convolution`,
quoted from the source's (2.3)-(2.5)), for the wave Green measures in
`d ∈ {1,2,3}` (the dimension clause of `H:homog`) and `h > 0`:
`∫ e^{iξ·x} G_h(dx) = sin(h|ξ|)/|ξ|`, with value `h` at `ξ = 0`, with
integrability, and `G_h(ℝ^d) = h`.  The `d = 3` measure is the definitional
choice of `WaveGreen`. -/
theorem waveGreen_fourier_paper (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) (h : ℝ) (hh : 0 < h)
    (ξ : Rd d) :
    Integrable (fun x : Rd d => Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)))
        (waveGreen d h) ∧
      ∫ x, Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) ∂(waveGreen d h) =
        ((if ξ = 0 then h else Real.sin (h * ‖ξ‖) / ‖ξ‖ : ℝ) : ℂ) ∧
      waveGreen d h univ = ENNReal.ofReal h := by
  obtain ⟨h1, h2⟩ := waveGreen_fourier d hd h hh ξ
  exact ⟨h1, by rw [h2, waveHat_eq_sin_div d h hh ξ], waveGreen_mass d hd h hh.le⟩

/-! ### The Fourier input of `DampedMultiplier` in every `d` -/

/-- `DampedMultiplier.GreenFourier (waveGreen d)` for `d ∈ {1,2,3}`: the wave
Green measures are finite and their characteristic functions are `waveHat s`
for `s > 0` (main TeX lines 777-778).  Extends `greenFourier_one`. -/
theorem greenFourier (d : ℕ) (hd : d = 1 ∨ d = 2 ∨ d = 3) : GreenFourier (waveGreen d) := by
  refine ⟨fun s _ => isFiniteMeasure_waveGreen d s, fun s hs ξ => ?_⟩
  rw [charFun_apply, ← (waveGreen_fourier d hd s hs ξ).2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [real_inner_comm, mul_comm]

/-- `L:damped-homogeneous-norms` (main TeX lines 803-919), the second norm of the
wave Green measures and of their Gaussian smoothing, under `H:homog` alone, in
every `d` (`d ∈ {1,2,3}` from `h.dim`; `GreenFourier (waveGreen d)` discharged
by `greenFourier`): for `v ≥ 0`, `θ > 0` and measurable `S ⊆ S'`, the second
norm of `waveGreen d` is `N2onSq α₀ θ S μ`, that of the Gaussian-smoothed family
`p * G` is `N_{2,m,S}(θ)²` with `m = e^{-v|ξ|²}`, all four outer integrands are
integrable, and `0 ≤ N_{2,m,S}(θ)² ≤ N_{2,1,S'}(θ)²` (lines 845-847, 915-917).
The conclusions are those of `DampedMultiplier.damped_homogeneous_norms_fourier_paper`
with `G := waveGreen d`; in `d = 1` this is
`DampedMultiplier.damped_homogeneous_norms_fourier_one`. -/
theorem damped_homogeneous_norms_fourier_wave {d : ℕ} {alpha alpha0 : ℝ}
    {Γ μ : Measure (Rd d)} (h : HomogCovariance d alpha alpha0 Γ μ) (v : ℝ) (hv : 0 ≤ v)
    (θ : ℝ) (hθ : 0 < θ) (S S' : Set ℝ) (hS : MeasurableSet S) (hS' : MeasurableSet S')
    (hSS : S ⊆ S') :
    Integrable (N2GreenOuter alpha0 θ S μ (waveGreen d)) P2 ∧
      N2GreenSq alpha0 θ S μ (waveGreen d) = (N2onSq alpha0 θ S μ : ℂ) ∧
      Integrable (N2GreenOuter alpha0 θ S μ (fun s => gaussKernel v ∗ waveGreen d s)) P2 ∧
      N2GreenSq alpha0 θ S μ (fun s => gaussKernel v ∗ waveGreen d s) =
        (N2onSq alpha0 θ S (smoothed μ (gaussMult v)) : ℂ) ∧
      Integrable (N2onOuter alpha0 θ S (smoothed μ (gaussMult v))) P2 ∧
      Integrable (N2onOuter alpha0 θ S' μ) P2 ∧
      0 ≤ N2onSq alpha0 θ S (smoothed μ (gaussMult v)) ∧
      N2onSq alpha0 θ S (smoothed μ (gaussMult v)) ≤ N2onSq alpha0 θ S' μ :=
  damped_homogeneous_norms_fourier_paper h (greenFourier d h.dim) v hv θ hθ S S' hS hS' hSS

end StratonovichHAMSecondMoment.WaveGreenFourier
