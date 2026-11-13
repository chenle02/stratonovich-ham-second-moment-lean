module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`P:masked-auxiliary-norm` (Auxiliary mask norm) of
`notes/integrated_covariance_foundation.tex` (revision a284420): statement
lines 88-100, proof lines 102-137, with the definitions of lines 79-86
(`ζ_R`, `k_R`, `L`, `E:masked-auxiliary-measure`) and the unitary Fourier
transform of lines 8-12.

Definitions (in the manuscript's convention, not Mathlib's):
* `cd d = (2π)^{-d/2}` and `paperHat f ξ = c_d ∫ e^{-iξ·x} f(x) dx` for `f`
  with values in a complex normed space (lines 8-12);
  `integrable_paperHat_integrand`: for a Schwartz map the defining integrand
  is integrable;
* `zetaR ζ R x = ζ(x/R)`, `kR ζ R = (ζ_R)^`, `Lz ζ = ‖ζ̂‖₁` (lines 79-80);
* `rho μ ζ R η = c_d² L ∫ |k_R(ξ-η)| μ(dξ)` as an `ℝ≥0∞`-valued lower
  integral of a nonnegative function, and `nu μ ζ R = ρ_R dη`
  (`E:masked-auxiliary-measure`, lines 83-86).

Formalized:
* lines 80-82: `kR_scale` (`k_R(u) = R^d ζ̂(Ru)`), `integral_norm_kR`
  (`‖k_R‖₁ = L`, with `integrable_kR`), `Lz_pos` (`ζ̂` integrable and `L > 0`
  for `ζ ≠ 0`);
* `masked_auxiliary_norm_paper`, under the section's standing assumptions
  (lines 5-6) `H:homog` (`HomogHypothesis.HomogCovariance`) and `Γ ≠ 0`, with
  `ζ` a real nonzero Schwartz function, `R > 0`, `H` a separable complex
  Hilbert space and `F` an `H`-valued Schwartz map: `L > 0`, `‖k_R‖₁ = L`,
  `ν_R` is even (`IsEven`), tempered (`IsTempered`) and Radon
  (`IsLocallyFiniteMeasure`, as in `HomogCovariance`);
  `ν_R(B(y,r)) ≤ c_d² L² C_Γ r^α` for open and closed balls, for all `y`,
  `r > 0`, with a bound that does not depend on `R`
  (`E:masked-auxiliary-growth`); and `E:masked-hilbert-fourier`
  `∫ ‖(ζ_R F)^(ξ)‖² μ(dξ) ≤ ∫ ‖F̂(η)‖² ν_R(dη)` with both integrands integrable,
  stated both for Bochner integrals and for lower integrals, together with the
  finiteness of the right side (lines 134-135).  `C_Γ` is
  `MaskedSpectralGrowth.CGamma`.
* The general form `masked_auxiliary_norm` assumes only: `μ` s-finite,
  tempered and even, the spectral convention `IsSpectralMeasure Γ μ`, the
  scaling `Γ(cA) = c^{d-α}Γ(A)` (`SpectralHomogeneous Γ (d - α)`), `ζ ≠ 0`,
  and `E` any complex Banach space (no inner product, no separability).  Its
  constant `C_Γ` involves the Bochner integral `M_Γ`; it is the manuscript's
  constant when `Γ` is tempered (`MaskedSpectralGrowth.MGamma_pos`), as under
  `H:homog`.  The pieces carry their own minimal hypotheses
  (`nu_closedBall_le`, `isTempered_nu`, `isEven_nu`,
  `masked_hilbert_fourier`, ...).

Hypotheses of `H:homog` used by the wrapper: `μ_radon` (only to make `μ`
s-finite), `μ_tempered`, `μ_even`, `spectral`, `scaling`; the other fields,
`Γ ≠ 0`, the inner product and the separability of `H` are carried, unused.

Supplied inputs: none.  The fallback of the wave plan (convolution identity
supplied) was not needed.

Narrower than the TeX:
* the last sentence of the proposition, "For a real `H`, the same assertion
  holds after complexification" (line 99), is not formalized (Mathlib has no
  complexification of a real Hilbert space);
* the proof's intermediate claims that `ρ_R` is finite everywhere and
  continuous (lines 103-106) are not formalized: they are not part of the
  statement, and the Lean route proves local finiteness of `ν_R` from the
  ball bound instead.

Implicit hypotheses made explicit: `μ` s-finite for the Tonelli steps
(derived from `μ_radon` in the wrapper); integrability of every integrand
whose Bochner integral is stated; the balls are `Metric.ball y r` and
`Metric.closedBall y r`.

Proof route (differences from the TeX).
* The transform is related to Mathlib's `𝓕` (kernel `e^{-2πi⟨x,w⟩}`) by
  `paperHat_eq_fourier`; inversion in the paper's convention
  (`paper_inversion`) comes from `Continuous.fourierInv_fourier_eq` and the
  change of variables `w = η/(2π)`; Schwartz properties of `F̂` and `k_R` come
  from `SchwartzMap.fourierTransformCLM` composed with a dilation (`hatS`).
* `L > 0` by Fourier injectivity (the TeX states it without proof).
* Ball bound: Tonelli twice and the substitution `u = ξ - η`, then
  `MaskedSpectralGrowth.closedBall_le` at every center, as in lines 108-113.
* Radon: from the ball bound, not from the continuity of `ρ_R`.
* Tempered: Peetre's inequality
  `(1+|η|)^{-N} ≤ (1+|ξ|)^{-N}(1+|ξ-η|)^N` and the Schwartz decay of `k_R`
  give `∫(1+|η|)^{-N} dν_R ≤ c_d² L (∫(1+|ξ|)^{-N} dμ)(∫(1+|u|)^N|k_R(u)|du)`
  with the exponent `N` of `μ`; this replaces the "same dyadic argument" of
  lines 113-114 and is simpler.
* Even: `k_R(-u) = conj k_R(u)` (`ζ` real) and the evenness of `μ`, as in
  lines 106-107.
* Convolution identity `(ζ_R F)^(ξ) = c_d ∫ k_R(ξ-η) F̂(η) dη` (lines 116-120):
  Fourier inversion of `F` and one Bochner Fubini swap in the Banach space
  directly (`paperHat_mask`); the scalar, finite-rank and projection steps of
  lines 121-127 are not needed.  Weighted Cauchy-Schwarz (lines 127-132) is
  proved by the nonnegativity of the quadratic `t ↦ ∫ a (g - t)²`
  (`sq_integral_mul_le`); the final Tonelli step (lines 133-134) is
  `lintegral_nu`.
Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.MaskedSpectralGrowth

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Real Metric
open scoped ENNReal NNReal FourierTransform

namespace StratonovichHAMSecondMoment.MaskedAuxiliaryNorm

open HomogHypothesis SpectralHomog MaskedSpectralGrowth

variable {d : ℕ}

/-! ### The unitary Fourier transform of the section -/

/-- `c_d = (2π)^{-d/2}` (line 11). -/
def cd (d : ℕ) : ℝ := (2 * π) ^ (-(d : ℝ) / 2)

/-- Auxiliary to the Lean proof route. -/
theorem cd_pos (d : ℕ) : 0 < cd d := Real.rpow_pos_of_pos (by positivity) _

/-- Auxiliary to the Lean proof route. `c_d² (2π)^d = 1`. -/
theorem cd_sq_mul (d : ℕ) : cd d ^ 2 * (2 * π) ^ d = 1 := by
  have h2 : (0 : ℝ) < 2 * π := by positivity
  rw [cd, ← Real.rpow_natCast ((2 * π) ^ (-(d : ℝ) / 2)) 2, ← Real.rpow_mul h2.le,
    ← Real.rpow_natCast (2 * π) d, ← Real.rpow_add h2]
  norm_num

/-- The unitary Fourier transform of the section (lines 8-12), for a function
with values in a complex normed space `E`:
`f̂(ξ) = c_d ∫ e^{-i ξ·x} f(x) dx`. -/
def paperHat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Rd d → E)
    (ξ : Rd d) : E :=
  (cd d : ℂ) • ∫ x, Complex.exp (-(Complex.I * (inner ℝ ξ x : ℝ))) • f x

section Fourier

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Auxiliary to the Lean proof route. The section's transform in terms of
Mathlib's Fourier transform `𝓕 f(w) = ∫ e^{-2πi⟨v,w⟩} f(v) dv`:
`f̂(ξ) = c_d 𝓕 f(ξ/(2π))`. -/
theorem paperHat_eq_fourier (f : Rd d → E) (ξ : Rd d) :
    paperHat f ξ = (cd d : ℂ) • 𝓕 f ((2 * π)⁻¹ • ξ) := by
  rw [paperHat, Real.fourier_eq']
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  congr 2
  rw [real_inner_smul_right, real_inner_comm]
  have hπ : (2 * π) ≠ 0 := by positivity
  push_cast
  field_simp

/-- The defining integral of the transform converges for a Schwartz map: the
integrand `x ↦ e^{-iξ·x} f(x)` is integrable, so `paperHat` of a Schwartz map
is never a junk value. -/
theorem integrable_paperHat_integrand (f : SchwartzMap (Rd d) E) (ξ : Rd d) :
    Integrable (fun x => Complex.exp (-(Complex.I * (inner ℝ ξ x : ℝ))) • f x) := by
  refine f.integrable.norm.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_smul, Complex.norm_exp]
  simp

/-- Auxiliary to the Lean proof route. The dilation `x ↦ c • x` (`c ≠ 0`) as a
continuous linear equivalence. -/
def dil (c : ℝ) (hc : c ≠ 0) : Rd d ≃L[ℝ] Rd d :=
  (LinearEquiv.smulOfNeZero ℝ (Rd d) c hc).toContinuousLinearEquiv

/-- Auxiliary to the Lean proof route. -/
@[simp] theorem dil_apply (c : ℝ) (hc : c ≠ 0) (x : Rd d) : dil c hc x = c • x := rfl

/-- Auxiliary to the Lean proof route. The section's transform of a Schwartz
map, as a Schwartz map. -/
def hatS (f : SchwartzMap (Rd d) E) : SchwartzMap (Rd d) E :=
  (cd d : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (dil (2 * π)⁻¹ (by positivity)) (𝓕 f)

/-- Auxiliary to the Lean proof route. -/
theorem hatS_apply (f : SchwartzMap (Rd d) E) (ξ : Rd d) : hatS f ξ = paperHat f ξ := by
  rw [paperHat_eq_fourier, hatS, smul_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, dil_apply,
    SchwartzMap.fourier_coe]

/-- Auxiliary to the Lean proof route. The transform of a Schwartz map is
continuous. -/
theorem continuous_paperHat (f : SchwartzMap (Rd d) E) : Continuous (paperHat (f : Rd d → E)) := by
  have : paperHat (f : Rd d → E) = hatS f := funext fun ξ => (hatS_apply f ξ).symm
  rw [this]; exact (hatS f).continuous

/-- Auxiliary to the Lean proof route. The transform of a Schwartz map is
integrable. -/
theorem integrable_paperHat (f : SchwartzMap (Rd d) E) : Integrable (paperHat (f : Rd d → E)) := by
  have : paperHat (f : Rd d → E) = hatS f := funext fun ξ => (hatS_apply f ξ).symm
  rw [this]; exact (hatS f).integrable

/-- Fourier inversion in the section's convention, for a Schwartz map with
values in a complex Banach space: `f(x) = c_d ∫ e^{i η·x} f̂(η) dη` (used in
the proof of `P:masked-auxiliary-norm`, line 121, "Fourier inversion").
Derived from Mathlib's `Continuous.fourierInv_fourier_eq` by the change of
variables `w = η/(2π)`. -/
theorem paper_inversion [CompleteSpace E] (f : SchwartzMap (Rd d) E) (x : Rd d) :
    f x = (cd d : ℂ) • ∫ η, Complex.exp (Complex.I * (inner ℝ η x : ℝ)) • paperHat f η := by
  have hinv : 𝓕⁻ (𝓕 (f : Rd d → E)) x = f x := by
    have h := f.continuous.fourierInv_fourier_eq f.integrable
      (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 f).integrable)
    rw [h]
  rw [← hinv, Real.fourierInv_eq']
  set g : Rd d → E := fun w => Complex.exp (↑(2 * π * inner ℝ w x) * Complex.I) • 𝓕 (f : Rd d → E) w
    with hg
  have hpt : ∀ η : Rd d, Complex.exp (Complex.I * (inner ℝ η x : ℝ)) • paperHat f η =
      (cd d : ℂ) • g ((2 * π)⁻¹ • η) := by
    intro η
    rw [paperHat_eq_fourier, hg, smul_comm]
    congr 2
    rw [real_inner_smul_left]
    have hπ : (2 * π) ≠ 0 := by positivity
    push_cast
    field_simp
  simp_rw [hpt]
  rw [integral_smul, Measure.integral_comp_inv_smul_of_nonneg volume g (by positivity),
    finrank_euclideanSpace_fin, smul_smul, ← Complex.coe_smul, smul_smul]
  have hc := cd_sq_mul d
  have : (cd d : ℂ) * (cd d : ℂ) * (((2 * π) ^ d : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← sq, hc, Complex.ofReal_one]
  rw [this, one_smul]

end Fourier

/-- Auxiliary to the Lean proof route. Schwartz maps integrate polynomial
weights: `(1+‖u‖)^N ‖f(u)‖` is integrable. -/
theorem integrable_one_add_pow_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap (Rd d) E) (N : ℕ) :
    Integrable (fun u : Rd d => (1 + ‖u‖) ^ N * ‖f u‖) := by
  have h0 := f.integrable_pow_mul volume 0
  have hN := f.integrable_pow_mul volume N
  refine ((h0.add hN).const_mul (2 ^ (N - 1))).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun u => ?_)
  have hb := add_pow_le (zero_le_one' ℝ) (norm_nonneg u) N
  rw [one_pow] at hb
  rw [Real.norm_of_nonneg (by positivity)]
  simp only [pow_zero, one_mul]
  calc (1 + ‖u‖) ^ N * ‖f u‖ ≤ 2 ^ (N - 1) * (1 + ‖u‖ ^ N) * ‖f u‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = 2 ^ (N - 1) * (‖f u‖ + ‖u‖ ^ N * ‖f u‖) := by ring

/-! ### The mask `ζ_R`, the kernel `k_R` and the constant `L` (lines 79-82) -/

/-- Auxiliary to the Lean proof route. The real Schwartz function `ζ` as a
complex Schwartz map. -/
def zc (ζ : SchwartzMap (Rd d) ℝ) : SchwartzMap (Rd d) ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM ζ

/-- Auxiliary to the Lean proof route. -/
@[simp] theorem zc_apply (ζ : SchwartzMap (Rd d) ℝ) (x : Rd d) : zc ζ x = (ζ x : ℂ) := rfl

/-- The mask `ζ_R(x) = ζ(x/R)` (line 79). -/
def zetaR (ζ : SchwartzMap (Rd d) ℝ) (R : ℝ) (x : Rd d) : ℝ := ζ (R⁻¹ • x)

/-- The kernel `k_R = ζ_R^` (line 80), the section's transform of the mask. -/
def kR (ζ : SchwartzMap (Rd d) ℝ) (R : ℝ) : Rd d → ℂ :=
  paperHat (fun x => (zetaR ζ R x : ℂ))

/-- `L = ‖ζ̂‖₁` (line 80). -/
def Lz (ζ : SchwartzMap (Rd d) ℝ) : ℝ := ∫ η, ‖paperHat (fun x => (ζ x : ℂ)) η‖

/-- Auxiliary to the Lean proof route. The mask as a complex Schwartz map
(`R ≠ 0`). -/
def zetaS (ζ : SchwartzMap (Rd d) ℝ) (R : ℝ) (hR : R ≠ 0) : SchwartzMap (Rd d) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (dil R⁻¹ (inv_ne_zero hR)) (zc ζ)

/-- Auxiliary to the Lean proof route. -/
theorem zetaS_apply (ζ : SchwartzMap (Rd d) ℝ) (R : ℝ) (hR : R ≠ 0) (x : Rd d) :
    zetaS ζ R hR x = (zetaR ζ R x : ℂ) := rfl

/-- Auxiliary to the Lean proof route. `k_R` is the transform of a Schwartz
map, hence itself a Schwartz map. -/
theorem kR_eq_hatS (ζ : SchwartzMap (Rd d) ℝ) (R : ℝ) (hR : R ≠ 0) :
    kR ζ R = hatS (zetaS ζ R hR) := by
  funext u
  rw [hatS_apply]
  rfl

/-- Auxiliary to the Lean proof route. -/
theorem continuous_kR (ζ : SchwartzMap (Rd d) ℝ) {R : ℝ} (hR : R ≠ 0) : Continuous (kR ζ R) := by
  rw [kR_eq_hatS ζ R hR]; exact (hatS _).continuous

/-- Auxiliary to the Lean proof route. -/
theorem integrable_kR (ζ : SchwartzMap (Rd d) ℝ) {R : ℝ} (hR : R ≠ 0) : Integrable (kR ζ R) := by
  rw [kR_eq_hatS ζ R hR]; exact (hatS _).integrable

/-- The scaling of the kernel (line 81): `k_R(u) = R^d ζ̂(Ru)` for `R > 0`. -/
theorem kR_scale (ζ : SchwartzMap (Rd d) ℝ) {R : ℝ} (hR : 0 < R) (u : Rd d) :
    kR ζ R u = ((R ^ d : ℝ) : ℂ) * paperHat (fun x => (ζ x : ℂ)) (R • u) := by
  rw [kR, paperHat, paperHat]
  set f : Rd d → ℂ := fun y => Complex.exp (-(Complex.I * (inner ℝ u (R • y) : ℝ))) • (ζ y : ℂ)
    with hf
  have hpt : ∀ x : Rd d, Complex.exp (-(Complex.I * (inner ℝ u x : ℝ))) • (zetaR ζ R x : ℂ) =
      f (R⁻¹ • x) := by
    intro x
    rw [hf]
    simp only [zetaR]
    rw [smul_inv_smul₀ hR.ne']
  simp_rw [hpt]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume f hR.le, finrank_euclideanSpace_fin, hf]
  simp_rw [real_inner_smul_right, real_inner_smul_left]
  rw [Complex.real_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- `‖k_R‖₁ = L` for `R > 0` (line 81), with `k_R` integrable. -/
theorem integral_norm_kR (ζ : SchwartzMap (Rd d) ℝ) {R : ℝ} (hR : 0 < R) :
    ∫ u, ‖kR ζ R u‖ = Lz ζ := by
  simp_rw [kR_scale ζ hR, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ R ^ d)]
  rw [integral_const_mul,
    Measure.integral_comp_smul_of_nonneg volume (fun v => ‖paperHat (fun x => (ζ x : ℂ)) v‖) R
      (hR := hR.le), finrank_euclideanSpace_fin, smul_eq_mul, Lz, ← mul_assoc,
    mul_inv_cancel₀ (by positivity), one_mul]

/-- Auxiliary to the Lean proof route. Fourier injectivity in the section's
convention: a Schwartz `ζ` whose transform vanishes identically is zero. -/
theorem eq_zero_of_paperHat_eq_zero (ζ : SchwartzMap (Rd d) ℝ)
    (h : ∀ η, paperHat (fun x => (ζ x : ℂ)) η = 0) : ζ = 0 := by
  ext x
  have hx := paper_inversion (zc ζ) x
  have h' : ∀ η, paperHat (zc ζ : Rd d → ℂ) η = 0 := h
  simp only [h', smul_zero, integral_zero] at hx
  simpa using hx

/-- `L > 0` for a nonzero real Schwartz `ζ` (line 82), with `ζ̂` integrable. -/
theorem Lz_pos (ζ : SchwartzMap (Rd d) ℝ) (hζ : ζ ≠ 0) :
    Integrable (paperHat (fun x => (ζ x : ℂ))) ∧ 0 < Lz ζ := by
  have hint : Integrable (paperHat (fun x => (ζ x : ℂ))) := integrable_paperHat (zc ζ)
  have hcont : Continuous (paperHat (fun x => (ζ x : ℂ))) := continuous_paperHat (zc ζ)
  refine ⟨hint, ?_⟩
  obtain ⟨η, hη⟩ : ∃ η, paperHat (fun x => (ζ x : ℂ)) η ≠ 0 := by
    by_contra hcon
    exact hζ (eq_zero_of_paperHat_eq_zero ζ fun η => by_contra fun h => hcon ⟨η, h⟩)
  rw [Lz, integral_pos_iff_support_of_nonneg (fun _ => norm_nonneg _) hint.norm]
  have hopen : IsOpen (Function.support fun v => ‖paperHat (fun x => (ζ x : ℂ)) v‖) :=
    isOpen_ne_fun hcont.norm continuous_const
  exact hopen.measure_pos volume ⟨η, by simpa using hη⟩

/-- Since `ζ` is real, `k_R(-u) = conj(k_R(u))` (lines 106-107), hence
`|k_R(-u)| = |k_R(u)|`. -/
theorem kR_neg (ζ : SchwartzMap (Rd d) ℝ) (R : ℝ) (u : Rd d) :
    kR ζ R (-u) = (starRingEnd ℂ) (kR ζ R u) := by
  rw [kR, paperHat, paperHat, smul_eq_mul, smul_eq_mul, map_mul, Complex.conj_ofReal,
    ← integral_conj]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg,
    Complex.conj_I, inner_neg_left]
  push_cast
  ring_nf

/-- Auxiliary to the Lean proof route. -/
theorem norm_kR_neg (ζ : SchwartzMap (Rd d) ℝ) (R : ℝ) (u : Rd d) :
    ‖kR ζ R (-u)‖ = ‖kR ζ R u‖ := by
  rw [kR_neg, Complex.norm_conj]

/-! ### The auxiliary measure `ν_R` (`E:masked-auxiliary-measure`, lines 83-86) -/

/-- The density `ρ_R(η) = c_d² L ∫ |k_R(ξ-η)| μ(dξ)` of
`E:masked-auxiliary-measure` (line 85), as an `ℝ≥0∞`-valued function (the
integrand is nonnegative, so the lower Lebesgue integral is the manuscript's
integral and no junk value enters). -/
def rho (μ : Measure (Rd d)) (ζ : SchwartzMap (Rd d) ℝ) (R : ℝ) (η : Rd d) : ℝ≥0∞ :=
  ENNReal.ofReal (cd d ^ 2 * Lz ζ) * ∫⁻ ξ, ‖kR ζ R (ξ - η)‖ₑ ∂μ

/-- The auxiliary measure `ν_R(dη) = ρ_R(η) dη` (line 84). -/
def nu (μ : Measure (Rd d)) (ζ : SchwartzMap (Rd d) ℝ) (R : ℝ) : Measure (Rd d) :=
  volume.withDensity (rho μ ζ R)

section Measure

variable {μ : Measure (Rd d)} {ζ : SchwartzMap (Rd d) ℝ} {R : ℝ}

/-- Auxiliary to the Lean proof route. -/
theorem measurable_kR_sub (hR : R ≠ 0) :
    Measurable (fun p : Rd d × Rd d => ‖kR ζ R (p.1 - p.2)‖ₑ) :=
  ((continuous_kR ζ hR).comp (continuous_fst.sub continuous_snd)).enorm.measurable

/-- Auxiliary to the Lean proof route. `ρ_R` is measurable (`μ` s-finite,
`R ≠ 0`). -/
theorem measurable_rho [SFinite μ] (hR : R ≠ 0) : Measurable (rho μ ζ R) :=
  measurable_const.mul (measurable_kR_sub hR).lintegral_prod_left'

/-- Auxiliary to the Lean proof route (Tonelli). For `μ` s-finite, `R ≠ 0` and
measurable `w ≥ 0`:
`∫ w dν_R = c_d² L ∫ (∫ w(η) |k_R(ξ-η)| dη) μ(dξ)`. -/
theorem lintegral_nu [SFinite μ] (hR : R ≠ 0) {w : Rd d → ℝ≥0∞} (hw : Measurable w) :
    ∫⁻ η, w η ∂nu μ ζ R = ENNReal.ofReal (cd d ^ 2 * Lz ζ) *
      ∫⁻ ξ, ∫⁻ η, w η * ‖kR ζ R (ξ - η)‖ₑ ∂volume ∂μ := by
  rw [nu, lintegral_withDensity_eq_lintegral_mul₀ (measurable_rho hR).aemeasurable
    hw.aemeasurable]
  simp only [Pi.mul_apply, rho, mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  have hm : ∀ η : Rd d, Measurable fun ξ : Rd d => ‖kR ζ R (ξ - η)‖ₑ := fun η =>
    ((continuous_kR ζ hR).comp (continuous_id.sub continuous_const)).enorm.measurable
  simp_rw [← lintegral_mul_const _ (hm _)]
  rw [lintegral_lintegral_swap]
  · congr 1; funext ξ; congr 1; funext η; ring
  · exact ((measurable_kR_sub hR).comp measurable_swap).mul (hw.comp measurable_fst)
      |>.aemeasurable

/-- Auxiliary to the Lean proof route (Tonelli and the substitution
`u = ξ - η`, as in lines 108-111): for measurable `A`,
`ν_R(A) = c_d² L ∫ |k_R(u)| μ(A + u) du`, written with the preimage of `A`
under `ξ ↦ ξ - u`. -/
theorem nu_apply [SFinite μ] (hR : R ≠ 0) {A : Set (Rd d)} (hA : MeasurableSet A) :
    nu μ ζ R A = ENNReal.ofReal (cd d ^ 2 * Lz ζ) *
      ∫⁻ u, ‖kR ζ R u‖ₑ * μ ((fun ξ => ξ - u) ⁻¹' A) := by
  have h := lintegral_nu (μ := μ) (ζ := ζ) hR (measurable_one.indicator hA)
  rw [lintegral_indicator_one hA] at h
  rw [h]
  congr 1
  have hsub : ∀ ξ : Rd d, ∫⁻ η, A.indicator 1 η * ‖kR ζ R (ξ - η)‖ₑ =
      ∫⁻ u, A.indicator 1 (ξ - u) * ‖kR ζ R u‖ₑ := by
    intro ξ
    have := lintegral_sub_left_eq_self (μ := (volume : Measure (Rd d)))
      (fun u => A.indicator 1 (ξ - u) * ‖kR ζ R u‖ₑ) ξ
    simpa only [sub_sub_cancel] using this
  simp_rw [hsub]
  rw [lintegral_lintegral_swap]
  · congr 1
    funext u
    rw [lintegral_mul_const (‖kR ζ R u‖ₑ) (f := fun ξ => A.indicator (1 : Rd d → ℝ≥0∞) (ξ - u))
      ((measurable_one.indicator hA).comp (measurable_sub_const u)), mul_comm]
    congr 1
    have : (fun ξ : Rd d => A.indicator (1 : Rd d → ℝ≥0∞) (ξ - u)) =
        ((fun ξ => ξ - u) ⁻¹' A).indicator 1 := by
      rfl
    rw [this, lintegral_indicator_one (measurable_sub_const u hA)]
  · refine (((measurable_one.indicator hA).comp (measurable_fst.sub measurable_snd)).mul
      ((continuous_kR ζ hR).enorm.measurable.comp measurable_snd)).aemeasurable

/-- Auxiliary to the Lean proof route. -/
theorem preimage_sub_closedBall (u y : Rd d) (r : ℝ) :
    (fun ξ => ξ - u) ⁻¹' closedBall y r = closedBall (y + u) r := by
  ext ξ; simp [mem_closedBall, dist_eq_norm, sub_sub, add_comm]

/-- Auxiliary to the Lean proof route. -/
theorem preimage_sub_ball (u y : Rd d) (r : ℝ) :
    (fun ξ => ξ - u) ⁻¹' ball y r = ball (y + u) r := by
  ext ξ; simp [mem_ball, dist_eq_norm, sub_sub, add_comm]

/-- Auxiliary to the Lean proof route. `∫ |k_R| = L` as a lower integral
(`R > 0`). -/
theorem lintegral_enorm_kR (hR : 0 < R) : ∫⁻ u, ‖kR ζ R u‖ₑ = ENNReal.ofReal (Lz ζ) := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (integrable_kR ζ hR.ne'), integral_norm_kR ζ hR]

/-- Auxiliary to the Lean proof route. `L ≥ 0`. -/
theorem Lz_nonneg : 0 ≤ Lz ζ := integral_nonneg fun _ => norm_nonneg _

/-- Auxiliary to the Lean proof route. A uniform bound `μ(A + u) ≤ M` gives
`ν_R(A) ≤ c_d² L · L · M`. -/
theorem nu_le_of_translate_le [SFinite μ] (hR : 0 < R) {A : Set (Rd d)} (hA : MeasurableSet A)
    {M : ℝ} (hb : ∀ u, μ ((fun ξ => ξ - u) ⁻¹' A) ≤ ENNReal.ofReal M) :
    nu μ ζ R A ≤ ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * M) := by
  rw [nu_apply hR.ne' hA]
  calc ENNReal.ofReal (cd d ^ 2 * Lz ζ) * ∫⁻ u, ‖kR ζ R u‖ₑ * μ ((fun ξ => ξ - u) ⁻¹' A)
      ≤ ENNReal.ofReal (cd d ^ 2 * Lz ζ) * ∫⁻ u, ‖kR ζ R u‖ₑ * ENNReal.ofReal M := by
        gcongr with u; exact hb u
    _ = ENNReal.ofReal (cd d ^ 2 * Lz ζ) * (ENNReal.ofReal (Lz ζ) * ENNReal.ofReal M) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_enorm_kR hR]
    _ = ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * M) := by
        have hL := Lz_nonneg (ζ := ζ)
        rw [← ENNReal.ofReal_mul hL, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-- Auxiliary to the Lean proof route. `P:masked-spectral-growth` at every
center: `μ(B̄(y,r)) ≤ C_Γ r^α`, from `MaskedSpectralGrowth.closedBall_le`. -/
theorem mu_closedBall_le {Γ : Measure (Rd d)} {alpha : ℝ} (hμt : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha)) (y : Rd d)
    {r : ℝ} (hr : 0 < r) : μ (closedBall y r) ≤ ENNReal.ofReal (CGamma Γ * r ^ alpha) := by
  refine closedBall_le hsp hΓs y r hr ?_
  refine (integrable_gauss_of_tempered hμt (b := 1 / r ^ 2) (by positivity) y).congr
    (Filter.Eventually.of_forall fun ξ => ?_)
  simp only; congr 1; field_simp

end Measure

/-! ### `ν_R` is even, tempered and Radon, with uniform ball bounds -/

section Properties

variable {μ Γ : Measure (Rd d)} {ζ : SchwartzMap (Rd d) ℝ} {R alpha : ℝ}

/-- `E:masked-auxiliary-growth` (lines 90-93), closed ball: for `R > 0`, `r > 0`,
`ν_R(B̄(y,r)) ≤ c_d² L² C_Γ r^α`. General form: `μ` s-finite and tempered,
the spectral convention and the scaling `Γ(cA) = c^{d-α}Γ(A)`. -/
theorem nu_closedBall_le [SFinite μ] (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ)
    (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha)) (hR : 0 < R) (y : Rd d) {r : ℝ}
    (hr : 0 < r) :
    nu μ ζ R (closedBall y r) ≤ ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha) := by
  rw [mul_assoc (cd d ^ 2 * Lz ζ ^ 2)]
  exact nu_le_of_translate_le hR measurableSet_closedBall fun u => by
    rw [preimage_sub_closedBall]; exact mu_closedBall_le hμt hsp hΓs _ hr

/-- `E:masked-auxiliary-growth` (lines 90-93), open ball. Same hypotheses as
`nu_closedBall_le`. -/
theorem nu_ball_le [SFinite μ] (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ)
    (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha)) (hR : 0 < R) (y : Rd d) {r : ℝ}
    (hr : 0 < r) :
    nu μ ζ R (ball y r) ≤ ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha) :=
  (measure_mono ball_subset_closedBall).trans (nu_closedBall_le hμt hsp hΓs hR y hr)

/-- `ν_R` is Radon (line 89): locally finite (on `ℝ^d` a locally finite Borel
measure is Radon, as in `HomogHypothesis.HomogCovariance`). Lean route: from
the ball bound, instead of the continuity of `ρ_R` (lines 103-106). Same
hypotheses as `nu_closedBall_le`. -/
theorem isLocallyFiniteMeasure_nu [SFinite μ] (hμt : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha))
    (hR : 0 < R) : IsLocallyFiniteMeasure (nu μ ζ R) :=
  ⟨fun x => ⟨closedBall x 1, closedBall_mem_nhds x one_pos,
    (nu_closedBall_le hμt hsp hΓs hR x one_pos).trans_lt ENNReal.ofReal_lt_top⟩⟩

/-- Auxiliary to the Lean proof route (Peetre's inequality):
`(1+|η|)^{-N} ≤ (1+|ξ|)^{-N} (1+|ξ-η|)^N`. -/
theorem peetre (ξ η : Rd d) (N : ℕ) :
    (1 + ‖η‖) ^ (-(N : ℝ)) ≤ (1 + ‖ξ‖) ^ (-(N : ℝ)) * (1 + ‖ξ - η‖) ^ N := by
  have h1 : 0 < 1 + ‖η‖ := by positivity
  have h2 : 0 < 1 + ‖ξ‖ := by positivity
  rw [Real.rpow_neg h1.le, Real.rpow_neg h2.le, Real.rpow_natCast, Real.rpow_natCast,
    inv_mul_eq_div, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul,
    ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ N
  have : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
    calc ‖ξ‖ = ‖(ξ - η) + η‖ := by rw [sub_add_cancel]
      _ ≤ ‖ξ - η‖ + ‖η‖ := norm_add_le _ _
  nlinarith [norm_nonneg (ξ - η), norm_nonneg η]

/-- Auxiliary to the Lean proof route. Weighted transfer of temperedness from
`μ` to `ν_R` by Peetre's inequality (`μ` s-finite, `R ≠ 0`):
`∫ (1+|η|)^{-N} dν_R ≤ c_d² L (∫ (1+|ξ|)^{-N} dμ) (∫ (1+|u|)^N |k_R(u)| du)`. -/
theorem lintegral_weight_nu_le [SFinite μ] (hR : R ≠ 0) (N : ℕ) :
    ∫⁻ η, ENNReal.ofReal ((1 + ‖η‖) ^ (-(N : ℝ))) ∂nu μ ζ R ≤
      ENNReal.ofReal (cd d ^ 2 * Lz ζ) *
        ((∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ (-(N : ℝ))) ∂μ) *
          ∫⁻ u, ENNReal.ofReal ((1 + ‖u‖) ^ N * ‖kR ζ R u‖)) := by
  rw [lintegral_nu hR (by fun_prop)]
  gcongr ENNReal.ofReal (cd d ^ 2 * Lz ζ) * ?_
  rw [← lintegral_mul_const _ (by fun_prop)]
  refine lintegral_mono fun ξ => ?_
  calc ∫⁻ η, ENNReal.ofReal ((1 + ‖η‖) ^ (-(N : ℝ))) * ‖kR ζ R (ξ - η)‖ₑ
      ≤ ∫⁻ η, ENNReal.ofReal ((1 + ‖ξ‖) ^ (-(N : ℝ))) *
          ENNReal.ofReal ((1 + ‖ξ - η‖) ^ N * ‖kR ζ R (ξ - η)‖) := by
        refine lintegral_mono fun η => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        calc (1 + ‖η‖) ^ (-(N : ℝ)) * ‖kR ζ R (ξ - η)‖
            ≤ ((1 + ‖ξ‖) ^ (-(N : ℝ)) * (1 + ‖ξ - η‖) ^ N) * ‖kR ζ R (ξ - η)‖ :=
              mul_le_mul_of_nonneg_right (peetre ξ η N) (norm_nonneg _)
          _ = _ := by ring
    _ = ENNReal.ofReal ((1 + ‖ξ‖) ^ (-(N : ℝ))) *
          ∫⁻ u, ENNReal.ofReal ((1 + ‖u‖) ^ N * ‖kR ζ R u‖) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_sub_left_eq_self
          (fun u => ENNReal.ofReal ((1 + ‖u‖) ^ N * ‖kR ζ R u‖)) ξ

/-- Auxiliary to the Lean proof route. `∫ (1+|u|)^N |k_R(u)| du < ∞`
(Schwartz decay of `k_R`, `R ≠ 0`). -/
theorem lintegral_weight_kR_lt_top (hR : R ≠ 0) (N : ℕ) :
    ∫⁻ u, ENNReal.ofReal ((1 + ‖u‖) ^ N * ‖kR ζ R u‖) < ⊤ := by
  rw [kR_eq_hatS ζ R hR]
  exact (integrable_one_add_pow_mul (hatS (zetaS ζ R hR)) N).lintegral_lt_top

/-- `ν_R` is tempered (line 89), with the exponent of `μ`. Lean route:
Peetre's inequality and the Schwartz decay of `k_R`, instead of the polynomial
growth on centred balls and the dyadic argument of lines 113-114. Hypotheses:
`μ` s-finite and tempered, `R ≠ 0`. -/
theorem isTempered_nu [SFinite μ] (hμt : IsTempered μ) (hR : R ≠ 0) :
    IsTempered (nu μ ζ R) := by
  obtain ⟨N, hN⟩ := hμt
  exact ⟨N, (lintegral_weight_nu_le hR N).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top hN (lintegral_weight_kR_lt_top hR N)))⟩

/-- Auxiliary to the Lean proof route. `ρ_R` is even when `μ` is even and `ζ`
is real (lines 106-107). -/
theorem rho_neg (hR : R ≠ 0) (hμe : IsEven μ) (η : Rd d) : rho μ ζ R (-η) = rho μ ζ R η := by
  unfold rho
  congr 1
  conv_lhs => rw [← hμe]
  rw [lintegral_map (f := fun ξ => ‖kR ζ R (ξ - -η)‖ₑ) (g := fun x : Rd d => -x)
    ((continuous_kR ζ hR).comp (continuous_id.sub continuous_const)).enorm.measurable
    measurable_neg]
  congr 1
  funext ξ
  rw [show -ξ - -η = -(ξ - η) by abel, ← ofReal_norm, ← ofReal_norm,
    norm_kR_neg]

/-- `ν_R` is even (line 89): `μ` even, `ζ` real, `R ≠ 0`. -/
theorem isEven_nu (hR : R ≠ 0) (hμe : IsEven μ) : IsEven (nu μ ζ R) := by
  unfold IsEven
  ext A hA
  rw [Measure.map_apply measurable_neg hA, nu, withDensity_apply _ (measurable_neg hA),
    withDensity_apply _ hA, ← lintegral_indicator (measurable_neg hA), ← lintegral_indicator hA]
  conv_rhs => rw [← lintegral_neg_eq_self]
  refine lintegral_congr fun η => ?_
  by_cases h : -η ∈ A
  · rw [Set.indicator_of_mem (show η ∈ (fun x : Rd d => -x) ⁻¹' A from h),
      Set.indicator_of_mem h, rho_neg hR hμe]
  · rw [Set.indicator_of_notMem (show η ∉ (fun x : Rd d => -x) ⁻¹' A from h),
      Set.indicator_of_notMem h]

end Properties

/-! ### The Hilbert-valued Fourier bound `E:masked-hilbert-fourier` -/

/-- Auxiliary to the Lean proof route (weighted Cauchy-Schwarz, lines 127-128, in
the form of a nonnegative quadratic): for `a ≥ 0` with `a`, `a g`, `a g²`
integrable, `(∫ a g)² ≤ (∫ a)(∫ a g²)`. -/
theorem sq_integral_mul_le {a g : Rd d → ℝ} (ha : ∀ x, 0 ≤ a x) (hai : Integrable a)
    (hag : Integrable fun x => a x * g x) (hag2 : Integrable fun x => a x * g x ^ 2) :
    (∫ x, a x * g x) ^ 2 ≤ (∫ x, a x) * ∫ x, a x * g x ^ 2 := by
  have hq : ∀ t : ℝ, 0 ≤ (∫ x, a x) * (t * t) + (-2 * ∫ x, a x * g x) * t +
      ∫ x, a x * g x ^ 2 := by
    intro t
    have e : (fun x => a x * (g x - t) ^ 2) =
        fun x => (t * t) * a x + (-2 * t) * (a x * g x) + a x * g x ^ 2 := by
      funext x; ring
    have hexp : ∫ x, a x * (g x - t) ^ 2 = (∫ x, a x) * (t * t) +
        (-2 * ∫ x, a x * g x) * t + ∫ x, a x * g x ^ 2 := by
      have i1 : Integrable (fun x => t * t * a x) := hai.const_mul _
      have i2 : Integrable (fun x => -2 * t * (a x * g x)) := hag.const_mul _
      have i12 : Integrable (fun x => t * t * a x + -2 * t * (a x * g x)) := i1.add i2
      rw [e, integral_add i12 hag2, integral_add i1 i2, integral_const_mul, integral_const_mul]
      ring
    rw [← hexp]
    exact integral_nonneg fun x => mul_nonneg (ha x) (sq_nonneg _)
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith

/-- Auxiliary to the Lean proof route. Schwartz maps satisfy
`(1+|x|)^N |f(x)| ≤ C` with `C ≥ 0`. -/
theorem exists_weight_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap (Rd d) E) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (1 + ‖x‖) ^ N * ‖f x‖ ≤ C := by
  have h : ∀ x, (1 + ‖x‖) ^ N * ‖f x‖ ≤ 2 ^ N *
      ((Finset.Iic (N, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := by
    intro x
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) le_rfl le_rfl f x
    rwa [norm_iteratedFDeriv_zero] at this
  exact ⟨_, (by positivity : (0 : ℝ) ≤ (1 + ‖(0 : Rd d)‖) ^ N * ‖f 0‖).trans (h 0), h⟩

/-- Auxiliary to the Lean proof route. `‖v‖ₑ² = (‖v‖²)⁺` as extended reals. -/
theorem ofReal_norm_sq {E : Type*} [NormedAddCommGroup E] (v : E) :
    ENNReal.ofReal (‖v‖ ^ 2) = ‖v‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {μ : Measure (Rd d)} {ζ : SchwartzMap (Rd d) ℝ} {R : ℝ}

/-- Auxiliary to the Lean proof route. -/
@[fun_prop] theorem continuous_zetaR : Continuous (zetaR ζ R) := ζ.continuous.comp (continuous_const_smul _)

/-- Auxiliary to the Lean proof route. -/
theorem norm_exp_I_mul (r : ℝ) : ‖Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- Auxiliary to the Lean proof route. -/
theorem norm_exp_neg_I_mul (r : ℝ) : ‖Complex.exp (-(Complex.I * (r : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- The convolution identity of the proof (lines 116-120): for a Schwartz map
`F` with values in a complex Banach space and `R ≠ 0`,
`(ζ_R F)^(ξ) = c_d ∫ k_R(ξ-η) F̂(η) dη`.  Lean route: Fourier inversion of
`F` (`paper_inversion`) and one Bochner Fubini swap (`integral_integral_swap`,
the integrand being dominated by `c_d |ζ_R(x)| |F̂(η)|`), directly in the
Banach space; the TeX's passage through scalar, finite-rank and projected
functions (lines 121-127) is not needed. -/
theorem paperHat_mask (hR : R ≠ 0) (F : SchwartzMap (Rd d) E) (ξ : Rd d) :
    paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ =
      (cd d : ℂ) • ∫ η, kR ζ R (ξ - η) • paperHat (F : Rd d → E) η := by
  set Fh := paperHat (F : Rd d → E) with hFh
  have hFc : Continuous Fh := continuous_paperHat F
  have hFi : Integrable Fh := integrable_paperHat F
  have hz : Continuous fun x => (zetaR ζ R x : ℂ) := Complex.continuous_ofReal.comp continuous_zetaR
  set c : Rd d → Rd d → ℂ := fun x η => (cd d : ℂ) *
    Complex.exp (-(Complex.I * (inner ℝ ξ x : ℝ))) * (zetaR ζ R x : ℂ) *
      Complex.exp (Complex.I * (inner ℝ η x : ℝ)) with hc
  have h1 : ∀ x, Complex.exp (-(Complex.I * (inner ℝ ξ x : ℝ))) • ((zetaR ζ R x : ℂ) • F x) =
      ∫ η, c x η • Fh η := by
    intro x
    conv_lhs => rw [paper_inversion F x]
    rw [smul_smul, smul_smul, ← integral_smul]
    congr 1; funext η
    rw [smul_smul, hc]
    congr 1; ring
  have hint : Integrable (Function.uncurry fun x η => c x η • Fh η)
      ((volume : Measure (Rd d)).prod volume) := by
    have hprod := ((zetaS ζ R hR).integrable (μ := volume)).smul_prod hFi
    refine (hprod.norm.const_mul (cd d)).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      fun_prop
    · simp only [Function.uncurry, hc, norm_smul, norm_mul, Complex.norm_real,
        norm_exp_I_mul, norm_exp_neg_I_mul, mul_one, zetaS_apply,
        Real.norm_of_nonneg (cd_pos d).le]
      exact le_of_eq (by ring)
  rw [paperHat]
  simp_rw [h1]
  congr 1
  rw [integral_integral_swap hint]
  congr 1
  funext η
  rw [integral_smul_const]
  congr 1
  rw [kR, paperHat, smul_eq_mul, ← integral_const_mul]
  congr 1
  funext x
  have he : Complex.exp (-(Complex.I * (inner ℝ (ξ - η) x : ℝ))) =
      Complex.exp (-(Complex.I * (inner ℝ ξ x : ℝ))) * Complex.exp (Complex.I * (inner ℝ η x : ℝ)) := by
    rw [← Complex.exp_add, inner_sub_left]; congr 1; push_cast; ring
  rw [hc, he, smul_eq_mul]
  ring

omit [CompleteSpace E] in
/-- Auxiliary to the Lean proof route. The integrand of the pointwise bound is
integrable (`R ≠ 0`). -/
theorem integrable_weighted (hR : R ≠ 0) (F : SchwartzMap (Rd d) E) (ξ : Rd d) :
    Integrable (fun η => ‖kR ζ R (ξ - η)‖) ∧
      Integrable (fun η => ‖kR ζ R (ξ - η)‖ * ‖paperHat (F : Rd d → E) η‖) ∧
      Integrable (fun η => ‖kR ζ R (ξ - η)‖ * ‖paperHat (F : Rd d → E) η‖ ^ 2) := by
  have hai : Integrable (fun η => ‖kR ζ R (ξ - η)‖) :=
    ((integrable_kR ζ hR).comp_sub_left ξ).norm
  have hFc : Continuous (paperHat (F : Rd d → E)) := continuous_paperHat F
  obtain ⟨C, -, hC⟩ := exists_weight_bound (hatS F) 0
  have hb : ∀ η, ‖paperHat (F : Rd d → E) η‖ ≤ C := fun η => by
    simpa [hatS_apply] using hC η
  refine ⟨hai, hai.mul_bdd (c := C) hFc.norm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun η => ?_),
    hai.mul_bdd (c := C ^ 2) (hFc.norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => ?_)⟩
  · rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hb η
  · rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb η) 2

/-- The pointwise bound of the proof (lines 127-132), from the convolution
identity, the triangle inequality and weighted Cauchy-Schwarz (`R > 0`):
`|(ζ_R F)^(ξ)|² ≤ c_d² L ∫ |k_R(ξ-η)| |F̂(η)|² dη`. -/
theorem norm_sq_paperHat_mask_le (hR : 0 < R) (F : SchwartzMap (Rd d) E) (ξ : Rd d) :
    ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ ^ 2 ≤
      cd d ^ 2 * Lz ζ * ∫ η, ‖kR ζ R (ξ - η)‖ * ‖paperHat (F : Rd d → E) η‖ ^ 2 := by
  obtain ⟨hai, hag, hag2⟩ := integrable_weighted hR.ne' F ξ
  have hM : ∫ η, ‖kR ζ R (ξ - η)‖ = Lz ζ := by
    rw [integral_sub_left_eq_self (fun u => ‖kR ζ R u‖) volume ξ, integral_norm_kR ζ hR]
  have hP : ‖∫ η, kR ζ R (ξ - η) • paperHat (F : Rd d → E) η‖ ≤
      ∫ η, ‖kR ζ R (ξ - η)‖ * ‖paperHat (F : Rd d → E) η‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext η; rw [norm_smul]
  rw [paperHat_mask hR.ne', norm_smul, Complex.norm_real, Real.norm_of_nonneg (cd_pos d).le,
    mul_pow]
  calc cd d ^ 2 * ‖∫ η, kR ζ R (ξ - η) • paperHat (F : Rd d → E) η‖ ^ 2
      ≤ cd d ^ 2 * (∫ η, ‖kR ζ R (ξ - η)‖ * ‖paperHat (F : Rd d → E) η‖) ^ 2 := by
        gcongr
    _ ≤ cd d ^ 2 * ((∫ η, ‖kR ζ R (ξ - η)‖) *
          ∫ η, ‖kR ζ R (ξ - η)‖ * ‖paperHat (F : Rd d → E) η‖ ^ 2) := by
        gcongr
        exact sq_integral_mul_le (fun _ => norm_nonneg _) hai hag hag2
    _ = _ := by rw [hM]; ring

/-- `E:masked-hilbert-fourier` (lines 93-98) as an inequality of lower
integrals (no junk value): for `μ` s-finite, `R > 0`, and a Schwartz map `F`
with values in a complex Banach space,
`∫ |(ζ_R F)^(ξ)|² μ(dξ) ≤ ∫ |F̂(η)|² ν_R(dη)`. -/
theorem masked_hilbert_fourier_lintegral [SFinite μ] (hR : 0 < R) (F : SchwartzMap (Rd d) E) :
    ∫⁻ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ₑ ^ 2 ∂μ ≤
      ∫⁻ η, ‖paperHat (F : Rd d → E) η‖ₑ ^ 2 ∂nu μ ζ R := by
  have hFc : Continuous (paperHat (F : Rd d → E)) := continuous_paperHat F
  rw [lintegral_nu hR.ne' (hFc.enorm.measurable.pow_const 2),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ξ => ?_
  obtain ⟨-, -, hi⟩ := integrable_weighted hR.ne' F ξ
  calc ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ₑ ^ 2
      = ENNReal.ofReal (‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ ^ 2) :=
        (ofReal_norm_sq _).symm
    _ ≤ ENNReal.ofReal (cd d ^ 2 * Lz ζ *
          ∫ η, ‖kR ζ R (ξ - η)‖ * ‖paperHat (F : Rd d → E) η‖ ^ 2) :=
        ENNReal.ofReal_le_ofReal (norm_sq_paperHat_mask_le hR F ξ)
    _ = ENNReal.ofReal (cd d ^ 2 * Lz ζ) *
          ∫⁻ η, ENNReal.ofReal (‖kR ζ R (ξ - η)‖ * ‖paperHat (F : Rd d → E) η‖ ^ 2) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) Lz_nonneg),
          ofReal_integral_eq_lintegral_ofReal hi
            (Filter.Eventually.of_forall fun _ => by positivity)]
    _ = _ := by
        congr 1
        refine lintegral_congr fun η => ?_
        rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm_sq, ofReal_norm, mul_comm]

omit [CompleteSpace E] in
/-- The right side of `E:masked-hilbert-fourier` is finite (lines 134-135, "by
Schwartz decay and temperedness of `ν_R`"), for `μ` s-finite and tempered and
`R ≠ 0`. -/
theorem lintegral_paperHat_nu_lt_top [SFinite μ] (hμt : IsTempered μ) (hR : R ≠ 0)
    (F : SchwartzMap (Rd d) E) :
    ∫⁻ η, ‖paperHat (F : Rd d → E) η‖ₑ ^ 2 ∂nu μ ζ R < ⊤ := by
  obtain ⟨N, hN⟩ := hμt
  obtain ⟨C0, hC0, h0⟩ := exists_weight_bound (hatS F) 0
  obtain ⟨C1, hC1, h1⟩ := exists_weight_bound (hatS F) N
  have hpt : ∀ η, ‖paperHat (F : Rd d → E) η‖ₑ ^ 2 ≤
      ENNReal.ofReal (C0 * C1) * ENNReal.ofReal ((1 + ‖η‖) ^ (-(N : ℝ))) := by
    intro η
    have hp : 0 < (1 + ‖η‖) ^ N := by positivity
    have b0 : ‖paperHat (F : Rd d → E) η‖ ≤ C0 := by simpa [hatS_apply] using h0 η
    have b1 : ‖paperHat (F : Rd d → E) η‖ ≤ C1 * ((1 + ‖η‖) ^ N)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
      simpa [hatS_apply] using h1 η
    rw [← ofReal_norm_sq, ← ENNReal.ofReal_mul (mul_nonneg hC0 hC1)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, sq]
    calc ‖paperHat (F : Rd d → E) η‖ * ‖paperHat (F : Rd d → E) η‖
        ≤ C0 * (C1 * ((1 + ‖η‖) ^ N)⁻¹) :=
          mul_le_mul b0 b1 (norm_nonneg _) hC0
      _ = _ := by ring
  refine (lintegral_mono hpt).trans_lt ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ((lintegral_weight_nu_le hR N).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top hN (lintegral_weight_kR_lt_top hR N))))

omit [CompleteSpace E] in
/-- Auxiliary to the Lean proof route. `(ζ_R F)^` is continuous (`R ≠ 0`):
`ζ_R F` is a Schwartz map. -/
theorem continuous_paperHat_mask (hR : R ≠ 0) (F : SchwartzMap (Rd d) E) :
    Continuous (paperHat (fun x => (zetaR ζ R x : ℂ) • F x)) := by
  have he : (fun x => (zetaR ζ R x : ℂ) • F x) =
      ⇑(SchwartzMap.smulLeftCLM E (⇑(zetaS ζ R hR)) F) := by
    funext x
    rw [SchwartzMap.smulLeftCLM_apply_apply (zetaS ζ R hR).hasTemperateGrowth, zetaS_apply]
  rw [he]
  exact continuous_paperHat _

/-- **`E:masked-hilbert-fourier`** (lines 93-98) for a Schwartz map `F` with
values in a complex Banach space `E`, `μ` s-finite and tempered, `R > 0`:
both sides are integrable, `∫ |(ζ_R F)^|² dμ ≤ ∫ |F̂|² dν_R` as Bochner
integrals and as lower integrals, and the right side is finite.  The
manuscript states it for a separable complex Hilbert space; neither the inner
product nor separability is used. -/
theorem masked_hilbert_fourier [SFinite μ] (hμt : IsTempered μ) (hR : 0 < R)
    (F : SchwartzMap (Rd d) E) :
    Integrable (fun ξ => ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ ^ 2) μ ∧
      Integrable (fun η => ‖paperHat (F : Rd d → E) η‖ ^ 2) (nu μ ζ R) ∧
      ∫⁻ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ₑ ^ 2 ∂μ ≤
        ∫⁻ η, ‖paperHat (F : Rd d → E) η‖ₑ ^ 2 ∂nu μ ζ R ∧
      ∫⁻ η, ‖paperHat (F : Rd d → E) η‖ₑ ^ 2 ∂nu μ ζ R < ⊤ ∧
      ∫ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ ^ 2 ∂μ ≤
        ∫ η, ‖paperHat (F : Rd d → E) η‖ ^ 2 ∂nu μ ζ R := by
  have hle := masked_hilbert_fourier_lintegral (μ := μ) (ζ := ζ) hR F
  have hfin := lintegral_paperHat_nu_lt_top (ζ := ζ) hμt hR.ne' F
  have hGc := continuous_paperHat_mask (ζ := ζ) hR.ne' F
  have hFc : Continuous (paperHat (F : Rd d → E)) := continuous_paperHat F
  set G := paperHat (fun x => (zetaR ζ R x : ℂ) • F x) with hG
  set Fh := paperHat (F : Rd d → E) with hFh
  have hGm : AEStronglyMeasurable (fun ξ => ‖G ξ‖ ^ 2) μ :=
    (hGc.norm.pow 2).aestronglyMeasurable
  have hFm : AEStronglyMeasurable (fun η => ‖Fh η‖ ^ 2) (nu μ ζ R) :=
    (hFc.norm.pow 2).aestronglyMeasurable
  have hG0 : 0 ≤ᵐ[μ] fun ξ => ‖G ξ‖ ^ 2 := Filter.Eventually.of_forall fun _ => by positivity
  have hF0 : 0 ≤ᵐ[nu μ ζ R] fun η => ‖Fh η‖ ^ 2 :=
    Filter.Eventually.of_forall fun _ => by positivity
  have eG : ∫⁻ ξ, ENNReal.ofReal (‖G ξ‖ ^ 2) ∂μ = ∫⁻ ξ, ‖G ξ‖ₑ ^ 2 ∂μ :=
    lintegral_congr fun _ => ofReal_norm_sq _
  have eF : ∫⁻ η, ENNReal.ofReal (‖Fh η‖ ^ 2) ∂nu μ ζ R = ∫⁻ η, ‖Fh η‖ₑ ^ 2 ∂nu μ ζ R :=
    lintegral_congr fun _ => ofReal_norm_sq _
  refine ⟨⟨hGm, (hasFiniteIntegral_iff_ofReal hG0).2 ?_⟩,
    ⟨hFm, (hasFiniteIntegral_iff_ofReal hF0).2 ?_⟩, hle, hfin, ?_⟩
  · rw [eG]; exact hle.trans_lt hfin
  · rw [eF]; exact hfin
  · rw [integral_eq_lintegral_of_nonneg_ae hG0 hGm, integral_eq_lintegral_of_nonneg_ae hF0 hFm,
      eG, eF]
    exact ENNReal.toReal_mono hfin.ne hle

end Hilbert

/-! ### `P:masked-auxiliary-norm` -/

/-- **`P:masked-auxiliary-norm`** (lines 88-100), general form. Hypotheses:
`μ` s-finite, tempered and even; the spectral convention
`E:masked-spectral-convention` (`IsSpectralMeasure Γ μ`); the scaling
`Γ(cA) = c^{d-α}Γ(A)` (`SpectralHomogeneous Γ (d - α)`); `ζ` a nonzero real
Schwartz function; `E` a complex Banach space and `F` an `E`-valued Schwartz
map.  Conclusions: `ζ̂` is integrable and `L > 0` (line 82); for every
`R > 0`: `k_R` is integrable with `‖k_R‖₁ = L` (line 81); `ν_R` is even,
tempered and locally finite (Radon); `ν_R(B(y,r)) ≤ c_d² L² C_Γ r^α` for open
and closed balls, with a constant independent of `R`
(`E:masked-auxiliary-growth`); and `E:masked-hilbert-fourier` with both sides
integrable, as Bochner and as lower integrals, the right side finite. -/
theorem masked_auxiliary_norm {Γ μ : Measure (Rd d)} {alpha : ℝ} [SFinite μ]
    (hμt : IsTempered μ) (hμe : IsEven μ) (hsp : IsSpectralMeasure Γ μ)
    (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha)) (ζ : SchwartzMap (Rd d) ℝ) (hζ : ζ ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (F : SchwartzMap (Rd d) E) :
    (Integrable (paperHat (fun x => (ζ x : ℂ))) ∧ 0 < Lz ζ) ∧
      ∀ R : ℝ, 0 < R →
        (Integrable (kR ζ R) ∧ ∫ u, ‖kR ζ R u‖ = Lz ζ) ∧
        IsEven (nu μ ζ R) ∧ IsTempered (nu μ ζ R) ∧ IsLocallyFiniteMeasure (nu μ ζ R) ∧
        (∀ y : Rd d, ∀ r : ℝ, 0 < r →
          nu μ ζ R (ball y r) ≤ ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha) ∧
          nu μ ζ R (closedBall y r) ≤
            ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha)) ∧
        (Integrable (fun ξ => ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ ^ 2) μ ∧
          Integrable (fun η => ‖paperHat (F : Rd d → E) η‖ ^ 2) (nu μ ζ R) ∧
          ∫⁻ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ₑ ^ 2 ∂μ ≤
            ∫⁻ η, ‖paperHat (F : Rd d → E) η‖ₑ ^ 2 ∂nu μ ζ R ∧
          ∫⁻ η, ‖paperHat (F : Rd d → E) η‖ₑ ^ 2 ∂nu μ ζ R < ⊤ ∧
          ∫ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ ^ 2 ∂μ ≤
            ∫ η, ‖paperHat (F : Rd d → E) η‖ ^ 2 ∂nu μ ζ R) :=
  ⟨Lz_pos ζ hζ, fun _ hR =>
    ⟨⟨integrable_kR ζ hR.ne', integral_norm_kR ζ hR⟩, isEven_nu hR.ne' hμe,
      isTempered_nu hμt hR.ne', isLocallyFiniteMeasure_nu hμt hsp hΓs hR,
      fun y _ hr => ⟨nu_ball_le hμt hsp hΓs hR y hr, nu_closedBall_le hμt hsp hΓs hR y hr⟩,
      masked_hilbert_fourier hμt hR F⟩⟩

/-- **`P:masked-auxiliary-norm` with the manuscript's hypotheses**: the
section's standing assumptions `H:homog` (`HomogCovariance`) and `Γ ≠ 0`
(lines 5-6; `a = α₀` plays no role here), `ζ` a real nonzero Schwartz function
(line 79), `R > 0`, and `H` a separable complex Hilbert space with an
`H`-valued Schwartz map `F` (lines 93-94).  Conclusions as in
`masked_auxiliary_norm`.  Uses the fields `μ_radon` (for s-finiteness),
`μ_tempered`, `μ_even`, `spectral` and `scaling` of `H:homog`; `Γ ≠ 0`, the
inner product and the separability of `H` are carried, unused.  The clause
"for a real `H`, the same assertion holds after complexification" (line 99)
is not formalized (narrower). -/
theorem masked_auxiliary_norm_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (h : HomogCovariance d alpha alpha0 Γ μ) (_hΓ : Γ ≠ 0) (ζ : SchwartzMap (Rd d) ℝ)
    (hζ : ζ ≠ 0) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (F : SchwartzMap (Rd d) H) :
    (Integrable (paperHat (fun x => (ζ x : ℂ))) ∧ 0 < Lz ζ) ∧
      ∀ R : ℝ, 0 < R →
        (Integrable (kR ζ R) ∧ ∫ u, ‖kR ζ R u‖ = Lz ζ) ∧
        IsEven (nu μ ζ R) ∧ IsTempered (nu μ ζ R) ∧ IsLocallyFiniteMeasure (nu μ ζ R) ∧
        (∀ y : Rd d, ∀ r : ℝ, 0 < r →
          nu μ ζ R (ball y r) ≤ ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha) ∧
          nu μ ζ R (closedBall y r) ≤
            ENNReal.ofReal (cd d ^ 2 * Lz ζ ^ 2 * CGamma Γ * r ^ alpha)) ∧
        (Integrable (fun ξ => ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ ^ 2) μ ∧
          Integrable (fun η => ‖paperHat (F : Rd d → H) η‖ ^ 2) (nu μ ζ R) ∧
          ∫⁻ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ₑ ^ 2 ∂μ ≤
            ∫⁻ η, ‖paperHat (F : Rd d → H) η‖ₑ ^ 2 ∂nu μ ζ R ∧
          ∫⁻ η, ‖paperHat (F : Rd d → H) η‖ₑ ^ 2 ∂nu μ ζ R < ⊤ ∧
          ∫ ξ, ‖paperHat (fun x => (zetaR ζ R x : ℂ) • F x) ξ‖ ^ 2 ∂μ ≤
            ∫ η, ‖paperHat (F : Rd d → H) η‖ ^ 2 ∂nu μ ζ R) := by
  have := h.μ_radon
  exact masked_auxiliary_norm h.μ_tempered h.μ_even h.spectral h.scaling ζ hζ F

end StratonovichHAMSecondMoment.MaskedAuxiliaryNorm
