module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

The spatial white-noise model of Section `S:intrinsic-white-evaluation` of
`notes/integrated_white_evaluation.tex` (revision 39f2597a, lines 1-11): `d = α = 1`,
`Γ = c δ₀` with `c ≥ 0`, temporal kernel `|s-t|^{-a}` with `0 < a < 1`.  This module
formalizes the prerequisites of `T:white-moment-bounds` (statement lines 140-151, proof
lines 153-167 of `integrated_white_evaluation.tex`) that do not use the spatial energy
value of `P:white-spatial-energy`.

Objects (new definitions): `whiteCov c = c δ₀` and `whiteSpectral c = (c/(2π)) · Lebesgue`,
both measures on `ℝ¹ = HomogHypothesis.Rd 1`, the coefficient `c` entering through
`ENNReal.ofReal c` (so for `c < 0`, outside the manuscript's range, both are the zero
measure; every statement below that is meant for the manuscript carries `0 ≤ c` or
`0 < c` explicitly).

What is formalized, in full:
* (a) `white_homogCovariance`: for `c ≥ 0` and `0 < a < 1` the pair `(c δ₀, (c/(2π)) Leb)`
  satisfies `H:homog` (main TeX `notes_stratonovich_ham_second_moment.tex`, lines 384-400,
  whose lines 399-400 name spatial white noise as the case `α = d = 1`) in the package's form
  `HomogHypothesis.HomogCovariance 1 1 a`: both measures are Radon (locally finite), even
  and tempered; `c δ₀` is positive definite (the pairing with `φ ⋆ φ̃` is `c ∫ |φ|²`); the
  spectral identity `∫ φ d(c δ₀) = ∫ (∫ φ(x) e^{iξx} dx) (c/(2π)) dξ` holds for every
  Schwartz `φ` (Fourier inversion at `0`); `Γ(lA) = l^{d-α} Γ(A) = Γ(A)`; `α = d = 1`;
  `a + 1 < 2`.  The statement that white noise is an instance of `H:homog` is asserted
  in the main TeX (lines 399-400) and assumed in lines 4-9 of the white section; no proof is
  written in the TeX.  Also `whiteSpectral_homogeneous`: `μ(lA) = l μ(A)`
  (`SpectralHomog.SpectralHomogeneous μ 1`).
* (b) `whiteSpectral_closedBall`, `whiteSpectral_ball`: `V = μ{|ξ| ≤ 1} = μ{|ξ| < 1} = c/π`
  (`V` as defined at main TeX line 5559, closed ball, and line 1069, `μ(B_1)`).
* (c) `spatialPair_whiteCov`, `spatialEnergy_whiteCov`: for `c ≥ 0` and every real `f`,
  `B_Γ(f², f²) = c ∫ f⁴` for the real pairing `SpatialFourierBound.spatialPair` (TeX line 9:
  `A_sp(f) = cA`, `A = ∫ f⁴`); `pairing_whiteCov`, `pairing_sq_whiteCov`: the same for the
  extended pairing `OccupationKernelRow.pairing`, `B_Γ(F, H) = c ∫⁻ F H` in `[0,∞]` (stated for
  every real `c`; for `c < 0` both sides are `0`).  The
  real identity is between two Bochner integrals of the same function, so it needs no
  integrability hypothesis and asserts none (if `f⁴` is not integrable both sides are
  `0`); the `[0,∞]` identity has no junk value.
* (d) `F0_white`, `two_pow_F0_white`: the arithmetic of TeX lines 154-161 at `α = 1`
  (`q = 3`, `k = 2`, `m = 3/2`): `F₀(c²/6) = √c/(3√2)` and `2^m F₀(c²/6) = (2/3)√c` for
  `c ≥ 0`; `white_bracket_lower`, `white_bracket_upper`: the two sides of
  `E:intrinsic-spatial-bracket` (`integrated_occupation_ceiling.tex` lines 323-327) at
  `α = 1` and `z = c²/6`, `2^m M_a^{-1/k} F₀(c²/6)` and `2^m K₀^{1/k} F₀(c²/6)`, equal
  `WhiteRelativeWidth.lowerFormula c a` and `upperFormula c a` (the two sides of
  `E:white-moment-bounds`, TeX lines 143-144), with `M_a = TemporalEquilibrium.mass a`
  (`= WhiteRelativeWidth.boundMass a`) and `K₀ = WhiteRelativeWidth.boundK0 a`.

Scope (what this module does not claim).  The value `𝓔_sp = c²/6` is
`P:white-spatial-energy` (TeX lines 79-133), reserved (package B9): it is neither used nor
proved here; (d) evaluates `F₀` at the number `c²/6`, not at `SpatialFourLinear.Esp`.
`T:white-moment-bounds` itself (the bracket for `C_2`) is not stated here.

Exact-hypothesis wrappers (these are the section's setup and proof steps, not labelled
results): `white_model_paper` ((a), (b)) and `white_pairing_paper` ((c)) with the section's
`c ≥ 0`, `0 < a < 1` (lines 4-5); `white_score_arithmetic_paper` ((d)) with `c > 0` as in
TeX line 159 (the general lemmas hold for `c ≥ 0`, which covers the `c = 0` remark of
lines 164-165 that both displayed formulas vanish).

Proof route (the TeX gives none for (a)-(c)).  The spectral identity: the inner integral is
`𝓕φ(-ξ/(2π))` in Mathlib's convention `𝓕φ(w) = ∫ e^{-2πi⟨v,w⟩} φ(v) dv`
(`inner_integral_eq_fourier`), the substitution `ξ = -2πη` gives the factor `2π`
(`Measure.integral_comp_smul`), and `∫ 𝓕φ = 𝓕⁻(𝓕φ)(0) = φ(0)` by Fourier inversion
(`Continuous.fourierInv_fourier_eq`).  The fallback (a named input `WhiteSpectral`) was not
needed.  `V` via the coordinate isometry `WaveGreen.coordOne`.  (d) by `Real.sqrt`/`rpow`
arithmetic.

No supplied inputs (named hypotheses); no Lean junk value makes a statement true (the
measures are nonnegative for `c ≥ 0`, `M_a, K₀ > 0` for `0 < a < 1`, and `c ≥ 0` under
every square root).
-/
public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.SpatialFourierBound
public import StratonovichHAMSecondMoment.OccupationKernelRow
public import StratonovichHAMSecondMoment.SpatialStaticControls
public import StratonovichHAMSecondMoment.SpatialFourLinear
public import StratonovichHAMSecondMoment.WhiteRelativeWidth
public import StratonovichHAMSecondMoment.TemporalEquilibrium
public import StratonovichHAMSecondMoment.WaveGreen

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal Pointwise FourierTransform

namespace StratonovichHAMSecondMoment.WhiteModel

open HomogHypothesis

/-! ### The model -/

/-- The white covariance `Γ = c δ₀` on `ℝ¹` (TeX line 4). -/
def whiteCov (c : ℝ) : Measure (Rd 1) := ENNReal.ofReal c • Measure.dirac 0

/-- Its spectral measure `μ = (c/(2π)) · Lebesgue` on `ℝ¹`, in the convention
`Γ = ∫ e^{iξx} μ(dξ)` of `H:homog` (main TeX lines 388-391). -/
def whiteSpectral (c : ℝ) : Measure (Rd 1) := ENNReal.ofReal (c / (2 * Real.pi)) • volume

/-! ### Radon, even, tempered -/

/-- Auxiliary to the Lean proof route: a finite multiple of a locally finite measure is
locally finite. -/
theorem isLocallyFiniteMeasure_smul {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (ν : Measure X) [IsLocallyFiniteMeasure ν] {r : ℝ≥0∞} (hr : r ≠ ∞) :
    IsLocallyFiniteMeasure (r • ν) :=
  ⟨fun x => by
    obtain ⟨s, hs, h⟩ := ν.finiteAt_nhds x
    exact ⟨s, hs, by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top hr.lt_top h⟩⟩

/-- `c δ₀` is a Radon (locally finite) measure. -/
theorem whiteCov_radon (c : ℝ) : IsLocallyFiniteMeasure (whiteCov c) :=
  isLocallyFiniteMeasure_smul _ ENNReal.ofReal_ne_top

/-- `(c/(2π)) Leb` is a Radon (locally finite) measure. -/
theorem whiteSpectral_radon (c : ℝ) : IsLocallyFiniteMeasure (whiteSpectral c) :=
  isLocallyFiniteMeasure_smul _ ENNReal.ofReal_ne_top

/-- `c δ₀` is even. -/
theorem whiteCov_even (c : ℝ) : IsEven (whiteCov c) := by
  unfold IsEven whiteCov
  ext s hs
  rw [Measure.map_apply measurable_neg hs, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurable_neg hs), Measure.dirac_apply' _ hs]
  have h0 : ((0 : Rd 1) ∈ (fun x : Rd 1 => -x) ⁻¹' s) ↔ (0 : Rd 1) ∈ s := by
    rw [Set.mem_preimage, neg_zero]
  by_cases h : (0 : Rd 1) ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (h0.2 h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt h0.1 h)]

/-- `(c/(2π)) Leb` is even. -/
theorem whiteSpectral_even (c : ℝ) : IsEven (whiteSpectral c) := by
  unfold IsEven whiteSpectral
  ext s hs
  rw [Measure.map_apply measurable_neg hs, Measure.smul_apply, Measure.smul_apply,
    ← Measure.map_apply measurable_neg hs, Measure.map_neg_eq_self]

/-- `c δ₀` is tempered (with `k = 0`). -/
theorem whiteCov_tempered (c : ℝ) : IsTempered (whiteCov c) := by
  refine ⟨0, ?_⟩
  rw [whiteCov, lintegral_smul_measure, lintegral_dirac]
  simp

/-- `(c/(2π)) Leb` is tempered (with `k = 2`: `(1 + |ξ|)^{-2}` is Lebesgue integrable on
`ℝ¹`). -/
theorem whiteSpectral_tempered (c : ℝ) : IsTempered (whiteSpectral c) := by
  refine ⟨2, ?_⟩
  have hI : Integrable (fun x : Rd 1 => (1 + ‖x‖) ^ (-(2 : ℝ))) volume :=
    integrable_one_add_norm (by simp)
  rw [whiteSpectral, lintegral_smul_measure]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  simpa using hI.lintegral_lt_top

/-! ### Positive definiteness and the spectral identity -/

/-- Auxiliary to the Lean proof route: integration against `c δ₀` (`c ≥ 0`),
`∫ f d(c δ₀) = c f(0)`. -/
theorem integral_whiteCov {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {c : ℝ} (hc : 0 ≤ c) (f : Rd 1 → E) : ∫ x, f x ∂(whiteCov c) = c • f 0 := by
  rw [whiteCov, integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal hc]

/-- `c δ₀` is positive definite (`c ≥ 0`): `⟨c δ₀, φ ⋆ φ̃⟩ = c ∫ |φ|²` is a nonnegative real. -/
theorem whiteCov_posdef {c : ℝ} (hc : 0 ≤ c) : IsPosDefDistr (whiteCov c) := by
  intro φ
  rw [integral_whiteCov hc]
  have hI : (∫ y, φ (0 + y) * (starRingEnd ℂ) (φ y)) =
      ((∫ y, Complex.normSq (φ y) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]; congr 1; ext y; rw [zero_add, Complex.mul_conj]
  rw [hI]
  refine ⟨by simp, ?_⟩
  rw [Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
  exact mul_nonneg hc (integral_nonneg fun y => Complex.normSq_nonneg _)

/-- Auxiliary to the Lean proof route: the inner integral of the spectral identity in Mathlib's
Fourier convention: `∫ φ(x) e^{iξx} dx = 𝓕φ(-ξ/(2π))`. -/
theorem inner_integral_eq_fourier (φ : Rd 1 → ℂ) (ξ : Rd 1) :
    ∫ x, φ x * Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) =
      𝓕 φ (-(2 * Real.pi)⁻¹ • ξ) := by
  rw [Real.fourier_eq]
  congr 1; ext x
  rw [Circle.smul_def, Real.fourierChar_apply, mul_comm]
  congr 2
  rw [real_inner_smul_right, real_inner_comm]
  push_cast
  field_simp

/-- The spectral identity (`c ≥ 0`): for every Schwartz `φ`,
`∫ φ d(c δ₀) = ∫ (∫ φ(x) e^{iξx} dx) (c/(2π)) dξ`, i.e. `μ = (c/(2π)) Leb` is the spectral
measure of `c δ₀` in the convention of `H:homog` (Fourier inversion at `0`). -/
theorem whiteSpectral_isSpectral {c : ℝ} (hc : 0 ≤ c) :
    IsSpectralMeasure (whiteCov c) (whiteSpectral c) := by
  intro φ
  have hFint : Integrable (𝓕 (φ : Rd 1 → ℂ)) volume := by
    have := (𝓕 φ).integrable (μ := (volume : Measure (Rd 1)))
    rwa [SchwartzMap.fourier_coe] at this
  have hinv : ∫ η, 𝓕 (φ : Rd 1 → ℂ) η = φ 0 := by
    have h0 := congrFun (Continuous.fourierInv_fourier_eq φ.continuous φ.integrable hFint) 0
    rw [Real.fourierInv_eq] at h0
    simpa using h0
  simp_rw [inner_integral_eq_fourier (φ : Rd 1 → ℂ)]
  rw [integral_whiteCov hc, whiteSpectral, integral_smul_measure,
    Measure.integral_comp_smul (volume : Measure (Rd 1)) (𝓕 (φ : Rd 1 → ℂ)), hinv,
    finrank_euclideanSpace_fin, ENNReal.toReal_ofReal (by positivity), smul_smul]
  congr 1
  rw [pow_one, inv_neg, inv_inv, abs_neg, abs_of_pos (by positivity)]
  field_simp

/-! ### Scaling and `H:homog` -/

/-- `Γ(lA) = l^{d-α} Γ(A)` with `d = α = 1`, i.e. `(c δ₀)(lA) = (c δ₀)(A)` (`l > 0`). -/
theorem whiteCov_scaling (c : ℝ) (A : Set (Rd 1)) (hA : MeasurableSet A) (l : ℝ) (hl : 0 < l) :
    whiteCov c (l • A) = ENNReal.ofReal (l ^ (((1 : ℕ) : ℝ) - 1)) * whiteCov c A := by
  have h1 : ((0 : Rd 1) ∈ l • A) ↔ (0 : Rd 1) ∈ A := by
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hl.ne', smul_zero]
  have hm : MeasurableSet (l • A) := hA.const_smul₀ l
  rw [whiteCov, Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ hm,
    Measure.dirac_apply' _ hA]
  by_cases h : (0 : Rd 1) ∈ A
  · simp [Set.indicator_of_mem h, Set.indicator_of_mem (h1.mpr h)]
  · simp [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt h1.mp h)]

/-- `μ(lA) = l μ(A)` (`l > 0`): the spectral measure is homogeneous of degree `α = 1`. -/
theorem whiteSpectral_homogeneous (c : ℝ) :
    SpectralHomog.SpectralHomogeneous (whiteSpectral c) 1 := by
  intro A _ l hl
  rw [whiteSpectral, Measure.smul_apply, Measure.smul_apply, Measure.addHaar_smul,
    finrank_euclideanSpace_fin, pow_one, Real.rpow_one, abs_of_pos hl, smul_eq_mul,
    smul_eq_mul]
  ring

/-- (a) The white model satisfies `H:homog` with `d = α = 1` and `α₀ = a`, for `c ≥ 0` and
`0 < a < 1`. -/
theorem white_homogCovariance {c a : ℝ} (hc : 0 ≤ c) (ha0 : 0 < a) (ha1 : a < 1) :
    HomogCovariance 1 1 a (whiteCov c) (whiteSpectral c) where
  dim := Or.inl rfl
  alpha0_pos := ha0
  alpha0_lt_one := ha1
  Γ_radon := whiteCov_radon c
  Γ_even := whiteCov_even c
  Γ_tempered := whiteCov_tempered c
  Γ_posdef := whiteCov_posdef hc
  μ_radon := whiteSpectral_radon c
  μ_even := whiteSpectral_even c
  μ_tempered := whiteSpectral_tempered c
  spectral := whiteSpectral_isSpectral hc
  scaling := fun A hA l hl => whiteCov_scaling c A hA l hl
  threshold := by linarith
  alpha_range := Or.inr ⟨by norm_num, rfl⟩

/-! ### (b) The spectral mass of the unit ball -/

/-- `V = μ{|ξ| ≤ 1} = c/π` (`c ≥ 0`). -/
theorem whiteSpectral_closedBall {c : ℝ} (hc : 0 ≤ c) :
    whiteSpectral c (closedBall 0 1) = ENNReal.ofReal (c / Real.pi) := by
  have hb : closedBall (0 : Rd 1) 1 = WaveGreen.coordOne ⁻¹' Icc (-1) 1 := by
    ext x; simp [WaveGreen.coordOne_apply, WaveGreen.norm_coord_one, abs_le]
  rw [whiteSpectral, Measure.smul_apply, hb,
    WaveGreen.coordOne_mp.measure_preimage measurableSet_Icc.nullMeasurableSet, Real.volume_Icc,
    smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  norm_num

/-- `μ{|ξ| < 1} = c/π` (`c ≥ 0`). -/
theorem whiteSpectral_ball {c : ℝ} (hc : 0 ≤ c) :
    whiteSpectral c (ball 0 1) = ENNReal.ofReal (c / Real.pi) := by
  rw [whiteSpectral, Measure.smul_apply, WaveGreen.ball_eq_preimage_coordOne,
    WaveGreen.coordOne_mp.measure_preimage measurableSet_Ioo.nullMeasurableSet, Real.volume_Ioo,
    smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  norm_num

/-- The real value `V = (μ{|ξ| ≤ 1}).toReal = c/π` (`c ≥ 0`). -/
theorem whiteSpectral_closedBall_toReal {c : ℝ} (hc : 0 ≤ c) :
    (whiteSpectral c (closedBall 0 1)).toReal = c / Real.pi := by
  rw [whiteSpectral_closedBall hc, ENNReal.toReal_ofReal (by positivity)]

/-! ### (c) The spatial pairing of squares -/

/-- `B_Γ(F, G) = c ∫ F G` for the real pairing `SpatialFourierBound.spatialPair` and
`Γ = c δ₀` (`c ≥ 0`), for all real `F`, `G` (both sides are the same Bochner integral up
to the factor `c`; no integrability is assumed or asserted). -/
theorem spatialPair_whiteCov {c : ℝ} (hc : 0 ≤ c) (F G : Rd 1 → ℝ) :
    SpatialFourierBound.spatialPair (whiteCov c) F G = c * ∫ x, F x * G x := by
  rw [SpatialFourierBound.spatialPair, integral_whiteCov hc]
  simp

/-- `A_sp(f) = B_Γ(f², f²) = c ∫ f⁴` for `Γ = c δ₀` (`c ≥ 0`; TeX line 9). -/
theorem spatialEnergy_whiteCov {c : ℝ} (hc : 0 ≤ c) (f : Rd 1 → ℝ) :
    SpatialFourierBound.spatialEnergy (whiteCov c) f = c * ∫ x, f x ^ 4 := by
  rw [SpatialFourierBound.spatialEnergy, spatialPair_whiteCov hc]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

/-- `B_Γ(F, H) = c ∫⁻ F H` in `[0,∞]` for the extended pairing `OccupationKernelRow.pairing`
(`ν = dx Γ(dy)`) and `Γ = c δ₀`, for all `F, H : ℝ¹ → [0,∞]` (no measurability needed). -/
theorem pairing_whiteCov (c : ℝ) (F H : Rd 1 → ℝ≥0∞) :
    OccupationKernelRow.pairing (whiteCov c) F H = ENNReal.ofReal c * ∫⁻ x, F x * H x := by
  have hrange : MeasurableSet (Set.range fun x : Rd 1 => (x, (0 : Rd 1))) := by
    rw [show (Set.range fun x : Rd 1 => (x, (0 : Rd 1))) = univ ×ˢ {0} by
      ext ⟨x, y⟩; simp [eq_comm]]
    exact MeasurableSet.univ.prod (measurableSet_singleton 0)
  have hemb : MeasurableEmbedding (fun x : Rd 1 => (x, (0 : Rd 1))) :=
    MeasurableEmbedding.of_measurable_inverse (measurable_id.prodMk measurable_const)
      hrange measurable_fst (fun x => rfl)
  rw [OccupationKernelRow.pairing, OccupationKernelRow.pairMeasure, whiteCov,
    Measure.prod_smul_right, lintegral_smul_measure, Measure.prod_dirac, hemb.lintegral_map]
  simp

/-- `A_sp(f) = B_Γ(f², f²) = c ∫⁻ f⁴` in `[0,∞]` for the extended pairing and `Γ = c δ₀`,
in the spelling `zE (f²)` of `SpatialStaticControls`. -/
theorem pairing_sq_whiteCov (c : ℝ) (f : Rd 1 → ℝ) :
    OccupationKernelRow.pairing (whiteCov c) (SpatialStaticControls.zE fun x => f x ^ 2)
        (SpatialStaticControls.zE fun x => f x ^ 2) =
      ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (f x ^ 4) := by
  rw [pairing_whiteCov]
  congr 1
  refine lintegral_congr fun x => ?_
  simp only [SpatialStaticControls.zE]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-! ### (d) The `F₀` arithmetic at `α = 1` -/

/-- Auxiliary to the Lean proof route: the bracket of `F₀` at `α = 1`, `z = c²/6` is `c/72`. -/
theorem F0_inner_white {c : ℝ} (hc : 0 ≤ c) :
    (2 * (c ^ 2 / 6) / (2 - 1)) ^ (((2 : ℝ) - 1) / 2) /
        (8 * ((4 : ℝ) - 1) ^ (((4 : ℝ) - 1) / 2)) = c / 72 := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := by positivity
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  rw [show ((2 : ℝ) - 1) / 2 = 1 / 2 by norm_num, show ((4 : ℝ) - 1) / 2 = 1 + 1 / 2 by norm_num,
    show (4 : ℝ) - 1 = 3 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    show 2 * (c ^ 2 / 6) / (2 - 1) = c ^ 2 / 3 by ring,
    Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_sq hc]
  field_simp
  linear_combination (-(24 : ℝ) * c) * hs3

/-- `F₀(c²/6) = √c/(3√2)` at `α = 1` (`c ≥ 0`; TeX lines 157-160). -/
theorem F0_white {c : ℝ} (hc : 0 ≤ c) :
    SpatialFourLinear.F0 1 (c ^ 2 / 6) = Real.sqrt c / (3 * Real.sqrt 2) := by
  unfold SpatialFourLinear.F0
  rw [F0_inner_white hc, show (1 : ℝ) / (3 - 1) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
    Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 72),
    show (72 : ℝ) = 6 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num),
    Real.sqrt_sq (by norm_num)]
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  field_simp
  ring

/-- `2^m F₀(c²/6) = (2/3)√c` at `α = 1`, `m = q/k = (4-1)/(3-1) = 3/2` (`c ≥ 0`; TeX lines
160-161). -/
theorem two_pow_F0_white {c : ℝ} (hc : 0 ≤ c) :
    (2 : ℝ) ^ (((4 : ℝ) - 1) / (3 - 1)) * SpatialFourLinear.F0 1 (c ^ 2 / 6) =
      2 / 3 * Real.sqrt c := by
  rw [F0_white hc, show ((4 : ℝ) - 1) / (3 - 1) = 1 + 1 / 2 by norm_num,
    Real.rpow_add (by norm_num), Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  field_simp

/-- The lower side of `E:intrinsic-spatial-bracket` at `α = 1` (`k = 2`, `m = 3/2`) and
`z = c²/6`: `2^m M_a^{-1/k} F₀(c²/6) = (2/3) √(c/M_a)`, the lower formula of
`E:white-moment-bounds` (`c ≥ 0`, `0 < a < 1`). -/
theorem white_bracket_lower {c a : ℝ} (hc : 0 ≤ c) (ha0 : 0 < a) (ha1 : a < 1) :
    (2 : ℝ) ^ (((4 : ℝ) - 1) / (3 - 1)) * TemporalEquilibrium.mass a ^ (-(1 / ((3 : ℝ) - 1))) *
        SpatialFourLinear.F0 1 (c ^ 2 / 6) = WhiteRelativeWidth.lowerFormula c a := by
  have hM := WhiteRelativeWidth.boundMass_pos ha0 ha1
  rw [← WhiteRelativeWidth.boundMass_eq_mass ha0 ha1, mul_right_comm, two_pow_F0_white hc,
    WhiteRelativeWidth.lowerFormula, show (1 : ℝ) / (3 - 1) = 1 / 2 by norm_num,
    Real.rpow_neg hM.le, ← Real.sqrt_eq_rpow, Real.sqrt_div' _ hM.le]
  have hs : 0 < Real.sqrt (WhiteRelativeWidth.boundMass a) := Real.sqrt_pos.2 hM
  field_simp

/-- The upper side of `E:intrinsic-spatial-bracket` at `α = 1` and `z = c²/6`:
`2^m K₀^{1/k} F₀(c²/6) = (2/3) √(c K₀)`, the upper formula of `E:white-moment-bounds`
(`c ≥ 0`, `0 < a < 1`). -/
theorem white_bracket_upper {c a : ℝ} (hc : 0 ≤ c) (ha1 : a < 1) :
    (2 : ℝ) ^ (((4 : ℝ) - 1) / (3 - 1)) * WhiteRelativeWidth.boundK0 a ^ (1 / ((3 : ℝ) - 1)) *
        SpatialFourLinear.F0 1 (c ^ 2 / 6) = WhiteRelativeWidth.upperFormula c a := by
  have hK := WhiteRelativeWidth.boundK0_pos ha1
  rw [mul_right_comm, two_pow_F0_white hc, WhiteRelativeWidth.upperFormula,
    show (1 : ℝ) / (3 - 1) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sqrt_mul hc]
  ring

/-! ### Exact-hypothesis wrappers -/

/-- (a) and (b) under the section's standing assumptions (TeX lines 4-5: `c ≥ 0`,
`0 < a < 1`): `(c δ₀, (c/(2π)) Leb)` satisfies `H:homog` with `d = α = 1`, `α₀ = a`; the
spectral measure is homogeneous of degree `1`; `V = μ{|ξ| ≤ 1} = μ{|ξ| < 1} = c/π`. -/
theorem white_model_paper {c a : ℝ} (hc : 0 ≤ c) (ha0 : 0 < a) (ha1 : a < 1) :
    HomogCovariance 1 1 a (whiteCov c) (whiteSpectral c) ∧
      SpectralHomog.SpectralHomogeneous (whiteSpectral c) 1 ∧
      whiteSpectral c (closedBall 0 1) = ENNReal.ofReal (c / Real.pi) ∧
      whiteSpectral c (ball 0 1) = ENNReal.ofReal (c / Real.pi) :=
  ⟨white_homogCovariance hc ha0 ha1, whiteSpectral_homogeneous c, whiteSpectral_closedBall hc,
    whiteSpectral_ball hc⟩

/-- (c) under the section's standing assumption `c ≥ 0` (TeX lines 4-9): for every real `f`,
`A_sp(f) = B_Γ(f², f²) = c ∫ f⁴`, for the real pairing (as Bochner integrals) and for the
extended pairing (in `[0,∞]`). -/
theorem white_pairing_paper {c : ℝ} (hc : 0 ≤ c) (f : Rd 1 → ℝ) :
    SpatialFourierBound.spatialPair (whiteCov c) (fun x => f x ^ 2) (fun x => f x ^ 2) =
        c * ∫ x, f x ^ 4 ∧
      OccupationKernelRow.pairing (whiteCov c) (SpatialStaticControls.zE fun x => f x ^ 2)
          (SpatialStaticControls.zE fun x => f x ^ 2) =
        ENNReal.ofReal c * ∫⁻ x, ENNReal.ofReal (f x ^ 4) :=
  ⟨spatialEnergy_whiteCov hc f, pairing_sq_whiteCov c f⟩

/-- (d) with the hypotheses of TeX line 159 (`c > 0`, and the section's `0 < a < 1`): at
`α = 1` (`k = 2`, `m = 3/2`), `F₀(c²/6) = √c/(3√2)`, `2^m F₀(c²/6) = (2/3)√c`, and the two
sides `2^m M_a^{-1/k} F₀(c²/6)`, `2^m K₀^{1/k} F₀(c²/6)` of `E:intrinsic-spatial-bracket` at
`z = c²/6` are the lower and upper formulas of `E:white-moment-bounds`.  The value
`𝓔_sp = c²/6` (`P:white-spatial-energy`) is not asserted. -/
theorem white_score_arithmetic_paper {c a : ℝ} (hc : 0 < c) (ha0 : 0 < a) (ha1 : a < 1) :
    SpatialFourLinear.F0 1 (c ^ 2 / 6) = Real.sqrt c / (3 * Real.sqrt 2) ∧
      (2 : ℝ) ^ (((4 : ℝ) - 1) / (3 - 1)) * SpatialFourLinear.F0 1 (c ^ 2 / 6) =
        2 / 3 * Real.sqrt c ∧
      (2 : ℝ) ^ (((4 : ℝ) - 1) / (3 - 1)) * TemporalEquilibrium.mass a ^ (-(1 / ((3 : ℝ) - 1))) *
          SpatialFourLinear.F0 1 (c ^ 2 / 6) = WhiteRelativeWidth.lowerFormula c a ∧
      (2 : ℝ) ^ (((4 : ℝ) - 1) / (3 - 1)) * WhiteRelativeWidth.boundK0 a ^ (1 / ((3 : ℝ) - 1)) *
          SpatialFourLinear.F0 1 (c ^ 2 / 6) = WhiteRelativeWidth.upperFormula c a :=
  ⟨F0_white hc.le, two_pow_F0_white hc.le, white_bracket_lower hc.le ha0 ha1,
    white_bracket_upper hc.le ha1⟩

end StratonovichHAMSecondMoment.WhiteModel
