module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

`L:phase-contractions` (Two static contraction bounds) of the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` at revision a284420: the
statement at lines 2072-2086 (displays `E:phase-resolvent`, `E:phase-trace` and
the definition of `T_ε`), its proof at lines 2088-2138, the standing
assumptions of Section `S:static-phase` at lines 2054-2057 and the constants of
`E:phase-constants` at lines 2058-2070.

Objects.  `PhaseCovariance α Γ μ` is the section's class (`0 < α < 2`, `Γ`
nonnegative, even, positive-definite, tempered, Radon on `ℝ³`,
`Γ(rA) = r^{3-α}Γ(A)`, `μ` its spectral measure in the convention
`Γ = ∫ e^{iξ·x} μ(dξ)`, `μ` locally finite, even, tempered as in `H:homog`);
`PhaseCovariance.of_homog` shows that `H:homog` in `d = 3` implies it.
`R_α` is `SpectralMassIdentity.ralpha` (`V = μ(B_1)`); `M`, `c_Γ`, `b_α`, `D_Γ` are
`massM`, `cGam`, `bAlpha`, `dGam` (`dGam_eq`: the expression of the `hDdef`
hypotheses of `IntervalScalar`).  `p_v` is `pdens v`
(`(2πv)^{-3/2} e^{-|x|²/(2v)}`, a probability density by `integral_pdens`),
`Γ_ε = p_{2ε} * Γ` is `gammaEps`, `G_a` is `WaveGreen.waveGreen 3 a` (the recorded
`toSphere` definitional choice of `WaveGreen`), `Ĝ_a` is `WaveKernel.waveHat a`,
and `T_ε(a,q) = ∫ e^{iq·x} Γ_ε(x) G_a(dx)` is `traceT`.

Formalized:
* `phase_contractions_paper`: the lemma under `PhaseCovariance` and the two
  supplied inputs below: `E:phase-resolvent` with integrability; for every
  `x`, the integrability of `y ↦ p_{2ε}(x-y)` against `Γ` and `Γ_ε(x) ≥ 0`;
  the integrability of both integrands of `T_ε`; the identity
  `T_ε(a,q) = ∫ Ĝ_a(q+ξ) e^{-ε|ξ|²} μ(dξ)`; and `|T_ε(a,q)| ≤ D_Γ a^{1-α}`.
* General forms with fewer hypotheses: `phase_resolvent` (every `d`; also
  `R_Γ(λ) = λ^{α-2} R_α` at `q = 0`), `phase_trace` (no spectral measure, no
  Fourier input; also `T_ε(a,0) = ∫ Γ_ε dG_a` and `|T_ε(a,q)| ≤ T_ε(a,0)`),
  `traceT_fourier`, and the proof steps `gauss_shift_le` (Gaussian Fourier
  pairing), `lintegral_norm_radial` (radial law), `measure_singleton_zero`,
  `lintegral_waveGreen_three` (integration over the normal coordinate),
  `sphere_convolution` (the sphere convolution formula),
  `integral_normal_coordinate`, `three_regions`, `middle_region_le`,
  `kernel_le_bAlpha` and `gammaEps_fourier`.

Supplied inputs (named hypotheses, both being proved by wave item L9-G, to be
instantiated at integration):
* `WaveFourierThree`: `∫ e^{iξ·x} G_s(dx) = sin(s|ξ|)/|ξ|` (value `s` at
  `ξ = 0`, `waveHat s ξ`) for `s > 0`, `ξ ∈ ℝ³`.  It is the `d = 3` case of the
  formula `Ĝ_s(ξ) = sin(s|ξ|)/|ξ|` of main TeX lines 777-778 for the measure
  `G_s`, which the TeX uses as `Ĝ_a` at lines 2083 and 2107-2108; no
  stronger.  Used only for the Fourier form of `T_ε`.
* `ArchimedesLaw`: for every unit `e ∈ ℝ³`, the image of `volume.toSphere`
  under `ω ↦ ⟨e,ω⟩` is `2π` Lebesgue measure on `[-1,1]`.  It is the
  classical fact behind "direct integration over its normal coordinate" (main
  TeX lines 2125-2126) and behind the radiality of `G_a * p_{2ε}` (line 2118);
  it concerns only the sphere measure, not the covariance.  Used only for the
  bound `E:phase-trace`.

Implicit hypotheses made explicit: the integrability of every integrand
(conclusions, so no statement holds through the junk value of a
non-integrable Bochner integral); `μ(B_1)`, `Γ(B_1)` are finite (local
finiteness), so `R_α` and `D_Γ` use no junk `toReal`; `2 - α > 0` and
`sin(πα/2) > 0`, so no division by zero; Borel sets in the scaling.  No
`Γ ≠ 0` is assumed (for `Γ = 0` both bounds hold with value `0`).

Hypotheses carried but unused (checked through every lemma called):
`Γ_even`, `Γ_posdef` and `μ_even` of `PhaseCovariance`.

Differences from the TeX (proof route; statements are the TeX's):
* Gaussian pairing: both sides are written by
  `MaskedSpectralGrowth.masked_gaussian_transform`, and the shifted one is
  bounded by its absolute value (`|e^{iq·x}| = 1`, `Γ ≥ 0`), so evenness is not
  needed for the realness used by the TeX.
* The value at `q = 0` is `SpectralMassIdentity.resolvent_eq_ralpha` (layer
  cake and a Beta integral) instead of the polar formula; `μ(cA) = c^α μ(A)` is
  `MaskedSpectralGrowth.spectralHomogeneous_of_scaling`.
* The radial law is proved for nonnegative measurable radial functions
  `F(x) = f(|x|)` (not only Schwartz ones), by identifying the image of `Γ`
  under `|·|` on the intervals `(-∞, t)`; the same lemma for Lebesgue measure
  (`β = 3`, `vol(B_1) = 4π/3`) gives the factor `c_Γ`.  All Fubini steps are
  nonnegative (lower integrals); the radial form of `G_a * p_{2ε}` comes from
  Archimedes' law.  Instead of evaluating `[p_{2ε} * (G_a * |·|^{-α})](0)` the
  Lean proof bounds `∫ p_{2ε}(z) (G_a * |·|^{-α})(-z) dz` by the supremum
  (the same quantity after the substitution `z ↦ -z`).
* The three regions are taken closed (`r ≤ a/2`, `r ≥ 2a`,
  `a/2 ≤ r ≤ 2a`), so no continuity argument is needed; the outer bounds use
  the TeX's distance bounds `a/2` and `a` (`kernel_le_of_dist`).
Lemmas marked "Auxiliary to the Lean proof route" have no manuscript label.

Narrower conclusions: none relative to the TeX statement, given the two
supplied inputs.  The fallback of the wave plan (the trace identity as a
named input) was not needed: the identity is proved from `WaveFourierThree`.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.MaskedSpectralGrowth
public import StratonovichHAMSecondMoment.SpectralMassIdentity
public import StratonovichHAMSecondMoment.WaveKernel
public import StratonovichHAMSecondMoment.WaveGreen

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter Metric
open scoped ENNReal Pointwise

namespace StratonovichHAMSecondMoment.PhaseContractions

open HomogHypothesis SpectralHomog MaskedSpectralGrowth SpectralMassIdentity WaveKernel WaveGreen

/-! ### The section's covariance class and constants -/

/-- The standing assumptions of Section `S:static-phase` (main TeX lines
2054-2057 at a284420): `0 < α < 2`; `Γ` a nonnegative, even,
positive-definite, tempered Radon measure on `ℝ³` with `Γ(rA) = r^{3-α}Γ(A)`
(Borel `A`, `r > 0`); `μ` its spectral measure in the convention
`Γ = ∫ e^{iξ·x} μ(dξ)` (`HomogHypothesis.IsSpectralMeasure`), a positive even
tempered Radon measure as in `H:homog`.  A Lean measure is nonnegative; on
`ℝ³` a locally finite Borel measure is Radon.  This is the three-dimensional
class of `H:homog` without the parameter `α₀` (`of_homog`). -/
structure PhaseCovariance (alpha : ℝ) (Γ μ : Measure (Rd 3)) : Prop where
  alpha_pos : 0 < alpha
  alpha_lt_two : alpha < 2
  Γ_radon : IsLocallyFiniteMeasure Γ
  Γ_even : IsEven Γ
  Γ_tempered : IsTempered Γ
  Γ_posdef : IsPosDefDistr Γ
  μ_radon : IsLocallyFiniteMeasure μ
  μ_even : IsEven μ
  μ_tempered : IsTempered μ
  spectral : IsSpectralMeasure Γ μ
  scaling : ∀ A : Set (Rd 3), MeasurableSet A → ∀ c : ℝ, 0 < c →
    Γ (c • A) = ENNReal.ofReal (c ^ ((3 : ℝ) - alpha)) * Γ A

/-- Every covariance allowed by `H:homog` in `d = 3` belongs to the class of
Section `S:static-phase` (`α < 2` from `α₀ + α < 2` and `α₀ > 0`). -/
theorem PhaseCovariance.of_homog {alpha alpha0 : ℝ} {Γ μ : Measure (Rd 3)}
    (h : HomogCovariance 3 alpha alpha0 Γ μ) : PhaseCovariance alpha Γ μ where
  alpha_pos := (alpha_mem_Ioo_of_homog h).1
  alpha_lt_two := (alpha_mem_Ioo_of_homog h).2
  Γ_radon := h.Γ_radon
  Γ_even := h.Γ_even
  Γ_tempered := h.Γ_tempered
  Γ_posdef := h.Γ_posdef
  μ_radon := h.μ_radon
  μ_even := h.μ_even
  μ_tempered := h.μ_tempered
  spectral := h.spectral
  scaling := by
    intro A hA c hc
    have := h.scaling A hA c hc
    simpa using this

/-- Auxiliary to the Lean proof route: the scaling field in the form
`SpectralHomogeneous Γ (3 - α)` used by `MaskedSpectralGrowth` (with `d = 3`). -/
theorem PhaseCovariance.scaling' {alpha : ℝ} {Γ μ : Measure (Rd 3)}
    (h : PhaseCovariance alpha Γ μ) : SpectralHomogeneous Γ (((3 : ℕ) : ℝ) - alpha) := by
  intro A hA c hc
  have := h.scaling A hA c hc
  simpa using this

/-- `M = Γ(B_1)` (`E:phase-constants`, main TeX line 2060; `B_1` the open unit
ball, line 2067), as a real number (finite for locally finite `Γ`). -/
def massM (Γ : Measure (Rd 3)) : ℝ := (Γ (ball (0 : Rd 3) 1)).toReal

/-- `c_Γ = (3-α)M/(4π)` (`E:phase-constants`, main TeX line 2062). -/
def cGam (Γ : Measure (Rd 3)) (alpha : ℝ) : ℝ := (3 - alpha) * massM Γ / (4 * π)

/-- `b_α = 2^α + 3^{2-α}/(2-α)` (`E:phase-constants`, main TeX line 2063). -/
def bAlpha (alpha : ℝ) : ℝ := 2 ^ alpha + 3 ^ (2 - alpha) / (2 - alpha)

/-- `D_Γ = c_Γ b_α` (`E:phase-constants`, main TeX line 2064). -/
def dGam (Γ : Measure (Rd 3)) (alpha : ℝ) : ℝ := cGam Γ alpha * bAlpha alpha

/-- `D_Γ` is the expression carried by the `hDdef` hypotheses of
`IntervalScalar` (`static_interaction_paper` and its relatives). -/
theorem dGam_eq (Γ : Measure (Rd 3)) (alpha : ℝ) :
    dGam Γ alpha = (3 - alpha) * (Γ (ball 0 1)).toReal / (4 * π) *
      (2 ^ alpha + 3 ^ (2 - alpha) / (2 - alpha)) := rfl

/-! ### `E:phase-resolvent` -/

/-- The Gaussian Fourier pairing step of the proof of `L:phase-contractions`
(main TeX lines 2090-2098): for `s > 0` and `q ∈ ℝ^d`,
`∫ e^{-s|q+ξ|²} μ(dξ) ≤ ∫ e^{-s|ξ|²} μ(dξ)`.  Only the spectral convention is
assumed.  Proof route: `MaskedSpectralGrowth.masked_gaussian_transform` writes
both sides as Gaussian-weighted Fourier integrals of `Γ`, and the left one is
bounded by its absolute value (`|e^{iq·x}| = 1`, `Γ ≥ 0`), instead of the
TeX's realness from evenness. -/
theorem gauss_shift_le {d : ℕ} {Γ μ : Measure (Rd d)} (hsp : IsSpectralMeasure Γ μ)
    (s : ℝ) (hs : 0 < s) (q : Rd d) :
    ∫ ξ, Real.exp (-(s * ‖q + ξ‖ ^ 2)) ∂μ ≤ ∫ ξ, Real.exp (-(s * ‖ξ‖ ^ 2)) ∂μ := by
  set r : ℝ := (Real.sqrt s)⁻¹ with hr_def
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hr : 0 < r := inv_pos.2 hsq
  have hr2 : r ^ 2 = s⁻¹ := by rw [hr_def, inv_pow, Real.sq_sqrt hs.le]
  have hpt : ∀ v : Rd d, ‖v‖ ^ 2 / r ^ 2 = s * ‖v‖ ^ 2 := by
    intro v; rw [hr2, div_inv_eq_mul, mul_comm]
  have hT := masked_gaussian_transform hsp (-q) r hr
  have hT0 := masked_gaussian_transform hsp 0 r hr
  simp only [sub_neg_eq_add, sub_zero] at hT hT0
  simp only [hpt] at hT hT0
  simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
    mul_one] at hT0
  rw [integral_complex_ofReal, ← Complex.ofReal_mul] at hT0
  have h0 := Complex.ofReal_injective hT0
  have hL : ∫ ξ, Real.exp (-(s * ‖q + ξ‖ ^ 2)) ∂μ = ∫ ξ, Real.exp (-(s * ‖ξ + q‖ ^ 2)) ∂μ := by
    simp_rw [add_comm q]
  rw [hL, h0]
  have hnorm := congrArg norm hT
  rw [Complex.norm_real, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (r / (2 * Real.sqrt Real.pi)) ^ d)] at hnorm
  have hle := norm_integral_le_integral_norm (μ := Γ) (fun x : Rd d =>
    (Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) * Complex.exp (-(Complex.I * (inner ℝ (-q) x : ℝ))))
  have hpt2 : ∀ x : Rd d, ‖(Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ (-q) x : ℝ)))‖ = Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Complex.norm_exp]
    simp
  simp only [hpt2] at hle
  calc ∫ ξ, Real.exp (-(s * ‖ξ + q‖ ^ 2)) ∂μ
      ≤ ‖∫ ξ, Real.exp (-(s * ‖ξ + q‖ ^ 2)) ∂μ‖ := Real.le_norm_self _
    _ = (r / (2 * Real.sqrt Real.pi)) ^ d * ‖∫ x, (Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ (-q) x : ℝ))) ∂Γ‖ := hnorm
    _ ≤ (r / (2 * Real.sqrt Real.pi)) ^ d * ∫ x, Real.exp (-(r ^ 2 * ‖x‖ ^ 2 / 4)) ∂Γ :=
        mul_le_mul_of_nonneg_left hle (by positivity)

/-- Auxiliary to the Lean proof route: the Laplace integral
`1/c = ∫_0^∞ e^{-cs} ds` (`c > 0`), as a lower integral. -/
theorem ofReal_inv_eq_lintegral_exp (c : ℝ) (hc : 0 < c) :
    ENNReal.ofReal (1 / c) = ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-c * s)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi (by linarith) 0)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le), integral_exp_mul_Ioi (by linarith) 0]
  congr 1
  simp [div_neg, neg_div]

/-- Auxiliary to the Lean proof route: the lower integral of the shifted
resolvent integrand is at most the unshifted one (the Laplace integral in `s`
of `gauss_shift_le`, with nonnegative Tonelli on the spectral side). -/
theorem lintegral_shift_resolvent_le {d : ℕ} {Γ μ : Measure (Rd d)} [SFinite μ]
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) (lam : ℝ) (hlam : 0 < lam) (q : Rd d) :
    ∫⁻ ξ, ENNReal.ofReal (1 / (lam ^ 2 + ‖q + ξ‖ ^ 2)) ∂μ ≤
      ∫⁻ ξ, ENNReal.ofReal (1 / (lam ^ 2 + ‖ξ‖ ^ 2)) ∂μ := by
  have hrep : ∀ w : Rd d, ∫⁻ ξ, ENNReal.ofReal (1 / (lam ^ 2 + ‖w + ξ‖ ^ 2)) ∂μ =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(lam ^ 2) * s)) *
        ENNReal.ofReal (∫ ξ, Real.exp (-(s * ‖w + ξ‖ ^ 2)) ∂μ) := by
    intro w
    have h1 : ∀ ξ : Rd d, ENNReal.ofReal (1 / (lam ^ 2 + ‖w + ξ‖ ^ 2)) =
        ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(lam ^ 2 + ‖w + ξ‖ ^ 2) * s)) :=
      fun ξ => ofReal_inv_eq_lintegral_exp _ (by positivity)
    simp_rw [h1]
    rw [lintegral_lintegral_swap (by fun_prop)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : 0 < s := hs
    have hint : Integrable (fun ξ : Rd d => Real.exp (-(s * ‖w + ξ‖ ^ 2))) μ := by
      have := integrable_gauss_of_tempered hμt hs0 (-w)
      refine this.congr (Eventually.of_forall fun ξ => ?_)
      simp only [sub_neg_eq_add, add_comm ξ w]
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun _ => (Real.exp_pos _).le), ← lintegral_const_mul _ (by fun_prop)]
    refine lintegral_congr fun ξ => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  rw [hrep q]
  have h0 := hrep 0
  simp only [zero_add] at h0
  rw [h0]
  refine setLIntegral_mono' measurableSet_Ioi fun s hs => ?_
  exact mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (gauss_shift_le hsp s hs q)) (zero_le)

/-- **`E:phase-resolvent`** (main TeX lines 2075-2077 at a284420, proof
2089-2105), general
form in every dimension `d`: for a locally finite tempered `μ` with the
spectral convention `IsSpectralMeasure Γ μ`, the scaling
`Γ(cA) = c^{d-α}Γ(A)` (`SpectralHomogeneous Γ (d - α)`) and `0 < α < 2`, for
every `λ > 0` and `q`: `ξ ↦ 1/(λ²+|q+ξ|²)` is `μ`-integrable and
`∫ μ(dξ)/(λ²+|q+ξ|²) ≤ R_α λ^{α-2}`, with equality `R_Γ(λ) = λ^{α-2} R_α` at
`q = 0` (`R_α = απ μ(B_1)/(2 sin(πα/2))`, `SpectralMassIdentity.ralpha`).
The homogeneity `μ(cA) = c^α μ(A)` is derived from the scaling of `Γ`
(`MaskedSpectralGrowth.spectralHomogeneous_of_scaling`); the value at `q = 0`
is `SpectralMassIdentity.resolvent_eq_ralpha` (layer cake and a Beta integral,
not the TeX's polar formula). -/
theorem phase_resolvent {d : ℕ} {alpha : ℝ} {Γ μ : Measure (Rd d)} [IsLocallyFiniteMeasure μ]
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ)
    (hΓs : SpectralHomogeneous Γ ((d : ℝ) - alpha)) (ha0 : 0 < alpha) (ha2 : alpha < 2)
    (lam : ℝ) (hlam : 0 < lam) (q : Rd d) :
    Integrable (fun ξ : Rd d => 1 / (lam ^ 2 + ‖q + ξ‖ ^ 2)) μ ∧
      ∫ ξ, 1 / (lam ^ 2 + ‖q + ξ‖ ^ 2) ∂μ ≤ ralpha μ alpha * lam ^ (alpha - 2) ∧
      SpectralHomog.resolvent μ lam = lam ^ (alpha - 2) * ralpha μ alpha := by
  have hI := spectralHomogeneous_of_scaling hμt hsp hΓs
  obtain ⟨hint0, heq⟩ := resolvent_eq_ralpha hI ha0 ha2 lam hlam
  have hle := lintegral_shift_resolvent_le hμt hsp lam hlam q
  have hnn : ∀ w ξ : Rd d, 0 ≤ 1 / (lam ^ 2 + ‖w + ξ‖ ^ 2) := fun _ _ => by positivity
  have h0 : ∫⁻ ξ, ENNReal.ofReal (1 / (lam ^ 2 + ‖ξ‖ ^ 2)) ∂μ =
      ENNReal.ofReal (SpectralHomog.resolvent μ lam) := by
    unfold SpectralHomog.resolvent
    rw [ofReal_integral_eq_lintegral_ofReal hint0
      (Eventually.of_forall fun ξ => by positivity)]
  rw [h0] at hle
  have hmeas : AEStronglyMeasurable (fun ξ : Rd d => 1 / (lam ^ 2 + ‖q + ξ‖ ^ 2)) μ :=
    (by fun_prop : Measurable fun ξ : Rd d => 1 / (lam ^ 2 + ‖q + ξ‖ ^ 2)).aestronglyMeasurable
  have hint : Integrable (fun ξ : Rd d => 1 / (lam ^ 2 + ‖q + ξ‖ ^ 2)) μ :=
    ⟨hmeas, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ξ => hnn q ξ)).2
      (hle.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_, heq⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ξ => hnn q ξ) hmeas]
  have hres0 : 0 ≤ SpectralHomog.resolvent μ lam := integral_nonneg fun ξ => by positivity
  calc (∫⁻ ξ, ENNReal.ofReal (1 / (lam ^ 2 + ‖q + ξ‖ ^ 2)) ∂μ).toReal
      ≤ (ENNReal.ofReal (SpectralHomog.resolvent μ lam)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = ralpha μ alpha * lam ^ (alpha - 2) := by
        rw [ENNReal.toReal_ofReal hres0, heq, mul_comm]

/-! ### The radial law -/

/-- Auxiliary to the Lean proof route: `∫_0^t r^{β-1} dr = t^β/β` for `t, β > 0`,
as a lower integral. -/
theorem lintegral_rpow_Ioo (β : ℝ) (hβ : 0 < β) (t : ℝ) (ht : 0 < t) :
    ∫⁻ r in Ioo (0 : ℝ) t, ENNReal.ofReal (r ^ (β - 1)) = ENNReal.ofReal (t ^ β / β) := by
  have hII : IntervalIntegrable (fun r : ℝ => r ^ (β - 1)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hIoo : IntegrableOn (fun r : ℝ => r ^ (β - 1)) (Ioo 0 t) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).1 hII
  rw [← ofReal_integral_eq_lintegral_ofReal hIoo
    ((ae_restrict_iff' measurableSet_Ioo).2
      (Eventually.of_forall fun r hr => Real.rpow_nonneg hr.1.le _))]
  congr 1
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
    integral_rpow (Or.inl (by linarith)), sub_add_cancel, Real.zero_rpow hβ.ne', sub_zero]

/-- Auxiliary to the Lean proof route: the image of a locally finite measure
`ν` on `ℝ^d` with `ν(cA) = c^β ν(A)` (`β > 0`) under `y ↦ |y|` is
`β ν(B_1) r^{β-1} dr` on `(0, ∞)`.  (No mass at the origin is needed
separately: the identity is checked on the intervals `(-∞, t)`.) -/
theorem map_norm_eq {d : ℕ} (ν : Measure (Rd d)) [IsLocallyFiniteMeasure ν] {β : ℝ}
    (hβ : 0 < β) (hs : SpectralHomogeneous ν β) :
    ν.map (fun y => ‖y‖) = (ENNReal.ofReal β * ν (ball (0 : Rd d) 1)) •
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun r => ENNReal.ofReal (r ^ (β - 1))) := by
  set ρ := (ENNReal.ofReal β * ν (ball (0 : Rd d) 1)) •
      (volume.restrict (Ioi (0 : ℝ))).withDensity (fun r => ENNReal.ofReal (r ^ (β - 1)))
  set V := ν (ball (0 : Rd d) 1)
  have hV : V ≠ ⊤ := measure_ball_lt_top.ne
  have hpre : ∀ t : ℝ, (fun y : Rd d => ‖y‖) ⁻¹' Iio t = ball (0 : Rd d) t := by
    intro t; ext y; simp
  have hL : ∀ t : ℝ, ν.map (fun y => ‖y‖) (Iio t) = ν (ball (0 : Rd d) t) := by
    intro t
    rw [Measure.map_apply measurable_norm measurableSet_Iio, hpre]
  have hR : ∀ t : ℝ, ρ (Iio t) = ν (ball (0 : Rd d) t) := by
    intro t
    have hρ : ρ (Iio t) = (ENNReal.ofReal β * V) *
        ∫⁻ r in Ioo (0 : ℝ) t, ENNReal.ofReal (r ^ (β - 1)) := by
      have hset : Iio t ∩ Ioi (0 : ℝ) = Ioo 0 t := by
        ext r; simp [and_comm]
      simp only [ρ, Measure.smul_apply, smul_eq_mul]
      rw [withDensity_apply _ measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, hset]
    rcases le_or_gt t 0 with ht | ht
    · rw [hρ, Ioo_eq_empty (not_lt.2 ht), Measure.restrict_empty, lintegral_zero_measure,
        mul_zero, ball_eq_empty.2 ht, measure_empty]
    · rw [hρ, lintegral_rpow_Ioo β hβ t ht, SpectralHomog.measure_ball hs t ht]
      calc ENNReal.ofReal β * V * ENNReal.ofReal (t ^ β / β)
          = (ENNReal.ofReal β * ENNReal.ofReal (t ^ β / β)) * V := by ring
        _ = ENNReal.ofReal (t ^ β) * V := by
            rw [← ENNReal.ofReal_mul hβ.le]
            congr 2
            field_simp
  have hfin : ∀ t : ℝ, ν (ball (0 : Rd d) t) ≠ ⊤ := fun t => measure_ball_lt_top.ne
  have hIco : ∀ a b : ℝ, a < b → Ico a b = Iio b \ Iio a := by
    intro a b _; ext x; simp
  refine Measure.ext_of_Ico' _ _ (fun a b hab => ?_) (fun a b hab => ?_)
  · refine ne_top_of_le_ne_top (hfin b) ?_
    rw [← hL b]
    exact measure_mono Ico_subset_Iio_self
  · have hsub : Iio a ⊆ Iio b := Iio_subset_Iio hab.le
    rw [hIco a b hab,
      measure_sdiff hsub measurableSet_Iio.nullMeasurableSet (by rw [hL]; exact hfin a),
      measure_sdiff hsub measurableSet_Iio.nullMeasurableSet (by rw [hR]; exact hfin a),
      hL, hL, hR, hR]

/-- The radial law (proof of `L:phase-contractions`, main TeX lines 2110-2117),
general form: for a locally finite measure `ν` on `ℝ^d` with
`ν(cA) = c^β ν(A)` (`β > 0`) and measurable `f ≥ 0`,
`∫ f(|y|) ν(dy) = β ν(B_1) ∫_0^∞ f(r) r^{β-1} dr`.  For `Γ`, `β = 3 - α`
and `ν(B_r) = M r^{3-α}`; for Lebesgue measure on `ℝ³`, `β = 3`. -/
theorem lintegral_norm_radial {d : ℕ} (ν : Measure (Rd d)) [IsLocallyFiniteMeasure ν]
    {β : ℝ} (hβ : 0 < β) (hs : SpectralHomogeneous ν β) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f ‖y‖ ∂ν = ENNReal.ofReal β * ν (ball (0 : Rd d) 1) *
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (β - 1)) * f r := by
  rw [← lintegral_map hf measurable_norm, map_norm_eq ν hβ hs, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf, smul_eq_mul]
  rfl

/-- No origin atom (main TeX lines 2089-2090 for `μ`: "there is no origin
atom"; for `Γ` it is implicit in the radial distribution step, lines
2110-2111): a locally finite measure with
`ν(cA) = c^β ν(A)`, `β > 0`, has no atom at the origin
(`SpectralHomog.measure_zero`, restated for the section). -/
theorem measure_singleton_zero {d : ℕ} (ν : Measure (Rd d)) [IsLocallyFiniteMeasure ν]
    {β : ℝ} (hβ : 0 < β) (hs : SpectralHomogeneous ν β) : ν {0} = 0 :=
  SpectralHomog.measure_zero hs hβ

/-- Auxiliary to the Lean proof route: Lebesgue measure on `ℝ³` scales with
degree `3`. -/
theorem volume_homogeneous : SpectralHomogeneous (volume : Measure (Rd 3)) 3 := by
  intro A _ c hc
  rw [Measure.addHaar_smul, finrank_euclideanSpace, Fintype.card_fin,
    abs_of_pos (by positivity)]
  norm_cast

/-! ### The Gaussian density -/

/-- Auxiliary to the Lean proof route: the profile
`u ↦ (2πv)^{-d/2} e^{-u/(2v)}` of the Gaussian density. -/
def pprof (d : ℕ) (v u : ℝ) : ℝ := (2 * π * v) ^ (-((d : ℝ) / 2)) * Real.exp (-(u / (2 * v)))

/-- The Brownian Gaussian density `p_v(x) = (2πv)^{-d/2} e^{-|x|²/(2v)}` with
covariance `v I` (main TeX lines 2068-2069); `p_{2ε}` is `pdens (2ε)`. -/
def pdens {d : ℕ} (v : ℝ) (x : Rd d) : ℝ := pprof d v (‖x‖ ^ 2)

/-- Auxiliary to the Lean proof route. -/
theorem pprof_nonneg (d : ℕ) (v u : ℝ) (hv : 0 < v) : 0 ≤ pprof d v u := by
  unfold pprof; positivity

/-- Auxiliary to the Lean proof route. -/
theorem continuous_pprof (d : ℕ) (v : ℝ) : Continuous (pprof d v) := by
  unfold pprof; fun_prop

/-- Auxiliary to the Lean proof route. -/
theorem continuous_pdens {d : ℕ} (v : ℝ) : Continuous (pdens (d := d) v) := by
  unfold pdens; exact (continuous_pprof d v).comp (by fun_prop)

/-- `p_v` is a probability density for `v > 0`: integrable with
`∫ p_v = 1`. -/
theorem integral_pdens {d : ℕ} (v : ℝ) (hv : 0 < v) :
    Integrable (pdens (d := d) v) ∧ ∫ x, pdens (d := d) v x = 1 := by
  have hb : 0 < 1 / (2 * v) := by positivity
  have hG := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Rd d) hb
  rw [finrank_euclideanSpace, Fintype.card_fin] at hG
  have hpt : ∀ x : Rd d, pdens v x =
      (2 * π * v) ^ (-((d : ℝ) / 2)) * Real.exp (-(1 / (2 * v)) * ‖x‖ ^ 2) := by
    intro x; unfold pdens pprof; congr 2; ring
  have hval : ∫ x, pdens (d := d) v x = 1 := by
    simp_rw [hpt]
    rw [integral_const_mul, hG, show π / (1 / (2 * v)) = 2 * π * v by field_simp,
      Real.rpow_neg (by positivity), inv_mul_cancel₀ (by positivity)]
  exact ⟨Integrable.of_integral_ne_zero (by rw [hval]; norm_num), hval⟩

/-- Auxiliary to the Lean proof route: `∫ p_v = 1` as a lower integral. -/
theorem lintegral_pdens {d : ℕ} (v : ℝ) (hv : 0 < v) :
    ∫⁻ x, ENNReal.ofReal (pdens (d := d) v x) = 1 := by
  obtain ⟨hi, hval⟩ := integral_pdens (d := d) v hv
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x => pprof_nonneg d v _ hv), hval, ENNReal.ofReal_one]

/-! ### Supplied inputs from wave item L9-G and the sphere formula -/

/-- Supplied input (the d = 3 wave Green Fourier identity, being proved by
wave item L9-G): for `s > 0` and `ξ ∈ ℝ³`,
`∫ e^{iξ·x} G_s(dx) = sin(s|ξ|)/|ξ|` (value `s` at `ξ = 0`), i.e.
`WaveKernel.waveHat s ξ`, for `G_s = WaveGreen.waveGreen 3 s`.  The TeX uses it
in the Fourier form of `T_ε` (main TeX lines 2081-2084 and 2107-2108, "`Ĝ_a`"); its source is the
Fourier formula `Ĝ_s(ξ) = sin(s|ξ|)/|ξ|` of main TeX lines 777-778. -/
def WaveFourierThree : Prop :=
  ∀ s : ℝ, 0 < s → ∀ ξ : Rd 3,
    ∫ x, Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) ∂(waveGreen 3 s) = (waveHat s ξ : ℂ)

/-- Supplied input (Archimedes' law, being proved by wave item L9-G): for every
unit vector `e ∈ ℝ³`, the image of the unit-sphere measure
`volume.toSphere` (the measure used by `WaveGreen.waveGreen 3`) under
`ω ↦ ⟨e, ω⟩` is `2π` times Lebesgue measure on `[-1, 1]`.  The TeX uses it as
"direct integration over its normal coordinate" (main TeX lines 2125-2126). -/
def ArchimedesLaw : Prop :=
  ∀ e : Rd 3, ‖e‖ = 1 →
    (volume : Measure (Rd 3)).toSphere.map (fun ω : sphere (0 : Rd 3) 1 => inner ℝ e (ω : Rd 3)) =
      ENNReal.ofReal (2 * π) • volume.restrict (Icc (-1 : ℝ) 1)

/-- Integration against the spherical wave measure through its normal
coordinate (the "direct integration over its normal coordinate" of main TeX
lines 2125-2126), from Archimedes' law: for `a > 0`, `y ∈ ℝ³` and measurable
`φ ≥ 0`,
`∫ φ(|y-x|²) G_a(dx) = (a/2) ∫_{-1}^{1} φ(|y|² + a² - 2a|y|t) dt`.
In particular `x ↦ ∫ φ(|x-w|²) G_a(dw)` is radial. -/
theorem lintegral_waveGreen_three (hA : ArchimedesLaw) (a : ℝ) (ha : 0 < a)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (y : Rd 3) :
    ∫⁻ x, φ (‖y - x‖ ^ 2) ∂(waveGreen 3 a) =
      ENNReal.ofReal (a / 2) * ∫⁻ t in Icc (-1 : ℝ) 1, φ (‖y‖ ^ 2 + a ^ 2 - 2 * a * ‖y‖ * t) := by
  obtain ⟨e, he, hye⟩ : ∃ e : Rd 3, ‖e‖ = 1 ∧ ∀ ω : Rd 3, inner ℝ y ω = ‖y‖ * inner ℝ e ω := by
    by_cases hy : y = 0
    · obtain ⟨e, he⟩ := exists_norm_eq (Rd 3) zero_le_one
      exact ⟨e, he, fun ω => by simp [hy]⟩
    · have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
      refine ⟨‖y‖⁻¹ • y, ?_, fun ω => ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
      · rw [real_inner_smul_left, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  set g : ℝ → ℝ≥0∞ := fun t => φ (‖y‖ ^ 2 + a ^ 2 - 2 * a * ‖y‖ * t) with hg_def
  have hgm : Measurable g := hφ.comp (by fun_prop)
  have hpt : ∀ ω : sphere (0 : Rd 3) 1,
      φ (‖y - a • (ω : Rd 3)‖ ^ 2) = g (inner ℝ e (ω : Rd 3)) := by
    intro ω
    have hω : ‖(ω : Rd 3)‖ = 1 := mem_sphere_zero_iff_norm.1 ω.2
    simp only [hg_def]
    congr 1
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg ha.le, hω, hye]
    ring
  have hinner : Measurable fun ω : sphere (0 : Rd 3) 1 => inner ℝ e (ω : Rd 3) :=
    (continuous_const.inner continuous_subtype_val).measurable
  simp only [waveGreen]
  rw [lintegral_smul_measure, lintegral_map (f := fun x : Rd 3 => φ (‖y - x‖ ^ 2))
    (hφ.comp (by fun_prop : Measurable fun x : Rd 3 => ‖y - x‖ ^ 2)) (by fun_prop)]
  rw [lintegral_congr hpt, ← lintegral_map hgm hinner, hA e he, lintegral_smul_measure,
    smul_eq_mul, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  field_simp
  ring

/-! ### The sphere convolution formula and the three-region bound -/

/-- Auxiliary to the Lean proof route: `(|v|²)^{-α/2} = |v|^{-α}`. -/
theorem sq_norm_rpow (v : Rd 3) (alpha : ℝ) :
    (‖v‖ ^ 2) ^ (-alpha / 2) = ‖v‖ ^ (-alpha) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast
  ring

/-- Auxiliary to the Lean proof route: `(x²)^{p} = |x|^{2p}`. -/
theorem sq_rpow_eq_abs (x p : ℝ) : (x ^ 2) ^ p = |x| ^ (2 * p) := by
  rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
  norm_cast

/-- The one-dimensional integral behind the sphere convolution formula (main
TeX lines 2125-2131): for `a, r > 0` and `α < 2`,
`∫_{-1}^{1} (r² + a² - 2art)^{-α/2} dt = ((a+r)^{2-α} - |a-r|^{2-α})/(ar(2-α))`
with integrability (the integrand is singular at `t = 1` when `r = a`). -/
theorem integral_normal_coordinate (a r alpha : ℝ) (ha : 0 < a) (hr : 0 < r)
    (ha2 : alpha < 2) :
    IntervalIntegrable (fun t : ℝ => (r ^ 2 + a ^ 2 - 2 * a * r * t) ^ (-alpha / 2)) volume (-1) 1 ∧
      ∫ t in (-1 : ℝ)..1, (r ^ 2 + a ^ 2 - 2 * a * r * t) ^ (-alpha / 2) =
        ((a + r) ^ (2 - alpha) - |a - r| ^ (2 - alpha)) / (a * r * (2 - alpha)) := by
  set u : ℝ → ℝ := fun t => r ^ 2 + a ^ 2 - 2 * a * r * t with hu_def
  have har : 0 < a * r := mul_pos ha hr
  have h2a : 0 < 2 - alpha := by linarith
  have hk : 0 < a * r * (2 - alpha) := by positivity
  set g : ℝ → ℝ := fun t => -(u t ^ (1 - alpha / 2)) / (a * r * (2 - alpha)) with hg_def
  have hu_pos : ∀ t ∈ Ioo (-1 : ℝ) 1, 0 < u t := by
    intro t ht
    simp only [hu_def]
    nlinarith [sq_nonneg (a - r), ht.2]
  have hu_nn : ∀ t ∈ Icc (-1 : ℝ) 1, 0 ≤ u t := by
    intro t ht
    simp only [hu_def]
    nlinarith [sq_nonneg (a - r), ht.2]
  have hcont : ContinuousOn g (Icc (-1) 1) := by
    simp only [hg_def]
    refine ((ContinuousOn.rpow_const (by fun_prop) fun t _ => Or.inr (by linarith)).neg).div_const _
  have hderiv : ∀ t ∈ Ioo (-1 : ℝ) 1, HasDerivAt g (u t ^ (-alpha / 2)) t := by
    intro t ht
    have hu' : HasDerivAt u (-(2 * a * r)) t := by
      have := ((hasDerivAt_id t).const_mul (2 * a * r)).const_sub (r ^ 2 + a ^ 2)
      simpa [hu_def] using this
    have hd := ((hu'.rpow_const (p := 1 - alpha / 2) (Or.inl (hu_pos t ht).ne')).neg).div_const
      (a * r * (2 - alpha))
    rw [show (1 : ℝ) - alpha / 2 - 1 = -alpha / 2 by ring] at hd
    convert hd using 1
    field_simp
  have hint : IntervalIntegrable (fun t => u t ^ (-alpha / 2)) volume (-1) 1 := by
    refine intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := g) ?_ ?_ ?_
    · rwa [uIcc_of_le (by norm_num)]
    · intro t ht
      rw [min_eq_left (by norm_num), max_eq_right (by norm_num)] at ht
      exact hderiv t ht
    · intro t ht
      rw [min_eq_left (by norm_num), max_eq_right (by norm_num)] at ht
      exact Real.rpow_nonneg (hu_pos t ht).le _
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hderiv hint]
  have h1 : u 1 = (a - r) ^ 2 := by simp only [hu_def]; ring
  have h2 : u (-1) = (a + r) ^ 2 := by simp only [hu_def]; ring
  simp only [hg_def, h1, h2, sq_rpow_eq_abs, abs_of_pos (by linarith : 0 < a + r)]
  rw [show 2 * (1 - alpha / 2) = 2 - alpha by ring]
  field_simp
  ring

/-- **The sphere convolution formula** (main TeX lines 2125-2131): for
`a > 0`, `α < 2` (the TeX has `0 < α < 2`) and `z ∈ ℝ³` with `r = |z| > 0`,
`(G_a * |·|^{-α})(z) = ∫ |z-x|^{-α} G_a(dx) = ((a+r)^{2-α} - |a-r|^{2-α})/(2r(2-α))`,
as a lower integral (so in particular finite), given Archimedes' law. -/
theorem sphere_convolution (hA : ArchimedesLaw) (a : ℝ) (ha : 0 < a) (alpha : ℝ)
    (ha2 : alpha < 2) (z : Rd 3) (hz : 0 < ‖z‖) :
    ∫⁻ x, ENNReal.ofReal (‖z - x‖ ^ (-alpha)) ∂(waveGreen 3 a) =
      ENNReal.ofReal (((a + ‖z‖) ^ (2 - alpha) - |a - ‖z‖| ^ (2 - alpha)) /
        (2 * ‖z‖ * (2 - alpha))) := by
  set r := ‖z‖ with hr_def
  set φ : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (u ^ (-alpha / 2)) with hφ_def
  have hφm : Measurable φ := by simp only [hφ_def]; fun_prop
  have hpt : ∀ x : Rd 3, ENNReal.ofReal (‖z - x‖ ^ (-alpha)) = φ (‖z - x‖ ^ 2) := by
    intro x; simp only [hφ_def, sq_norm_rpow]
  simp_rw [hpt]
  rw [lintegral_waveGreen_three hA a ha φ hφm z]
  obtain ⟨hII, hval⟩ := integral_normal_coordinate a r alpha ha hz ha2
  have hIcc : IntegrableOn (fun t : ℝ => (r ^ 2 + a ^ 2 - 2 * a * r * t) ^ (-alpha / 2))
      (Icc (-1) 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hII.1
  have hnn : 0 ≤ᵐ[volume.restrict (Icc (-1 : ℝ) 1)]
      fun t : ℝ => (r ^ 2 + a ^ 2 - 2 * a * r * t) ^ (-alpha / 2) :=
    (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht =>
      Real.rpow_nonneg (by nlinarith [sq_nonneg (a - r), ht.2, mul_pos ha hz]) _)
  simp only [hφ_def]
  rw [← ofReal_integral_eq_lintegral_ofReal hIcc hnn, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num), hval, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : 0 < 2 - alpha := by linarith
  field_simp

/-- Auxiliary to the Lean proof route: if every point of the sphere of
radius `a` is at distance at least `δ > 0` from `z` (`δ ≤ |a - |z||`), then
`(G_a * |·|^{-α})(z) ≤ a δ^{-α}` (mass `a` times the largest value). -/
theorem kernel_le_of_dist (hA : ArchimedesLaw) (a : ℝ) (ha : 0 < a) (alpha : ℝ)
    (ha0 : 0 ≤ alpha) (z : Rd 3) (δ : ℝ) (hδ : 0 < δ) (hδz : δ ≤ |a - ‖z‖|) :
    ∫⁻ x, ENNReal.ofReal (‖z - x‖ ^ (-alpha)) ∂(waveGreen 3 a) ≤
      ENNReal.ofReal (a * δ ^ (-alpha)) := by
  set r := ‖z‖ with hr_def
  set φ : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (u ^ (-alpha / 2)) with hφ_def
  have hφm : Measurable φ := by simp only [hφ_def]; fun_prop
  have hpt : ∀ x : Rd 3, ENNReal.ofReal (‖z - x‖ ^ (-alpha)) = φ (‖z - x‖ ^ 2) := by
    intro x; simp only [hφ_def, sq_norm_rpow]
  simp_rw [hpt]
  rw [lintegral_waveGreen_three hA a ha φ hφm z]
  have hr0 : 0 ≤ r := norm_nonneg z
  have hδ2 : δ ^ 2 ≤ (a - r) ^ 2 := by
    rw [← sq_abs (a - r)]; exact pow_le_pow_left₀ hδ.le hδz 2
  have hbd : ∀ t ∈ Icc (-1 : ℝ) 1,
      φ (r ^ 2 + a ^ 2 - 2 * a * r * t) ≤ ENNReal.ofReal (δ ^ (-alpha)) := by
    intro t ht
    simp only [hφ_def]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle : δ ^ 2 ≤ r ^ 2 + a ^ 2 - 2 * a * r * t := by
      nlinarith [mul_nonneg ha.le hr0, ht.2]
    calc (r ^ 2 + a ^ 2 - 2 * a * r * t) ^ (-alpha / 2) ≤ (δ ^ 2) ^ (-alpha / 2) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
      _ = δ ^ (-alpha) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]; congr 1; push_cast; ring
  calc ENNReal.ofReal (a / 2) * ∫⁻ t in Icc (-1 : ℝ) 1, φ (r ^ 2 + a ^ 2 - 2 * a * r * t)
      ≤ ENNReal.ofReal (a / 2) * ∫⁻ _ in Icc (-1 : ℝ) 1, ENNReal.ofReal (δ ^ (-alpha)) := by
        exact mul_le_mul_of_nonneg_left (setLIntegral_mono' measurableSet_Icc hbd) zero_le
    _ = ENNReal.ofReal (a * δ ^ (-alpha)) := by
        rw [setLIntegral_const, Real.volume_Icc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- Auxiliary to the Lean proof route: `a · a^{-α} = a^{1-α}`. -/
theorem mul_rpow_neg (a alpha : ℝ) (ha : 0 < a) : a * a ^ (-alpha) = a ^ (1 - alpha) := by
  rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]

/-- The middle region of the three-region bound (main TeX lines 2134-2135),
a real inequality: for `a > 0`, `α < 2` and `a/2 ≤ r ≤ 2a`,
`((a+r)^{2-α} - |a-r|^{2-α})/(2r(2-α)) ≤ 3^{2-α} a^{1-α}/(2-α)`. -/
theorem middle_region_le (a r alpha : ℝ) (ha : 0 < a) (ha2 : alpha < 2) (hz1 : a / 2 ≤ r)
    (hz2 : r ≤ 2 * a) :
    ((a + r) ^ (2 - alpha) - |a - r| ^ (2 - alpha)) / (2 * r * (2 - alpha)) ≤
      3 ^ (2 - alpha) * a ^ (1 - alpha) / (2 - alpha) := by
  have hz : 0 < r := by linarith
  have h2a : 0 < 2 - alpha := by linarith
  have hX0 : 0 ≤ (a + r) ^ (2 - alpha) - |a - r| ^ (2 - alpha) := by
    have : |a - r| ≤ a + r := by
      rw [abs_le]; constructor <;> linarith
    linarith [Real.rpow_le_rpow (abs_nonneg _) this h2a.le]
  have hX : (a + r) ^ (2 - alpha) - |a - r| ^ (2 - alpha) ≤ 3 ^ (2 - alpha) * a ^ (2 - alpha) := by
    have h1 : (a + r) ^ (2 - alpha) ≤ (3 * a) ^ (2 - alpha) :=
      Real.rpow_le_rpow (by linarith) (by linarith) h2a.le
    rw [Real.mul_rpow (by norm_num) ha.le] at h1
    linarith [Real.rpow_nonneg (abs_nonneg (a - r)) (2 - alpha)]
  calc ((a + r) ^ (2 - alpha) - |a - r| ^ (2 - alpha)) / (2 * r * (2 - alpha))
      ≤ ((a + r) ^ (2 - alpha) - |a - r| ^ (2 - alpha)) / (a * (2 - alpha)) :=
        div_le_div_of_nonneg_left hX0 (by positivity) (by nlinarith)
    _ ≤ (3 ^ (2 - alpha) * a ^ (2 - alpha)) / (a * (2 - alpha)) :=
        div_le_div_of_nonneg_right hX (by positivity)
    _ = 3 ^ (2 - alpha) * a ^ (1 - alpha) / (2 - alpha) := by
        have hpow : a ^ (2 - alpha) = a ^ (1 - alpha) * a := by
          rw [show (2 : ℝ) - alpha = (1 - alpha) + 1 by ring, Real.rpow_add ha, Real.rpow_one]
        rw [hpow]
        field_simp

/-- **The three-region bound** (main TeX lines 2132-2136) for
`(G_a * |·|^{-α})(z) = ∫ |z-x|^{-α} G_a(dx)`, `a > 0`, `0 < α < 2`, `r = |z|`:
for `r ≤ a/2` it is at most `2^α a^{1-α}`; for `r ≥ 2a` at most `a^{1-α}`;
for `a/2 ≤ r ≤ 2a` at most `3^{2-α} a^{1-α}/(2-α)`.  The regions are closed
here (the TeX takes the outer ones open and covers the endpoints by
continuity). -/
theorem three_regions (hA : ArchimedesLaw) (a : ℝ) (ha : 0 < a) (alpha : ℝ) (ha0 : 0 < alpha)
    (ha2 : alpha < 2) (z : Rd 3) :
    (‖z‖ ≤ a / 2 → ∫⁻ x, ENNReal.ofReal (‖z - x‖ ^ (-alpha)) ∂(waveGreen 3 a) ≤
        ENNReal.ofReal (2 ^ alpha * a ^ (1 - alpha))) ∧
      (2 * a ≤ ‖z‖ → ∫⁻ x, ENNReal.ofReal (‖z - x‖ ^ (-alpha)) ∂(waveGreen 3 a) ≤
        ENNReal.ofReal (a ^ (1 - alpha))) ∧
      (a / 2 ≤ ‖z‖ → ‖z‖ ≤ 2 * a →
        ∫⁻ x, ENNReal.ofReal (‖z - x‖ ^ (-alpha)) ∂(waveGreen 3 a) ≤
          ENNReal.ofReal (3 ^ (2 - alpha) * a ^ (1 - alpha) / (2 - alpha))) := by
  refine ⟨fun hz => ?_, fun hz => ?_, fun hz1 hz2 => ?_⟩
  · refine (kernel_le_of_dist hA a ha alpha ha0.le z (a / 2) (by positivity) ?_).trans
      (le_of_eq ?_)
    · rw [abs_of_nonneg (by linarith)]; linarith
    · congr 1
      rw [Real.div_rpow ha.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul, ← mul_rpow_neg a alpha ha]
      ring
  · refine (kernel_le_of_dist hA a ha alpha ha0.le z a ha ?_).trans
      (le_of_eq (by rw [mul_rpow_neg a alpha ha]))
    rw [abs_of_nonpos (by linarith)]; linarith
  · have hz : 0 < ‖z‖ := by linarith
    rw [sphere_convolution hA a ha alpha ha2 z hz]
    exact ENNReal.ofReal_le_ofReal (middle_region_le a ‖z‖ alpha ha ha2 hz1 hz2)

/-- `sup_z (G_a * |·|^{-α})(z) ≤ b_α a^{1-α}` (main TeX lines 2123 and 2132-2136): the
maximum of the three regional bounds is at most `b_α = 2^α + 3^{2-α}/(2-α)`. -/
theorem kernel_le_bAlpha (hA : ArchimedesLaw) (a : ℝ) (ha : 0 < a) (alpha : ℝ) (ha0 : 0 < alpha)
    (ha2 : alpha < 2) (z : Rd 3) :
    ∫⁻ x, ENNReal.ofReal (‖z - x‖ ^ (-alpha)) ∂(waveGreen 3 a) ≤
      ENNReal.ofReal (bAlpha alpha * a ^ (1 - alpha)) := by
  obtain ⟨h1, h2, h3⟩ := three_regions hA a ha alpha ha0 ha2 z
  have hp : 0 < a ^ (1 - alpha) := Real.rpow_pos_of_pos ha _
  have h2a : 0 < 2 - alpha := by linarith
  have hq : 0 ≤ 3 ^ (2 - alpha) / (2 - alpha) := by positivity
  have h2p : 1 ≤ (2 : ℝ) ^ alpha := Real.one_le_rpow (by norm_num) ha0.le
  have hb2 : 2 ^ alpha * a ^ (1 - alpha) ≤ bAlpha alpha * a ^ (1 - alpha) := by
    unfold bAlpha; nlinarith
  rcases le_or_gt ‖z‖ (a / 2) with hz | hz
  · exact (h1 hz).trans (ENNReal.ofReal_le_ofReal hb2)
  rcases le_or_gt (2 * a) ‖z‖ with hz' | hz'
  · exact (h2 hz').trans (ENNReal.ofReal_le_ofReal (by nlinarith))
  · refine (h3 hz.le hz'.le).trans (ENNReal.ofReal_le_ofReal ?_)
    unfold bAlpha
    have : 3 ^ (2 - alpha) * a ^ (1 - alpha) / (2 - alpha) =
        3 ^ (2 - alpha) / (2 - alpha) * a ^ (1 - alpha) := by ring
    rw [this]
    nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) alpha]

/-! ### `Γ_ε`, `T_ε` and `E:phase-trace` -/

/-- `Γ_ε = p_{2ε} * Γ` (main TeX lines 2069-2070): `Γ_ε(x) = ∫ p_{2ε}(x-y) Γ(dy)`. -/
def gammaEps {d : ℕ} (Γ : Measure (Rd d)) (ε : ℝ) (x : Rd d) : ℝ :=
  ∫ y, pdens (2 * ε) (x - y) ∂Γ

/-- `T_ε(a,q) = ∫ e^{iq·x} Γ_ε(x) G_a(dx)` (main TeX lines 2081-2082), with
`G_a = WaveGreen.waveGreen 3 a`. -/
def traceT (Γ : Measure (Rd 3)) (ε a : ℝ) (q : Rd 3) : ℂ :=
  ∫ x, Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)) * (gammaEps Γ ε x : ℂ) ∂(waveGreen 3 a)

/-- Auxiliary to the Lean proof route: `y ↦ p_v(x-y)` is integrable against a
tempered measure (`v > 0`). -/
theorem integrable_pdens_sub {d : ℕ} {Γ : Measure (Rd d)} (hΓt : IsTempered Γ) (v : ℝ)
    (hv : 0 < v) (x : Rd d) : Integrable (fun y => pdens v (x - y)) Γ := by
  have hb : 0 < 1 / (2 * v) := by positivity
  refine ((integrable_gauss_of_tempered hΓt hb x).const_mul ((2 * π * v) ^ (-((d : ℝ) / 2)))).congr
    (Eventually.of_forall fun y => ?_)
  simp only [pdens, pprof, norm_sub_rev x y]
  congr 2
  ring

/-- Auxiliary to the Lean proof route: `Γ_ε(x)` as a lower integral. -/
theorem ofReal_gammaEps {d : ℕ} {Γ : Measure (Rd d)} (hΓt : IsTempered Γ) (ε : ℝ) (hε : 0 < ε)
    (x : Rd d) :
    ENNReal.ofReal (gammaEps Γ ε x) = ∫⁻ y, ENNReal.ofReal (pdens (2 * ε) (x - y)) ∂Γ :=
  ofReal_integral_eq_lintegral_ofReal (integrable_pdens_sub hΓt _ (by positivity) x)
    (Eventually.of_forall fun _ => pprof_nonneg _ _ _ (by positivity))

/-- `Γ_ε ≥ 0`. -/
theorem gammaEps_nonneg {d : ℕ} (Γ : Measure (Rd d)) (ε : ℝ) (hε : 0 < ε) (x : Rd d) :
    0 ≤ gammaEps Γ ε x :=
  integral_nonneg fun _ => pprof_nonneg _ _ _ (by positivity)

/-- Auxiliary to the Lean proof route: `Γ_ε` is measurable (`Γ` s-finite). -/
theorem measurable_gammaEps {d : ℕ} (Γ : Measure (Rd d)) [SFinite Γ] (ε : ℝ) :
    Measurable (gammaEps Γ ε) := by
  have hc : Continuous fun p : Rd d × Rd d => pdens (2 * ε) (p.1 - p.2) :=
    (continuous_pdens _).comp (continuous_fst.sub continuous_snd)
  exact (hc.stronglyMeasurable.integral_prod_right' (ν := Γ)).measurable

/-- The main estimate of `E:phase-trace` (main TeX lines 2108-2136), as a lower
integral: for a locally finite tempered `Γ` on `ℝ³` with
`Γ(cA) = c^{3-α}Γ(A)`, `0 < α < 2`, `ε, a > 0`, and Archimedes' law,
`∫ Γ_ε dG_a ≤ D_Γ a^{1-α}`.  Route as in the TeX: nonnegative Fubini, the
radial law for `Γ` and for Lebesgue measure (`lintegral_norm_radial`, with the
radial form of `G_a * p_{2ε}` from `lintegral_waveGreen_three`), a second
nonnegative Fubini, and `sup (G_a * |·|^{-α}) ≤ b_α a^{1-α}`. -/
theorem lintegral_gammaEps_le (hA : ArchimedesLaw) {Γ : Measure (Rd 3)} [IsLocallyFiniteMeasure Γ]
    (hΓt : IsTempered Γ) {alpha : ℝ} (hΓs : SpectralHomogeneous Γ (3 - alpha))
    (ha0 : 0 < alpha) (ha2 : alpha < 2) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 < a) :
    ∫⁻ x, ENNReal.ofReal (gammaEps Γ ε x) ∂(waveGreen 3 a) ≤
      ENNReal.ofReal (dGam Γ alpha * a ^ (1 - alpha)) := by
  set v := 2 * ε with hv_def
  have hv : 0 < v := by positivity
  set G := waveGreen 3 a
  set φ : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (pprof 3 v u) with hφ_def
  have hφm : Measurable φ := by
    simp only [hφ_def]; exact ENNReal.measurable_ofReal.comp (continuous_pprof 3 v).measurable
  set Φ : ℝ → ℝ≥0∞ := fun ρ =>
    ENNReal.ofReal (a / 2) * ∫⁻ t in Icc (-1 : ℝ) 1, φ (ρ ^ 2 + a ^ 2 - 2 * a * ρ * t) with hΦ_def
  have hΦm : Measurable Φ := by
    simp only [hΦ_def]
    refine Measurable.const_mul ?_ _
    exact Measurable.lintegral_prod_right'
      (f := fun p : ℝ × ℝ => φ (p.1 ^ 2 + a ^ 2 - 2 * a * p.1 * p.2)) (hφm.comp (by fun_prop))
  have hpm : Measurable fun p : Rd 3 × Rd 3 => ENNReal.ofReal (pdens v (p.1 - p.2)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_pdens v).comp (continuous_fst.sub continuous_snd)).measurable
  -- `G_a * p_v` is radial
  have hF : ∀ y : Rd 3, ∫⁻ x, ENNReal.ofReal (pdens v (x - y)) ∂G = Φ ‖y‖ := by
    intro y
    have hpt : ∀ x : Rd 3, ENNReal.ofReal (pdens v (x - y)) = φ (‖y - x‖ ^ 2) := by
      intro x; simp only [hφ_def, pdens, norm_sub_rev x y]
    simp_rw [hpt]
    exact lintegral_waveGreen_three hA a ha φ hφm y
  -- step 1: Fubini
  have h1 : ∫⁻ x, ENNReal.ofReal (gammaEps Γ ε x) ∂G = ∫⁻ y, Φ ‖y‖ ∂Γ := by
    simp_rw [ofReal_gammaEps hΓt ε hε]
    rw [lintegral_lintegral_swap hpm.aemeasurable]
    exact lintegral_congr hF
  -- step 2: the radial law for `Γ`
  have h2 := lintegral_norm_radial Γ (β := 3 - alpha) (by linarith) hΓs Φ hΦm
  -- step 3: the radial law for Lebesgue measure
  have h3 : ∫⁻ x, Φ ‖x‖ * ENNReal.ofReal (‖x‖ ^ (-alpha)) ∂(volume : Measure (Rd 3)) =
      ENNReal.ofReal (4 * π) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (3 - alpha - 1)) * Φ r := by
    have h := lintegral_norm_radial (volume : Measure (Rd 3)) (β := 3) (by norm_num)
      volume_homogeneous (fun r => Φ r * ENNReal.ofReal (r ^ (-alpha)))
      (hΦm.mul (ENNReal.measurable_ofReal.comp (by fun_prop)))
    rw [h, EuclideanSpace.volume_ball_fin_three]
    have hc : ENNReal.ofReal 3 * (ENNReal.ofReal 1 ^ 3 * ENNReal.ofReal (π * 4 / 3)) =
        ENNReal.ofReal (4 * π) := by
      rw [ENNReal.ofReal_one, one_pow, one_mul, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1; ring
    rw [hc]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr0 : 0 < r := hr
    rw [mul_comm (Φ r), ← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hr0.le _),
      ← Real.rpow_add hr0]
    congr 3
    ring
  -- step 4: the second Fubini and the supremum bound
  have hK : ∀ z : Rd 3, ∫⁻ w, ENNReal.ofReal (‖z + w‖ ^ (-alpha)) ∂G ≤
      ENNReal.ofReal (bAlpha alpha * a ^ (1 - alpha)) := by
    intro z
    have hz := kernel_le_bAlpha hA a ha alpha ha0 ha2 (-z)
    refine le_of_eq_of_le (lintegral_congr fun w => ?_) hz
    rw [show z + w = -(-z - w) by abel, norm_neg]
  have hm2 : Measurable fun p : Rd 3 × Rd 3 =>
      ENNReal.ofReal (pdens v (p.2 - p.1)) * ENNReal.ofReal (‖p.1‖ ^ (-alpha)) :=
    (ENNReal.measurable_ofReal.comp
      ((continuous_pdens v).comp (continuous_snd.sub continuous_fst)).measurable).mul
      (ENNReal.measurable_ofReal.comp (by fun_prop))
  have hm3 : Measurable fun p : Rd 3 × Rd 3 =>
      ENNReal.ofReal (pdens v p.2) * ENNReal.ofReal (‖p.2 + p.1‖ ^ (-alpha)) :=
    (ENNReal.measurable_ofReal.comp ((continuous_pdens v).comp continuous_snd).measurable).mul
      (ENNReal.measurable_ofReal.comp (by fun_prop))
  have h4 : ∫⁻ x, Φ ‖x‖ * ENNReal.ofReal (‖x‖ ^ (-alpha)) ∂(volume : Measure (Rd 3)) ≤
      ENNReal.ofReal (bAlpha alpha * a ^ (1 - alpha)) := by
    calc ∫⁻ x, Φ ‖x‖ * ENNReal.ofReal (‖x‖ ^ (-alpha)) ∂(volume : Measure (Rd 3))
        = ∫⁻ x, (∫⁻ w, ENNReal.ofReal (pdens v (w - x)) ∂G) *
            ENNReal.ofReal (‖x‖ ^ (-alpha)) ∂(volume : Measure (Rd 3)) := by
          refine lintegral_congr fun x => ?_
          rw [hF x]
      _ = ∫⁻ x, ∫⁻ w, ENNReal.ofReal (pdens v (w - x)) * ENNReal.ofReal (‖x‖ ^ (-alpha)) ∂G
            ∂(volume : Measure (Rd 3)) := by
          refine lintegral_congr fun x => (lintegral_mul_const _ ?_).symm
          exact ENNReal.measurable_ofReal.comp
            ((continuous_pdens v).comp (continuous_id.sub continuous_const)).measurable
      _ = ∫⁻ w, ∫⁻ x, ENNReal.ofReal (pdens v (w - x)) * ENNReal.ofReal (‖x‖ ^ (-alpha))
            ∂(volume : Measure (Rd 3)) ∂G :=
          lintegral_lintegral_swap hm2.aemeasurable
      _ = ∫⁻ w, ∫⁻ z, ENNReal.ofReal (pdens v z) * ENNReal.ofReal (‖z + w‖ ^ (-alpha))
            ∂(volume : Measure (Rd 3)) ∂G := by
          refine lintegral_congr fun w => ?_
          rw [← lintegral_sub_right_eq_self
            (fun z => ENNReal.ofReal (pdens v z) * ENNReal.ofReal (‖z + w‖ ^ (-alpha))) w]
          refine lintegral_congr fun x => ?_
          simp only [sub_add_cancel, pdens, norm_sub_rev w x]
      _ = ∫⁻ z, ∫⁻ w, ENNReal.ofReal (pdens v z) * ENNReal.ofReal (‖z + w‖ ^ (-alpha)) ∂G
            ∂(volume : Measure (Rd 3)) :=
          lintegral_lintegral_swap hm3.aemeasurable
      _ = ∫⁻ z, ENNReal.ofReal (pdens v z) * ∫⁻ w, ENNReal.ofReal (‖z + w‖ ^ (-alpha)) ∂G
            ∂(volume : Measure (Rd 3)) := by
          refine lintegral_congr fun z => lintegral_const_mul _ ?_
          exact ENNReal.measurable_ofReal.comp (by fun_prop)
      _ ≤ ∫⁻ z, ENNReal.ofReal (pdens v z) * ENNReal.ofReal (bAlpha alpha * a ^ (1 - alpha))
            ∂(volume : Measure (Rd 3)) :=
          lintegral_mono fun z => mul_le_mul_of_nonneg_left (hK z) zero_le
      _ = ENNReal.ofReal (bAlpha alpha * a ^ (1 - alpha)) := by
          rw [lintegral_mul_const (f := fun z => ENNReal.ofReal (pdens v z)) _
              (ENNReal.measurable_ofReal.comp (continuous_pdens v).measurable),
            lintegral_pdens v hv, one_mul]
  -- step 5: constants
  have hM : Γ (ball (0 : Rd 3) 1) = ENNReal.ofReal (massM Γ) :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  have h3a : 0 < 3 - alpha := by linarith
  have hc0 : 0 ≤ cGam Γ alpha := by
    unfold cGam massM; positivity
  have hconst : ENNReal.ofReal (3 - alpha) * Γ (ball (0 : Rd 3) 1) =
      ENNReal.ofReal (cGam Γ alpha) * ENNReal.ofReal (4 * π) := by
    rw [hM, ← ENNReal.ofReal_mul h3a.le, ← ENNReal.ofReal_mul hc0]
    congr 1
    unfold cGam
    field_simp
  calc ∫⁻ x, ENNReal.ofReal (gammaEps Γ ε x) ∂G
      = ENNReal.ofReal (3 - alpha) * Γ (ball (0 : Rd 3) 1) *
          ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (3 - alpha - 1)) * Φ r := by rw [h1, h2]
    _ = ENNReal.ofReal (cGam Γ alpha) * (ENNReal.ofReal (4 * π) *
          ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (3 - alpha - 1)) * Φ r) := by
        rw [hconst, mul_assoc]
    _ = ENNReal.ofReal (cGam Γ alpha) *
          ∫⁻ x, Φ ‖x‖ * ENNReal.ofReal (‖x‖ ^ (-alpha)) ∂(volume : Measure (Rd 3)) := by rw [h3]
    _ ≤ ENNReal.ofReal (cGam Γ alpha) * ENNReal.ofReal (bAlpha alpha * a ^ (1 - alpha)) :=
        mul_le_mul_of_nonneg_left h4 zero_le
    _ = ENNReal.ofReal (dGam Γ alpha * a ^ (1 - alpha)) := by
        rw [← ENNReal.ofReal_mul hc0]
        congr 1
        unfold dGam
        ring

/-- **`E:phase-trace`** (main TeX lines 2078-2082, proof 2108-2136), general form:
for a locally finite tempered `Γ` on `ℝ³` with `Γ(cA) = c^{3-α}Γ(A)`,
`0 < α < 2`, `ε, a > 0`, `q ∈ ℝ³`, and Archimedes' law: the integrand of
`T_ε(a,q)` is `G_a`-integrable, `T_ε(a,0) = ∫ Γ_ε dG_a` is real,
`|T_ε(a,q)| ≤ T_ε(a,0)`, and `|T_ε(a,q)| ≤ D_Γ a^{1-α}`.  Neither the spectral
measure nor the wave Fourier identity is used here. -/
theorem phase_trace (hA : ArchimedesLaw) {Γ : Measure (Rd 3)} [IsLocallyFiniteMeasure Γ]
    (hΓt : IsTempered Γ) {alpha : ℝ} (hΓs : SpectralHomogeneous Γ (3 - alpha))
    (ha0 : 0 < alpha) (ha2 : alpha < 2) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 < a) (q : Rd 3) :
    Integrable (fun x => Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)) *
        (gammaEps Γ ε x : ℂ)) (waveGreen 3 a) ∧
      traceT Γ ε a 0 = ((∫ x, gammaEps Γ ε x ∂(waveGreen 3 a) : ℝ) : ℂ) ∧
      ‖traceT Γ ε a q‖ ≤ ∫ x, gammaEps Γ ε x ∂(waveGreen 3 a) ∧
      ‖traceT Γ ε a q‖ ≤ dGam Γ alpha * a ^ (1 - alpha) := by
  have hgm := measurable_gammaEps Γ ε
  have hnn := gammaEps_nonneg Γ ε hε
  have hle := lintegral_gammaEps_le hA hΓt hΓs ha0 ha2 ε hε a ha
  have hgi : Integrable (gammaEps Γ ε) (waveGreen 3 a) :=
    ⟨hgm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn)).2
      (hle.trans_lt ENNReal.ofReal_lt_top)⟩
  have hnorm : ∀ x, ‖Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)) * (gammaEps Γ ε x : ℂ)‖ =
      gammaEps Γ ε x := by
    intro x
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (hnn x)]
    simp
  have hint : Integrable (fun x => Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)) *
      (gammaEps Γ ε x : ℂ)) (waveGreen 3 a) :=
    hgi.mono' (((by fun_prop : Continuous fun x : Rd 3 =>
        Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)))).measurable.mul
      (Complex.measurable_ofReal.comp hgm)).aestronglyMeasurable
      (Eventually.of_forall fun x => le_of_eq (hnorm x))
  have hT : ‖traceT Γ ε a q‖ ≤ ∫ x, gammaEps Γ ε x ∂(waveGreen 3 a) :=
    (norm_integral_le_integral_norm _).trans
      (le_of_eq (integral_congr_ae (Eventually.of_forall hnorm)))
  have h3a : 0 < 3 - alpha := by linarith
  have h2a : 0 < 2 - alpha := by linarith
  have hD : 0 ≤ dGam Γ alpha * a ^ (1 - alpha) := by
    unfold dGam cGam bAlpha massM; positivity
  refine ⟨hint, ?_, hT, hT.trans ?_⟩
  · unfold traceT
    simp only [inner_zero_left, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    exact integral_complex_ofReal
  · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hgm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hD hle

/-! ### The Fourier form of `T_ε` -/

/-- The Gaussian Fourier pairing for `Γ_ε` (proof of `L:phase-contractions`,
main TeX lines 2090-2096 and 2107-2108): `Γ_ε(x) = ∫ e^{iξ·x} e^{-ε|ξ|²} μ(dξ)` for `ε > 0`,
any `d`; only the spectral convention is assumed (as an identity of Lean
integrals). -/
theorem gammaEps_fourier {d : ℕ} {Γ μ : Measure (Rd d)} (hsp : IsSpectralMeasure Γ μ) (ε : ℝ)
    (hε : 0 < ε) (x : Rd d) :
    (gammaEps Γ ε x : ℂ) = ∫ ξ, Complex.exp (Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) *
      (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ) ∂μ := by
  set s : ℝ := 1 / (4 * ε) with hs_def
  have hs : 0 < s := by positivity
  have h := spectral_translated_gauss hsp s hs x
  have hpt : ∀ y : Rd d, pdens (2 * ε) (x - y) =
      (2 * π * (2 * ε)) ^ (-((d : ℝ) / 2)) * Real.exp (-(s * ‖y - x‖ ^ 2)) := by
    intro y
    simp only [pdens, pprof, norm_sub_rev x y, hs_def]
    congr 2
    field_simp
    ring
  have hC : (2 * π * (2 * ε)) ^ (-((d : ℝ) / 2)) * (π / s) ^ ((d : ℝ) / 2) = 1 := by
    rw [show π / s = 2 * π * (2 * ε) by rw [hs_def]; field_simp; ring,
      Real.rpow_neg (by positivity), inv_mul_cancel₀ (by positivity)]
  unfold gammaEps
  simp_rw [hpt]
  rw [integral_const_mul, Complex.ofReal_mul, ← integral_complex_ofReal, h, ← mul_assoc,
    ← Complex.ofReal_mul, hC, Complex.ofReal_one, one_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [hs_def]
  congr 4
  field_simp

/-- **The Fourier form of `T_ε`** (main TeX lines 2081-2084, proof 2107-2108,
"Fourier Fubini"): given the d = 3 wave Green Fourier identity, for a locally
finite tempered `μ` with the spectral convention, `ε, a > 0` and `q ∈ ℝ³`,
`ξ ↦ Ĝ_a(q+ξ) e^{-ε|ξ|²}` is `μ`-integrable and
`T_ε(a,q) = ∫ Ĝ_a(q+ξ) e^{-ε|ξ|²} μ(dξ)`, with `Ĝ_a = WaveKernel.waveHat a`. -/
theorem traceT_fourier (hW : WaveFourierThree) {Γ μ : Measure (Rd 3)} [IsLocallyFiniteMeasure μ]
    (hμt : IsTempered μ) (hsp : IsSpectralMeasure Γ μ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 < a)
    (q : Rd 3) :
    Integrable (fun ξ : Rd 3 => (waveHat a (q + ξ) : ℂ) * (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ)) μ ∧
      traceT Γ ε a q =
        ∫ ξ, (waveHat a (q + ξ) : ℂ) * (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ) ∂μ := by
  have he : Integrable (fun ξ : Rd 3 => Real.exp (-(ε * ‖ξ‖ ^ 2))) μ := integrable_gauss_zero hμt hε
  have hwc : Continuous fun ξ : Rd 3 => waveHat a (q + ξ) :=
    waveHat_continuous.comp (continuous_const.prodMk (continuous_const.add continuous_id))
  refine ⟨(he.const_mul a).mono' (by fun_prop) (Eventually.of_forall fun ξ => ?_), ?_⟩
  · rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have := abs_waveHat_le a (q + ξ)
    rw [abs_of_pos ha] at this
    exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
  have hprod : Integrable (Function.uncurry fun (x ξ : Rd 3) =>
      Complex.exp (Complex.I * ((inner ℝ (q + ξ) x : ℝ) : ℂ)) * (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ))
      ((waveGreen 3 a).prod μ) := by
    refine (he.comp_snd (waveGreen 3 a)).mono' ?_ (Eventually.of_forall fun p => le_of_eq ?_)
    · exact (by fun_prop : Continuous fun p : Rd 3 × Rd 3 =>
        Complex.exp (Complex.I * ((inner ℝ (q + p.2) p.1 : ℝ) : ℂ)) *
          (Real.exp (-(ε * ‖p.2‖ ^ 2)) : ℂ)).aestronglyMeasurable
    · show ‖Complex.exp (Complex.I * ((inner ℝ (q + p.2) p.1 : ℝ) : ℂ)) *
          (Real.exp (-(ε * ‖p.2‖ ^ 2)) : ℂ)‖ = Real.exp (-(ε * ‖p.2‖ ^ 2))
      rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
      simp
  unfold traceT
  calc ∫ x, Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)) * (gammaEps Γ ε x : ℂ)
        ∂(waveGreen 3 a)
      = ∫ x, ∫ ξ, Complex.exp (Complex.I * ((inner ℝ (q + ξ) x : ℝ) : ℂ)) *
          (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ) ∂μ ∂(waveGreen 3 a) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [gammaEps_fourier hsp ε hε x, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only
        rw [inner_add_left, Complex.ofReal_add, mul_add, Complex.exp_add]
        ring
    _ = ∫ ξ, ∫ x, Complex.exp (Complex.I * ((inner ℝ (q + ξ) x : ℝ) : ℂ)) *
          (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ) ∂(waveGreen 3 a) ∂μ := integral_integral_swap hprod
    _ = ∫ ξ, (waveHat a (q + ξ) : ℂ) * (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
        simp only
        rw [integral_mul_const, hW a ha (q + ξ)]

/-! ### `L:phase-contractions` -/

/-- **`L:phase-contractions`** (Two static contraction bounds; main TeX lines
2072-2086, proof 2088-2138, at a284420), with the section's standing
assumptions (`PhaseCovariance`, main TeX lines 2054-2057) and the constants of
`E:phase-constants` (lines 2058-2067), for `G_a = WaveGreen.waveGreen 3 a`, given the two supplied
inputs `WaveFourierThree` (the d = 3 wave Green Fourier identity) and
`ArchimedesLaw`:
* `E:phase-resolvent`: for `λ > 0` and `q ∈ ℝ³`, `ξ ↦ 1/(λ²+|q+ξ|²)` is
  `μ`-integrable and `∫ μ(dξ)/(λ²+|q+ξ|²) ≤ R_α λ^{α-2}`;
* `E:phase-trace` and the definition of `T_ε`: for `a, ε > 0` and `q ∈ ℝ³`,
  `y ↦ p_{2ε}(x-y)` is `Γ`-integrable and `Γ_ε(x) ≥ 0` for every `x`, the
  integrand of `T_ε(a,q) = ∫ e^{iq·x} Γ_ε(x) G_a(dx)` is `G_a`-integrable,
  `ξ ↦ Ĝ_a(q+ξ) e^{-ε|ξ|²}` is `μ`-integrable,
  `T_ε(a,q) = ∫ Ĝ_a(q+ξ) e^{-ε|ξ|²} μ(dξ)`, and `|T_ε(a,q)| ≤ D_Γ a^{1-α}`.
`WaveFourierThree` enters only the Fourier form of `T_ε`; `ArchimedesLaw` only
the bound.  Fields of `PhaseCovariance` used: `alpha_pos`, `alpha_lt_two`,
`Γ_radon`, `Γ_tempered`, `μ_radon`, `μ_tempered`, `spectral`, `scaling`;
carried unused: `Γ_even`, `Γ_posdef`, `μ_even`. -/
theorem phase_contractions_paper {alpha : ℝ} {Γ μ : Measure (Rd 3)}
    (h : PhaseCovariance alpha Γ μ) (hW : WaveFourierThree) (hA : ArchimedesLaw) :
    (∀ lam : ℝ, 0 < lam → ∀ q : Rd 3,
      Integrable (fun ξ : Rd 3 => 1 / (lam ^ 2 + ‖q + ξ‖ ^ 2)) μ ∧
        ∫ ξ, 1 / (lam ^ 2 + ‖q + ξ‖ ^ 2) ∂μ ≤ ralpha μ alpha * lam ^ (alpha - 2)) ∧
    (∀ a : ℝ, 0 < a → ∀ ε : ℝ, 0 < ε → ∀ q : Rd 3,
      (∀ x : Rd 3, Integrable (fun y => pdens (2 * ε) (x - y)) Γ ∧ 0 ≤ gammaEps Γ ε x) ∧
      Integrable (fun x => Complex.exp (Complex.I * ((inner ℝ q x : ℝ) : ℂ)) *
          (gammaEps Γ ε x : ℂ)) (waveGreen 3 a) ∧
        Integrable (fun ξ : Rd 3 => (waveHat a (q + ξ) : ℂ) *
          (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ)) μ ∧
        traceT Γ ε a q = ∫ ξ, (waveHat a (q + ξ) : ℂ) * (Real.exp (-(ε * ‖ξ‖ ^ 2)) : ℂ) ∂μ ∧
        ‖traceT Γ ε a q‖ ≤ dGam Γ alpha * a ^ (1 - alpha)) := by
  have := h.μ_radon
  have := h.Γ_radon
  refine ⟨fun lam hlam q => ?_, fun a ha ε hε q => ?_⟩
  · obtain ⟨h1, h2, _⟩ := phase_resolvent h.μ_tempered h.spectral h.scaling' h.alpha_pos
      h.alpha_lt_two lam hlam q
    exact ⟨h1, h2⟩
  · obtain ⟨hi, _, _, hb⟩ := phase_trace hA h.Γ_tempered h.scaling h.alpha_pos h.alpha_lt_two
      ε hε a ha q
    obtain ⟨hi2, hF⟩ := traceT_fourier hW h.μ_tempered h.spectral ε hε a ha q
    exact ⟨fun x => ⟨integrable_pdens_sub h.Γ_tempered _ (by positivity) x,
      gammaEps_nonneg Γ ε hε x⟩, hi, hi2, hF, hb⟩

end StratonovichHAMSecondMoment.PhaseContractions
