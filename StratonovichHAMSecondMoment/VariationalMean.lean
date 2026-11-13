module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemmas `L:variational-heat-envelope` (Gaussian envelope for the original
covariance; statement TeX lines 23-35, proof 37-62) and
`L:variational-global-mean` (global regularity of the original mean;
statement 64-74, proof 76-96) of `notes/integrated_unmasked_variational.tex`
at revision a284420.  The section's standing assumption (line 4) is a nonzero
covariance satisfying `H:homog` with `a = α₀`; the wrappers carry it as
`HomogHypothesis.HomogCovariance`, `Γ ≠ 0`, and the mean is taken with
exponent `α₀`.  Definitions reused: `VariationalDilation.conv`
(`(Γ * φ)(x) = ∫ φ(x - y) Γ(dy)`), `VariationalDilation.mean`
(`h_{Ψ,s}(x) = ∫_{(0,1)} |s-u|^{-a} (Γ * Ψ(u,·))(x) du`) and the control class
`VariationalDilation.CPos` (`E:variational-positive-class`).  New definition:
the heat kernel `heatK ε x = (2πε)^{-d/2} e^{-|x|²/(2ε)}` (lines 25-26).

Formalized:
* `variational_heat_envelope_paper` (same assumptions as the TeX, `ε > 0`):
  `y ↦ p_ε(x - y)` is `Γ`-integrable for every `x` (so `(Γ * p_ε)(x)`, in
  particular the value at `0`, is a finite genuine integral), the spectral
  integrand is `μ`-integrable, the identity of
  `E:variational-heat-envelope` holds at every `x` (as complex numbers, no
  normalization factor), `0 ≤ (Γ * p_ε)(x) ≤ (Γ * p_ε)(0)`, and
  `(Γ * p_ε)(0) > 0`.  General form `heat_envelope` (tempered `Γ`, `μ`,
  spectral convention; no `Γ ≠ 0`) plus `heat_conv_pos` (tempered `Γ ≠ 0`).
* `variational_global_mean_paper` (same assumptions as the TeX, `Ψ ∈ CPos`):
  the display `E:variational-global-mean` on `I = [0,1]`: there are real
  `M, C_Ψ ≥ 0` with `0 ≤ h_s(x) ≤ M` and
  `|h_s(x) - h_t(x)| ≤ C_Ψ |s - t|` for all `s, t ∈ I`, `x ∈ ℝ^d` (the
  sup-norm bound, stated pointwise in `x`); together with the integrability
  of every integrand in the definition of `h_s(x)` (`y ↦ Ψ(u, x-y)` against
  `Γ`, and `u ↦ |s-u|^{-α₀} (Γ * Ψ(u,·))(x)` on `(0,1)`), so that the
  bounds are about genuine integrals and not Lean's junk value `0`;
  continuity of `x ↦ h_s(x)`; and integrability of `h_s f²` for every
  `f ∈ L²(ℝ^d)`.  `variational_global_mean_lipschitz_paper` adds the joint
  Lipschitz bound `|h_s(x) - h_t(x')| ≤ C dist((s,x),(t,x'))` on `I × ℝ^d`.
  General form `global_mean` (tempered `Γ`, `μ`, spectral convention,
  `a < 1`).
* `isRayleighTrial_mean_iff_paper`: for `s ∈ I`, the explicit side condition
  `integrable_pot` of `WeakSobolev.IsRayleighTrial` (used by
  `VariationalDilation.rate`) is automatic for the manuscript's potential
  `h_s`: a trial is exactly a unit `f ∈ L²` with an `L²` weak gradient.

Narrower conclusion (not formalized): the first sentence of
`L:variational-global-mean`, "every mixed time and space derivative of `h_s`
is globally bounded in space, uniformly on compact time intervals".  Only the
displayed consequence `E:variational-global-mean` is formalized (plus the
spatial and joint Lipschitz bounds above, which are first-order statements
without derivatives), and only on `I = [0,1]`, the interval named in the
display.  No differentiability of `h_s` is proved.  The smoothness of
`x ↦ (Γ * p_ε)(x)` mentioned in the proof of `L:variational-heat-envelope`
(lines 44-46) is not part of its statement and is not formalized either.

Supplied inputs: none (no named analytic hypotheses).

Implicit hypotheses made explicit: `ε > 0` for `p_ε`; finiteness of
`(Γ * p_ε)(0)` and of `h_s(x)` is stated as integrability of the integrands,
since a Lean Bochner integral of a non-integrable function is `0`; `M` and
`C_Ψ` are real numbers (finite) and nonnegative.

Hypotheses of `H:homog` used: `Γ_tempered`, `μ_tempered`, `spectral`, and
`alpha0_lt_one` (for the global mean); `Γ ≠ 0` is used only for the strict
positivity in `L:variational-heat-envelope` and is carried, unused, in the
global-mean wrappers.  The other fields of `H:homog` (dimension, evenness,
positive definiteness, Radon property, scaling, the ranges of `α`,
`0 < α₀`) are carried, unused.

Proof route.  `L:variational-heat-envelope`: the identity is
`MaskedSpectralGrowth.spectral_translated_gauss` (the spectral convention
applied to a Gaussian Schwartz test, with Mathlib's Gaussian Fourier
integral), not the TeX's pairing with an arbitrary Schwartz test and
uniqueness of continuous distributions (lines 48-57); integrability against
`Γ` and `μ` comes from the package's integral form of temperedness, not from
polynomial ball growth (lines 38-44).  The bound by the value at `0` is the
TeX's (line 59), but without evenness of `μ`: the spectral integral is real
because it equals the real left side.  `L:variational-global-mean`: as in the
TeX, `|Ψ(u,z)| ≤ C e^{-|z|²/2}` from the spatial support and the envelope at
`ε = 1` give a uniform bound on `Γ * Ψ(u,·)`; the change of variables
`r = s - u` (lines 84-88) is `integral_sub_left_eq_self`, with the integrand
vanishing outside `(-1,1)` for `s ∈ [0,1]`; and `∫_{-1}^{1} |r|^{-a} dr =
2/(1-a)` for `a < 1`.  The Lipschitz bound does not differentiate under the
integral (the TeX's route, lines 82-94): it applies the Lipschitz bound of
the smooth compactly supported `Ψ` (`ContDiff.lipschitzWith_of_hasCompactSupport`)
inside both integrals, dominated by the same Gaussian envelope.  Lemmas
marked "Auxiliary to the Lean proof route" have no manuscript label.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.MaskedSpectralGrowth
public import StratonovichHAMSecondMoment.TimeFractional
public import StratonovichHAMSecondMoment.VariationalDilation
public import StratonovichHAMSecondMoment.WeakSobolev

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set

namespace StratonovichHAMSecondMoment.VariationalMean

open HomogHypothesis (Rd HomogCovariance IsTempered IsSpectralMeasure)
open MaskedSpectralGrowth (integrable_gauss_of_tempered integrable_gauss_zero
  spectral_translated_gauss)
open VariationalDilation (CPos conv mean)

variable {d : ℕ}

/-! ### `L:variational-heat-envelope` -/


/-- The normalized heat kernel `p_ε(x) = (2πε)^{-d/2} e^{-|x|²/(2ε)}` (TeX lines 25-26). -/
def heatK (ε : ℝ) (x : Rd d) : ℝ :=
  (2 * Real.pi * ε) ^ (-((d : ℝ) / 2)) * Real.exp (-(‖x‖ ^ 2 / (2 * ε)))

/-- `p_ε > 0` for `ε > 0`. -/
theorem heatK_pos {ε : ℝ} (hε : 0 < ε) (x : Rd d) : 0 < heatK ε x := by
  unfold heatK; positivity

/-- The spectral integrand of `E:variational-heat-envelope`,
`ξ ↦ e^{iξ·x} e^{-ε|ξ|²/2}`. -/
def heatSpec (ε : ℝ) (x ξ : Rd d) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) * (Real.exp (-(ε * ‖ξ‖ ^ 2 / 2)) : ℂ)

/-- Auxiliary to the Lean proof route.  For a tempered `Γ` and `ε > 0`, every
translate `y ↦ p_ε(x - y)` is `Γ`-integrable (the TeX's finiteness of the
classical convolution, lines 38-45, via the package's integral form of
temperedness instead of polynomial ball growth). -/
theorem heatK_integrable {Γ : Measure (Rd d)} (hΓ : IsTempered Γ) {ε : ℝ} (hε : 0 < ε)
    (x : Rd d) : Integrable (fun y => heatK ε (x - y)) Γ := by
  have h := (integrable_gauss_of_tempered hΓ (b := 1 / (2 * ε)) (by positivity) x).const_mul
    ((2 * Real.pi * ε) ^ (-((d : ℝ) / 2)))
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [heatK]
  rw [norm_sub_rev]
  congr 2
  field_simp

/-- Auxiliary to the Lean proof route.  For a tempered `μ` and `ε > 0`, the
spectral integrand is `μ`-integrable (absolute finiteness, line 55). -/
theorem heatSpec_integrable {μ : Measure (Rd d)} (hμ : IsTempered μ) {ε : ℝ} (hε : 0 < ε)
    (x : Rd d) : Integrable (heatSpec ε x) μ := by
  have h := integrable_gauss_zero hμ (c := ε / 2) (by positivity)
  refine Integrable.mono' h (by unfold heatSpec; fun_prop) (Filter.Eventually.of_forall fun ξ => ?_)
  rw [heatSpec, norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  apply le_of_eq; congr 1; ring

/-- The identity of `E:variational-heat-envelope`:
`(Γ * p_ε)(x) = ∫ e^{iξ·x} e^{-ε|ξ|²/2} μ(dξ)`, from the spectral convention
alone (as an identity of Lean integrals; integrability of both sides is in
`heat_envelope`).  Route: `MaskedSpectralGrowth.spectral_translated_gauss`,
not the TeX's distributional pairing (lines 48-57). -/
theorem heat_identity {Γ μ : Measure (Rd d)} (hsp : IsSpectralMeasure Γ μ) {ε : ℝ} (hε : 0 < ε)
    (x : Rd d) :
    ((conv Γ (heatK ε) x : ℝ) : ℂ) = ∫ ξ, heatSpec ε x ξ ∂μ := by
  have hs : (0:ℝ) < 1 / (2 * ε) := by positivity
  have h := spectral_translated_gauss hsp (1 / (2 * ε)) hs x
  have e1 : ∀ y : Rd d, heatK ε (x - y) =
      (2 * Real.pi * ε) ^ (-((d : ℝ) / 2)) * Real.exp (-(1 / (2 * ε) * ‖y - x‖ ^ 2)) := by
    intro y; unfold heatK; rw [norm_sub_rev]; congr 2; field_simp
  simp only [conv, heatSpec]
  simp_rw [e1]
  rw [integral_const_mul, Complex.ofReal_mul, ← integral_complex_ofReal, h]
  have e2 : ∀ ξ : Rd d, ‖ξ‖ ^ 2 / (4 * (1 / (2 * ε))) = ε * ‖ξ‖ ^ 2 / 2 := by
    intro ξ; field_simp; ring
  simp_rw [e2]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  have e3 : Real.pi / (1 / (2 * ε)) = 2 * Real.pi * ε := by field_simp
  rw [e3, ← Real.rpow_add (by positivity), neg_add_cancel, Real.rpow_zero,
    Complex.ofReal_one, one_mul]

/-- **`L:variational-heat-envelope`**, general form without its positivity
clause: for tempered `Γ`, `μ` with the spectral convention and `ε > 0`, both
integrands are integrable, the identity holds, and
`0 ≤ (Γ * p_ε)(x) ≤ (Γ * p_ε)(0)` for every `x` (finiteness of the value at
`0` is the integrability of the first clause).  Evenness of `μ` is not used:
the spectral integral is real because it equals the real left side. -/
theorem heat_envelope {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) {ε : ℝ} (hε : 0 < ε) :
    (∀ x, Integrable (fun y => heatK ε (x - y)) Γ) ∧
    (∀ x, Integrable (heatSpec ε x) μ) ∧
    (∀ x, ((conv Γ (heatK ε) x : ℝ) : ℂ) = ∫ ξ, heatSpec ε x ξ ∂μ) ∧
    (∀ x, 0 ≤ conv Γ (heatK ε) x ∧ conv Γ (heatK ε) x ≤ conv Γ (heatK ε) 0) := by
  refine ⟨heatK_integrable hΓt hε, heatSpec_integrable hμt hε, heat_identity hsp hε, fun x => ?_⟩
  have hnn : 0 ≤ conv Γ (heatK ε) x := integral_nonneg fun y => (heatK_pos hε _).le
  refine ⟨hnn, ?_⟩
  have h0 : ((conv Γ (heatK ε) 0 : ℝ) : ℂ) = ((∫ ξ, Real.exp (-(ε * ‖ξ‖ ^ 2 / 2)) ∂μ : ℝ) : ℂ) := by
    rw [heat_identity hsp hε, ← integral_complex_ofReal]
    congr 1; funext ξ; simp [heatSpec]
  have h0' := Complex.ofReal_injective h0
  have hle := norm_integral_le_integral_norm (μ := μ) (heatSpec ε x)
  have hn : ∀ ξ, ‖heatSpec ε x ξ‖ = Real.exp (-(ε * ‖ξ‖ ^ 2 / 2)) := by
    intro ξ
    rw [heatSpec, norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, one_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  simp only [hn] at hle
  rw [← heat_identity hsp hε, Complex.norm_real, Real.norm_of_nonneg hnn] at hle
  rw [h0']; exact hle

/-- The value at zero is strictly positive when `Γ ≠ 0` (line 60). -/
theorem heat_conv_pos {Γ : Measure (Rd d)} (hΓt : IsTempered Γ) (hΓ : Γ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    0 < conv Γ (heatK ε) 0 :=
  TimeFractional.integral_pos_of_ae_pos (heatK_integrable hΓt hε 0) hΓ
    (Filter.Eventually.of_forall fun _ => heatK_pos hε _)

/-- Auxiliary to the Lean proof route.  For `a < 1`, `r ↦ |r|^{-a}` is
integrable on `(-1, 1)` (the integrability of `|r|^{-a}` used at TeX
lines 89-91). -/
theorem abs_rpow_integrableOn {a : ℝ} (ha : a < 1) :
    IntegrableOn (fun r : ℝ => |r| ^ (-a)) (Ioo (-1) 1) := by
  have hpos : IntegrableOn (fun r : ℝ => |r| ^ (-a)) (Ioo 0 1) := by
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := -a) one_pos).2 (by linarith)
    refine this.congr_fun (fun r hr => ?_) measurableSet_Ioo
    simp [abs_of_pos hr.1]
  have hneg : IntegrableOn (fun r : ℝ => |r| ^ (-a)) (Ioo (-1) 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Ioo, neg_neg, neg_zero]
    exact hpos
  have hu : Ioo (-1 : ℝ) 1 ⊆ Ioo (-1) 0 ∪ {0} ∪ Ioo 0 1 := by
    intro r hr
    rcases lt_trichotomy r 0 with h | h | h
    · exact Or.inl (Or.inl ⟨hr.1, h⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨h, hr.2⟩
  refine IntegrableOn.mono_set ?_ hu
  refine (hneg.union ?_).union hpos
  exact integrableOn_singleton (by simp) (by simp)

/-- Auxiliary to the Lean proof route.  For `a < 1`,
`∫_{-1}^{1} |r|^{-a} dr = 2/(1-a)`. -/
theorem abs_rpow_integral {a : ℝ} (ha : a < 1) :
    ∫ r in Ioo (-1 : ℝ) 1, |r| ^ (-a) = 2 / (1 - a) := by
  let f : ℝ → ℝ := (Iio 1).indicator (fun r => r ^ (-a))
  have h := integral_comp_abs (f := f)
  have e1 : (fun x : ℝ => f |x|) = (Ioo (-1) 1).indicator (fun r : ℝ => |r| ^ (-a)) := by
    funext x
    simp only [f, indicator, mem_Iio, mem_Ioo]
    by_cases hx : |x| < 1
    · simp [hx, abs_lt.1 hx]
    · simp only [hx, ite_false]
      rw [eq_comm, ite_eq_right_iff]
      exact fun h => absurd (abs_lt.2 h) hx
  have e2 : ∫ x in Ioo (0 : ℝ) 1, x ^ (-a) = 1 / (-a + 1) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith)), Real.one_rpow, Real.zero_rpow (by linarith)]
    ring
  rw [e1, integral_indicator measurableSet_Ioo, setIntegral_indicator measurableSet_Iio,
    Ioi_inter_Iio, e2] at h
  rw [h]
  have : (1 : ℝ) - a ≠ 0 := by linarith
  have e : -a + 1 = 1 - a := by ring
  rw [e]; field_simp


/-- Auxiliary to the Lean proof route.  A compactly supported `Ψ` on
`ℝ × ℝ^d` vanishes for `|x| > R`, for some `R ≥ 0` (the common spatial
support of TeX line 79). -/
theorem exists_radius {Ψ : ℝ × Rd d → ℝ} (hc : HasCompactSupport Ψ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ u z, R < ‖z‖ → Ψ (u, z) = 0 := by
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ × Rd d)).1 hc.isCompact.isBounded
  refine ⟨max R 0, le_max_right _ _, fun u z hz => ?_⟩
  by_contra h
  have hm := hR (subset_tsupport Ψ h)
  rw [Metric.mem_closedBall, dist_zero_right] at hm
  have h2 : ‖z‖ ≤ ‖(u, z)‖ := by simp
  linarith [le_max_left R 0]

/-- Auxiliary to the Lean proof route.  A function with closed support in
`(0,1) × ℝ^d` vanishes at times outside `(0,1)` (its extension by zero, line
77). -/
theorem eq_zero_of_time {Ψ : ℝ × Rd d → ℝ} (ht : tsupport Ψ ⊆ Ioo (0 : ℝ) 1 ×ˢ univ) {u : ℝ}
    (hu : u ∉ Ioo (0 : ℝ) 1) (z : Rd d) : Ψ (u, z) = 0 := by
  by_contra h
  exact hu (ht (subset_tsupport Ψ h)).1

/-- Auxiliary to the Lean proof route.  `1 ≤ e^{R²/2} e^{-|z|²/2}` on
`|z| ≤ R` (the positive minimum of the heat kernel on the support, line 80). -/
theorem one_le_gauss {R : ℝ} {z : Rd d} (hz : ‖z‖ ≤ R) :
    1 ≤ Real.exp (R ^ 2 / 2) * Real.exp (-(‖z‖ ^ 2 / 2)) := by
  rw [← Real.exp_add]
  apply Real.one_le_exp
  have : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
  linarith

/-- Auxiliary to the Lean proof route.  The Gaussian mass
`∫ e^{-|y|²/2} Γ(dy) = (2π)^{d/2} (Γ * p_1)(0)`. -/
def gMass (Γ : Measure (Rd d)) : ℝ := ∫ y, Real.exp (-(‖y‖ ^ 2 / 2)) ∂Γ

/-- Auxiliary to the Lean proof route.  `L:variational-heat-envelope` at
`ε = 1`, rescaled: `y ↦ e^{-|x-y|²/2}` is `Γ`-integrable and
`∫ e^{-|x-y|²/2} Γ(dy) ≤ gMass Γ` for every `x` (tempered `Γ`, `μ`, spectral
convention). -/
theorem gauss_conv {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) (x : Rd d) :
    Integrable (fun y => Real.exp (-(‖x - y‖ ^ 2 / 2))) Γ ∧
      ∫ y, Real.exp (-(‖x - y‖ ^ 2 / 2)) ∂Γ ≤ gMass Γ := by
  obtain ⟨hi, -, -, hb⟩ := heat_envelope hΓt hμt hsp one_pos
  set c : ℝ := (2 * Real.pi * 1) ^ (-((d : ℝ) / 2)) with hcdef
  have hc : 0 < c := by positivity
  have e : ∀ w : Rd d, Real.exp (-(‖w‖ ^ 2 / 2)) = c⁻¹ * heatK 1 w := by
    intro w
    simp only [heatK, ← hcdef]
    field_simp
  constructor
  · simp_rw [e]; exact (hi x).const_mul _
  · have h := (hb x).2
    simp only [conv] at h
    rw [gMass]
    simp_rw [e]
    rw [integral_const_mul, integral_const_mul]
    have h0 : ∫ y, heatK 1 y ∂Γ = ∫ y, heatK (d := d) 1 (0 - y) ∂Γ := by
      congr 1; funext y; simp [heatK]
    rw [h0]
    exact mul_le_mul_of_nonneg_left h (inv_nonneg.2 hc.le)

/-- Auxiliary to the Lean proof route.  `gMass Γ ≥ 0`. -/
theorem gMass_nonneg (Γ : Measure (Rd d)) : 0 ≤ gMass Γ :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- Auxiliary to the Lean proof route.  If `|Ψ| ≤ B` and `Ψ(u,z) = 0` for
`|z| > R`, then `|Ψ(u,z)| ≤ B e^{R²/2} e^{-|z|²/2}` (TeX lines 78-80 for
`D = id`). -/
theorem pt_bound {Ψ : ℝ × Rd d → ℝ} {B R : ℝ} (hB : ∀ p, |Ψ p| ≤ B)
    (hR : ∀ u z, R < ‖z‖ → Ψ (u, z) = 0) (u : ℝ) (z : Rd d) :
    |Ψ (u, z)| ≤ B * Real.exp (R ^ 2 / 2) * Real.exp (-(‖z‖ ^ 2 / 2)) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (u, z))
  by_cases hz : ‖z‖ ≤ R
  · have h1 := one_le_gauss hz
    calc |Ψ (u, z)| ≤ B := hB _
      _ ≤ B * (Real.exp (R ^ 2 / 2) * Real.exp (-(‖z‖ ^ 2 / 2))) :=
          le_mul_of_one_le_right hB0 h1
      _ = _ := by ring
  · rw [hR u z (not_le.1 hz), abs_zero]
    positivity

/-- Auxiliary to the Lean proof route.  If `|Ψ p - Ψ q| ≤ L dist(p,q)` and
`Ψ(u,z) = 0` for `|z| > R`, then
`|Ψ(u,z) - Ψ(u',z')| ≤ L dist((u,z),(u',z')) e^{R²/2} (e^{-|z|²/2} + e^{-|z'|²/2})`.
This replaces the TeX's bound on the time derivative (Lean route). -/
theorem pt_diff {Ψ : ℝ × Rd d → ℝ} {L R : ℝ} (hL : ∀ p q, |Ψ p - Ψ q| ≤ L * dist p q)
    (hR : ∀ u z, R < ‖z‖ → Ψ (u, z) = 0) (u u' : ℝ) (z z' : Rd d) :
    |Ψ (u, z) - Ψ (u', z')| ≤ L * dist (u, z) (u', z') * Real.exp (R ^ 2 / 2) *
      (Real.exp (-(‖z‖ ^ 2 / 2)) + Real.exp (-(‖z'‖ ^ 2 / 2))) := by
  set D := L * dist (u, z) (u', z')
  have hD : 0 ≤ D := (abs_nonneg _).trans (hL _ _)
  have h1 : 0 ≤ Real.exp (R ^ 2 / 2) * Real.exp (-(‖z‖ ^ 2 / 2)) := by positivity
  have h2 : 0 ≤ Real.exp (R ^ 2 / 2) * Real.exp (-(‖z'‖ ^ 2 / 2)) := by positivity
  have key : 1 ≤ Real.exp (R ^ 2 / 2) * Real.exp (-(‖z‖ ^ 2 / 2)) +
      Real.exp (R ^ 2 / 2) * Real.exp (-(‖z'‖ ^ 2 / 2)) ∨ (Ψ (u, z) = 0 ∧ Ψ (u', z') = 0) := by
    by_cases hz : ‖z‖ ≤ R
    · exact Or.inl (by linarith [one_le_gauss hz])
    · by_cases hz' : ‖z'‖ ≤ R
      · exact Or.inl (by linarith [one_le_gauss hz'])
      · exact Or.inr ⟨hR u z (not_le.1 hz), hR u' z' (not_le.1 hz')⟩
  rcases key with k | ⟨e1, e2⟩
  · calc |Ψ (u, z) - Ψ (u', z')| ≤ D := hL _ _
      _ ≤ D * (Real.exp (R ^ 2 / 2) * Real.exp (-(‖z‖ ^ 2 / 2)) +
          Real.exp (R ^ 2 / 2) * Real.exp (-(‖z'‖ ^ 2 / 2))) := le_mul_of_one_le_right hD k
      _ = _ := by ring
  · rw [e1, e2, sub_zero, abs_zero]
    positivity

section conv
variable {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
  (hsp : IsSpectralMeasure Γ μ)
include hΓt hμt hsp

/-- Auxiliary to the Lean proof route.  Under the hypotheses of `pt_bound`
and continuity of `Ψ`, each `y ↦ Ψ(u, x - y)` is `Γ`-integrable (tempered
`Γ`, `μ`, spectral convention). -/
theorem conv_integrable {Ψ : ℝ × Rd d → ℝ} (hcont : Continuous Ψ) {B R : ℝ}
    (hB : ∀ p, |Ψ p| ≤ B) (hR : ∀ u z, R < ‖z‖ → Ψ (u, z) = 0) (u : ℝ) (x : Rd d) :
    Integrable (fun y => Ψ (u, x - y)) Γ := by
  have hg := (gauss_conv hΓt hμt hsp x).1.const_mul (B * Real.exp (R ^ 2 / 2))
  refine Integrable.mono' hg (hcont.comp (by fun_prop)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact pt_bound hB hR u (x - y)

/-- Auxiliary to the Lean proof route.  The uniform bound
`|(Γ * Ψ(u,·))(x)| ≤ B e^{R²/2} gMass Γ` (TeX lines 81-82, for `D = id`). -/
theorem conv_le {Ψ : ℝ × Rd d → ℝ} {B R : ℝ}
    (hB : ∀ p, |Ψ p| ≤ B) (hR : ∀ u z, R < ‖z‖ → Ψ (u, z) = 0) (u : ℝ) (x : Rd d) :
    |conv Γ (fun y => Ψ (u, y)) x| ≤ B * Real.exp (R ^ 2 / 2) * gMass Γ := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (u, x))
  have hg := (gauss_conv hΓt hμt hsp x)
  simp only [conv]
  refine (norm_integral_le_of_norm_le (f := fun y => Ψ (u, x - y))
    (hg.1.const_mul (B * Real.exp (R ^ 2 / 2)))
    (Filter.Eventually.of_forall fun y => ?_)).trans ?_
  · rw [Real.norm_eq_abs]; exact pt_bound hB hR u (x - y)
  · rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hg.2 (by positivity)

/-- Auxiliary to the Lean proof route.  The convolution is jointly Lipschitz:
`|(Γ*Ψ(u,·))(x) - (Γ*Ψ(u',·))(x')| ≤ 2 L e^{R²/2} gMass Γ · dist((u,x),(u',x'))`. -/
theorem conv_lip {Ψ : ℝ × Rd d → ℝ} (hcont : Continuous Ψ) {B L R : ℝ}
    (hB : ∀ p, |Ψ p| ≤ B) (hL : ∀ p q, |Ψ p - Ψ q| ≤ L * dist p q)
    (hR : ∀ u z, R < ‖z‖ → Ψ (u, z) = 0) (u u' : ℝ) (x x' : Rd d) :
    |conv Γ (fun y => Ψ (u, y)) x - conv Γ (fun y => Ψ (u', y)) x'| ≤
      2 * L * Real.exp (R ^ 2 / 2) * gMass Γ * dist (u, x) (u', x') := by
  have hD : 0 ≤ L * dist (u, x) (u', x') * Real.exp (R ^ 2 / 2) :=
    mul_nonneg ((abs_nonneg _).trans (hL (u, x) (u', x'))) (Real.exp_pos _).le
  have g1 := gauss_conv hΓt hμt hsp x
  have g2 := gauss_conv hΓt hμt hsp x'
  simp only [conv]
  rw [← integral_sub (conv_integrable hΓt hμt hsp hcont hB hR u x)
    (conv_integrable hΓt hμt hsp hcont hB hR u' x')]
  refine (norm_integral_le_of_norm_le (f := fun y => Ψ (u, x - y) - Ψ (u', x' - y))
    ((g1.1.add g2.1).const_mul
    (L * dist (u, x) (u', x') * Real.exp (R ^ 2 / 2)))
    (Filter.Eventually.of_forall fun y => ?_)).trans ?_
  · rw [Real.norm_eq_abs]
    have h := pt_diff hL hR u u' (x - y) (x' - y)
    have hd : dist ((u, x - y) : ℝ × Rd d) (u', x' - y) = dist (u, x) (u', x') := by
      simp only [Prod.dist_eq, dist_sub_right]
    rw [hd] at h
    exact h
  · simp only [Pi.add_apply]
    rw [integral_const_mul, integral_add g1.1 g2.1]
    calc L * dist (u, x) (u', x') * Real.exp (R ^ 2 / 2) *
          ((∫ y, Real.exp (-(‖x - y‖ ^ 2 / 2)) ∂Γ) + ∫ y, Real.exp (-(‖x' - y‖ ^ 2 / 2)) ∂Γ)
        ≤ L * dist (u, x) (u', x') * Real.exp (R ^ 2 / 2) * (gMass Γ + gMass Γ) :=
          mul_le_mul_of_nonneg_left (add_le_add g1.2 g2.2) hD
      _ = _ := by ring

end conv

/-- Auxiliary to the Lean proof route.  A control in `CPos` is bounded,
Lipschitz (`ContDiff.lipschitzWith_of_hasCompactSupport`) and spatially
supported in a ball. -/
theorem ctrl_data {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) :
    ∃ B L R : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ (∀ p, |Ψ p| ≤ B) ∧ (∀ p q, |Ψ p - Ψ q| ≤ L * dist p q) ∧
      (∀ u z, R < ‖z‖ → Ψ (u, z) = 0) := by
  obtain ⟨hs, hc, -, -, -⟩ := hΨ
  obtain ⟨B, hB⟩ := hs.continuous.bounded_above_of_compact_support hc
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) hc hs (by simp)
  obtain ⟨R, -, hR⟩ := exists_radius hc
  refine ⟨B, C, R, (norm_nonneg _).trans (hB 0), C.2, fun p => by simpa using hB p,
    fun p q => ?_, hR⟩
  have := hC.dist_le_mul p q
  rwa [Real.dist_eq] at this

/-- Nonnegativity of the mean (line 93: positive kernels), for every `s`,
`x`, `a` and every measure `Γ` (no integrability needed: a nonnegative
integrand has a nonnegative Bochner integral). -/
theorem mean_nonneg {Γ : Measure (Rd d)} {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) (a s : ℝ)
    (x : Rd d) : 0 ≤ mean a Γ Ψ s x :=
  setIntegral_nonneg measurableSet_Ioo fun _ _ =>
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (integral_nonneg fun _ => hΨ.2.2.2.1 _)

/-- Auxiliary to the Lean proof route.  `(Γ * Ψ(u,·))(x) = 0` for
`u ∉ (0,1)`. -/
theorem conv_eq_zero_of_time {Γ : Measure (Rd d)} {Ψ : ℝ × Rd d → ℝ}
    (ht : tsupport Ψ ⊆ Ioo (0 : ℝ) 1 ×ˢ univ) {u : ℝ} (hu : u ∉ Ioo (0 : ℝ) 1) (x : Rd d) :
    conv Γ (fun y => Ψ (u, y)) x = 0 := by
  simp only [conv, eq_zero_of_time ht hu, integral_zero]

/-- Auxiliary to the Lean proof route.  For `s ∈ [0,1]` and `r ∉ (-1,1)`,
`s - r ∉ (0,1)`. -/
theorem shift_mem {s r : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hr : r ∉ Ioo (-1 : ℝ) 1) :
    s - r ∉ Ioo (0 : ℝ) 1 := by
  intro h
  exact hr ⟨by linarith [h.2, hs.1], by linarith [h.1, hs.2]⟩

/-- The change of variables `r = s - u` of TeX lines 84-88: for
`s ∈ [0,1]`, `h_s(x) = ∫_{(-1,1)} |r|^{-a} (Γ * Ψ(s-r,·))(x) dr`
(an identity of Bochner integrals, unconditional; the TeX integrates over `ℝ`,
here the integrand vanishes outside `(-1,1)`). -/
theorem mean_eq_shift {Γ : Measure (Rd d)} {Ψ : ℝ × Rd d → ℝ}
    (ht : tsupport Ψ ⊆ Ioo (0 : ℝ) 1 ×ˢ univ) (a : ℝ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (x : Rd d) :
    mean a Γ Ψ s x = ∫ r in Ioo (-1 : ℝ) 1, |r| ^ (-a) * conv Γ (fun y => Ψ (s - r, y)) x := by
  set G : ℝ → ℝ := fun u => |s - u| ^ (-a) * conv Γ (fun y => Ψ (u, y)) x with hG
  have h1 : mean a Γ Ψ s x = ∫ u, G u := by
    rw [mean]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun u hu => by simp only [conv_eq_zero_of_time ht hu, mul_zero])
  have h2 : ∫ u, G u = ∫ r, G (s - r) := (integral_sub_left_eq_self G volume s).symm
  rw [h1, h2, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo (-1 : ℝ) 1) ?_]
  · refine setIntegral_congr_fun measurableSet_Ioo (fun r _ => ?_)
    simp only [hG, sub_sub_cancel]
  · intro r hr
    simp only [hG, conv_eq_zero_of_time ht (shift_mem hs hr), mul_zero]

/-- Auxiliary to the Lean proof route.  A continuous potential bounded by `M`
makes `V f²` integrable for every `f ∈ L²` (the `integrable_pot` side
condition of `WeakSobolev.IsRayleighTrial`). -/
theorem integrable_pot_of_bounded {V : Rd d → ℝ} (hV : Continuous V) {M : ℝ}
    (hM : ∀ x, |V x| ≤ M) {f : Rd d → ℝ} (hf : MemLp f 2 volume) :
    Integrable (fun x => V x * f x ^ 2) volume :=
  hf.integrable_sq.bdd_mul hV.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hM x)

section mean
variable {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
  (hsp : IsSpectralMeasure Γ μ)
include hΓt hμt hsp

/-- Auxiliary to the Lean proof route.  `(u,x) ↦ (Γ * Ψ(u,·))(x)` is
continuous (from `conv_lip`). -/
theorem convT_continuous {Ψ : ℝ × Rd d → ℝ} (hcont : Continuous Ψ) {B L R : ℝ}
    (hB : ∀ p, |Ψ p| ≤ B) (hL : ∀ p q, |Ψ p - Ψ q| ≤ L * dist p q)
    (hR : ∀ u z, R < ‖z‖ → Ψ (u, z) = 0) :
    Continuous (fun p : ℝ × Rd d => conv Γ (fun y => Ψ (p.1, y)) p.2) := by
  have hG := gMass_nonneg Γ
  have hL0 : 0 ≤ L := by
    have := hL (0, 0) (1, 0)
    have h1 : (0 : ℝ) < dist ((0 : ℝ), (0 : Rd d)) (1, 0) := by simp [Prod.dist_eq]
    by_contra h
    nlinarith [abs_nonneg (Ψ (0, 0) - Ψ (1, 0))]
  refine (LipschitzWith.of_dist_le_mul
    (K := Real.toNNReal (2 * L * Real.exp (R ^ 2 / 2) * gMass Γ)) fun p q => ?_).continuous
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  exact conv_lip hΓt hμt hsp hcont hB hL hR p.1 q.1 p.2 q.2

/-- Auxiliary to the Lean proof route.  The shifted integrand
`r ↦ |r|^{-a} (Γ * Ψ(s-r,·))(x)` is integrable on `(-1,1)` for `a < 1`. -/
theorem shift_integrableOn {Ψ : ℝ × Rd d → ℝ} (hcont : Continuous Ψ) {B L R : ℝ}
    (hB : ∀ p, |Ψ p| ≤ B) (hL : ∀ p q, |Ψ p - Ψ q| ≤ L * dist p q)
    (hR : ∀ u z, R < ‖z‖ → Ψ (u, z) = 0) {a : ℝ} (ha : a < 1) (s : ℝ) (x : Rd d) :
    IntegrableOn (fun r => |r| ^ (-a) * conv Γ (fun y => Ψ (s - r, y)) x) (Ioo (-1 : ℝ) 1) := by
  have hc := convT_continuous hΓt hμt hsp hcont hB hL hR
  refine (abs_rpow_integrableOn ha).mul_bdd (c := B * Real.exp (R ^ 2 / 2) * gMass Γ) ?_
    (ae_of_all _ fun r => ?_)
  · exact (hc.comp (by fun_prop : Continuous fun r : ℝ => (s - r, x))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact conv_le hΓt hμt hsp hB hR _ _

/-- The integrand of `h_s(x)` in `VariationalDilation.mean` is integrable on
`(0,1)` for `s ∈ [0,1]` and `a < 1` (so `h_s(x)` is a genuine integral). -/
theorem mean_integrableOn {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) {B L R : ℝ}
    (hB : ∀ p, |Ψ p| ≤ B) (hL : ∀ p q, |Ψ p - Ψ q| ≤ L * dist p q)
    (hR : ∀ u z, R < ‖z‖ → Ψ (u, z) = 0) {a : ℝ} (ha : a < 1) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (x : Rd d) :
    IntegrableOn (fun u => |s - u| ^ (-a) * conv Γ (fun y => Ψ (u, y)) x) (Ioo (0 : ℝ) 1) := by
  set H : ℝ → ℝ := fun r => |r| ^ (-a) * conv Γ (fun y => Ψ (s - r, y)) x with hHdef
  have hH : Integrable H := by
    rw [← integrableOn_iff_integrable_of_support_subset (s := Ioo (-1 : ℝ) 1)]
    · exact shift_integrableOn hΓt hμt hsp hΨ.1.continuous hB hL hR ha s x
    · intro r hr
      by_contra hr'
      apply hr
      simp only [hHdef, conv_eq_zero_of_time hΨ.2.2.1 (shift_mem hs hr'), mul_zero]
  have := ((integrable_comp_sub_left H s).2 hH).integrableOn (s := Ioo (0 : ℝ) 1)
  refine this.congr_fun (fun u _ => ?_) measurableSet_Ioo
  simp only [hHdef, sub_sub_cancel]

/-- The upper bound `h_s(x) ≤ B e^{R²/2} gMass Γ · 2/(1-a)` for
`s ∈ [0,1]` (TeX lines 89-92, the underived case). -/
theorem mean_le {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) {B L R : ℝ}
    (hB : ∀ p, |Ψ p| ≤ B) (hL : ∀ p q, |Ψ p - Ψ q| ≤ L * dist p q)
    (hR : ∀ u z, R < ‖z‖ → Ψ (u, z) = 0) {a : ℝ} (ha : a < 1) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (x : Rd d) :
    mean a Γ Ψ s x ≤ B * Real.exp (R ^ 2 / 2) * gMass Γ * (2 / (1 - a)) := by
  rw [mean_eq_shift hΨ.2.2.1 a hs x]
  calc ∫ r in Ioo (-1 : ℝ) 1, |r| ^ (-a) * conv Γ (fun y => Ψ (s - r, y)) x
      ≤ ∫ r in Ioo (-1 : ℝ) 1, |r| ^ (-a) * (B * Real.exp (R ^ 2 / 2) * gMass Γ) :=
        setIntegral_mono_on (shift_integrableOn hΓt hμt hsp hΨ.1.continuous hB hL hR ha s x)
          ((abs_rpow_integrableOn ha).mul_const _) measurableSet_Ioo fun r _ =>
            mul_le_mul_of_nonneg_left (le_of_abs_le (conv_le hΓt hμt hsp hB hR _ _))
              (Real.rpow_nonneg (abs_nonneg _) _)
    _ = _ := by rw [integral_mul_const, abs_rpow_integral ha]; ring

/-- The joint Lipschitz bound
`|h_s(x) - h_t(x')| ≤ 2 L e^{R²/2} gMass Γ · 2/(1-a) · dist((s,x),(t,x'))`
for `s, t ∈ [0,1]` (Lean route: the Lipschitz bound of `Ψ` under the integral
after the change of variables, instead of the TeX's bounded time
derivative, lines 93-94). -/
theorem mean_lip {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) {B L R : ℝ}
    (hB : ∀ p, |Ψ p| ≤ B) (hL : ∀ p q, |Ψ p - Ψ q| ≤ L * dist p q)
    (hR : ∀ u z, R < ‖z‖ → Ψ (u, z) = 0) {a : ℝ} (ha : a < 1) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (x x' : Rd d) :
    |mean a Γ Ψ s x - mean a Γ Ψ t x'| ≤
      2 * L * Real.exp (R ^ 2 / 2) * gMass Γ * (2 / (1 - a)) * dist (s, x) (t, x') := by
  have hcont := hΨ.1.continuous
  rw [mean_eq_shift hΨ.2.2.1 a hs x, mean_eq_shift hΨ.2.2.1 a ht x',
    ← integral_sub (shift_integrableOn hΓt hμt hsp hcont hB hL hR ha s x)
      (shift_integrableOn hΓt hμt hsp hcont hB hL hR ha t x')]
  set D := dist (s, x) (t, x') with hDdef
  refine (norm_integral_le_of_norm_le
    (f := fun r => |r| ^ (-a) * conv Γ (fun y => Ψ (s - r, y)) x -
      |r| ^ (-a) * conv Γ (fun y => Ψ (t - r, y)) x')
    ((abs_rpow_integrableOn ha).mul_const (2 * L * Real.exp (R ^ 2 / 2) * gMass Γ * D))
    (Filter.Eventually.of_forall fun r => ?_)).trans (le_of_eq ?_)
  · rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg r) _)]
    have h := conv_lip hΓt hμt hsp hcont hB hL hR (s - r) (t - r) x x'
    have hd : dist ((s - r, x) : ℝ × Rd d) (t - r, x') = D := by
      simp only [hDdef, Prod.dist_eq, dist_sub_right]
    rw [hd] at h
    exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (abs_nonneg _) _)
  · rw [integral_mul_const, abs_rpow_integral ha]; ring

end mean

/-! ### The manuscript's statements -/

/-- **`L:variational-heat-envelope`** (TeX lines 23-35) with the section's
standing hypotheses (line 4: a nonzero covariance satisfying `H:homog`): for
`ε > 0` and every `x`, `y ↦ p_ε(x-y)` is `Γ`-integrable (so `(Γ * p_ε)(x)` is
finite), `ξ ↦ e^{iξ·x} e^{-ε|ξ|²/2}` is `μ`-integrable,
`(Γ * p_ε)(x) = ∫ e^{iξ·x} e^{-ε|ξ|²/2} μ(dξ)`,
`0 ≤ (Γ * p_ε)(x) ≤ (Γ * p_ε)(0)`, and `(Γ * p_ε)(0) > 0`.  Of `H:homog`, only
the temperedness of `Γ` and `μ` and the spectral convention are used. -/
theorem variational_heat_envelope_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    (∀ x, Integrable (fun y => heatK ε (x - y)) Γ) ∧
    (∀ x, Integrable (fun ξ : Rd d => Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) *
        (Real.exp (-(ε * ‖ξ‖ ^ 2 / 2)) : ℂ)) μ) ∧
    (∀ x, ((conv Γ (heatK ε) x : ℝ) : ℂ) =
        ∫ ξ, Complex.exp (Complex.I * (inner ℝ ξ x : ℝ)) *
          (Real.exp (-(ε * ‖ξ‖ ^ 2 / 2)) : ℂ) ∂μ) ∧
    (∀ x, 0 ≤ conv Γ (heatK ε) x ∧ conv Γ (heatK ε) x ≤ conv Γ (heatK ε) 0) ∧
    0 < conv Γ (heatK ε) 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := heat_envelope hH.Γ_tempered hH.μ_tempered hH.spectral hε
  exact ⟨h1, h2, h3, h4, heat_conv_pos hH.Γ_tempered hΓ0 hε⟩

/-- **`L:variational-global-mean`**, general form of the display: for tempered
`Γ`, `μ` with the spectral convention, `Ψ ∈ CPos` and `a < 1`, there are
`M, C ≥ 0` such that every integrand defining `h_s(x)` is integrable
(`s ∈ [0,1]`), `0 ≤ h_s(x) ≤ M`, and
`|h_s(x) - h_t(x')| ≤ C dist((s,x),(t,x'))` for `s, t ∈ [0,1]`. -/
theorem global_mean {Γ μ : Measure (Rd d)} (hΓt : IsTempered Γ) (hμt : IsTempered μ)
    (hsp : IsSpectralMeasure Γ μ) {Ψ : ℝ × Rd d → ℝ} (hΨ : Ψ ∈ CPos d) {a : ℝ} (ha : a < 1) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧
      (∀ u x, Integrable (fun y => Ψ (u, x - y)) Γ) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ x,
        IntegrableOn (fun u => |s - u| ^ (-a) * conv Γ (fun y => Ψ (u, y)) x) (Ioo 0 1)) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ x, 0 ≤ mean a Γ Ψ s x ∧ mean a Γ Ψ s x ≤ M) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x x',
        |mean a Γ Ψ s x - mean a Γ Ψ t x'| ≤ C * dist (s, x) (t, x')) := by
  obtain ⟨B, L, R, hB0, hL0, hB, hL, hR⟩ := ctrl_data hΨ
  have hG := gMass_nonneg Γ
  have ha' : 0 < 1 - a := by linarith
  exact ⟨B * Real.exp (R ^ 2 / 2) * gMass Γ * (2 / (1 - a)),
    2 * L * Real.exp (R ^ 2 / 2) * gMass Γ * (2 / (1 - a)), by positivity, by positivity,
    conv_integrable hΓt hμt hsp hΨ.1.continuous hB hR,
    fun s hs x => mean_integrableOn hΓt hμt hsp hΨ hB hL hR ha hs x,
    fun s hs x => ⟨mean_nonneg hΨ a s x, mean_le hΓt hμt hsp hΨ hB hL hR ha hs x⟩,
    fun s hs t ht x x' => mean_lip hΓt hμt hsp hΨ hB hL hR ha hs ht x x'⟩

/-- Auxiliary to the Lean proof route.  `dist((s,x),(t,x)) = |s - t|`. -/
theorem dist_same_space (s t : ℝ) (x : Rd d) : dist (s, x) (t, x) = |s - t| := by
  rw [Prod.dist_eq, dist_self, Real.dist_eq]
  exact max_eq_left (abs_nonneg _)

/-- Auxiliary to the Lean proof route.  `dist((s,x),(s,x')) = dist(x,x')`. -/
theorem dist_same_time (s : ℝ) (x x' : Rd d) : dist (s, x) (s, x') = dist x x' := by
  rw [Prod.dist_eq, dist_self]
  exact max_eq_right dist_nonneg

/-- Auxiliary to the Lean proof route.  A spatial Lipschitz bound makes
`x ↦ h_s(x)` continuous. -/
theorem mean_continuous_of_lip {a : ℝ} {Γ : Measure (Rd d)} {Ψ : ℝ × Rd d → ℝ} {C s : ℝ}
    (hC : 0 ≤ C) (h : ∀ x x', |mean a Γ Ψ s x - mean a Γ Ψ s x'| ≤ C * dist (s, x) (s, x')) :
    Continuous (mean a Γ Ψ s) :=
  (LipschitzWith.of_dist_le_mul (K := Real.toNNReal C) fun x x' => by
    rw [Real.dist_eq, Real.coe_toNNReal _ hC, ← dist_same_time s x x']
    exact h x x').continuous

/-- **`L:variational-global-mean`** (TeX lines 64-74) with the section's
standing hypotheses (line 4: a nonzero covariance satisfying `H:homog`,
`a = α₀`), for `Ψ ∈ CPos` and `I = [0,1]`: there are real `M, C_Ψ ≥ 0` with
`E:variational-global-mean`, `0 ≤ h_s(x) ≤ M` and
`|h_s(x) - h_t(x)| ≤ C_Ψ |s - t|` for all `s, t ∈ I` and `x` (the sup-norm
bound, pointwise); every integrand in the definition of `h_s(x)` is
integrable; `x ↦ h_s(x)` is continuous; and `h_s f²` is integrable for every
`f ∈ L²`.  Narrower conclusion: the lemma's first sentence (every mixed
time/space derivative of `h_s` is globally bounded) is NOT formalized; only
its displayed consequence is.  `Γ ≠ 0` and the fields of `H:homog` other than
`Γ_tempered`, `μ_tempered`, `spectral`, `alpha0_lt_one` are carried, unused. -/
theorem variational_global_mean_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) :
    ∃ M CΨ : ℝ, 0 ≤ M ∧ 0 ≤ CΨ ∧
      (∀ u x, Integrable (fun y => Ψ (u, x - y)) Γ) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ x, IntegrableOn
        (fun u => |s - u| ^ (-alpha0) * conv Γ (fun y => Ψ (u, y)) x) (Ioo 0 1)) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ x, 0 ≤ mean alpha0 Γ Ψ s x ∧ mean alpha0 Γ Ψ s x ≤ M) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
        |mean alpha0 Γ Ψ s x - mean alpha0 Γ Ψ t x| ≤ CΨ * |s - t|) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, Continuous (mean alpha0 Γ Ψ s)) ∧
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ f : Rd d → ℝ, MemLp f 2 volume →
        Integrable (fun x => mean alpha0 Γ Ψ s x * f x ^ 2) volume) := by
  obtain ⟨M, C, hM, hC, h1, h2, h3, h4⟩ :=
    global_mean hH.Γ_tempered hH.μ_tempered hH.spectral hΨ hH.alpha0_lt_one
  have hcont : ∀ s ∈ Icc (0 : ℝ) 1, Continuous (mean alpha0 Γ Ψ s) := fun s hs =>
    mean_continuous_of_lip hC fun x x' => h4 s hs s hs x x'
  refine ⟨M, C, hM, hC, h1, h2, h3, fun s hs t ht x => ?_, hcont, fun s hs f hf => ?_⟩
  · rw [← dist_same_space s t x]
    exact h4 s hs t ht x x
  · refine integrable_pot_of_bounded (hcont s hs) (M := M) (fun x => ?_) hf
    rw [abs_of_nonneg (h3 s hs x).1]
    exact (h3 s hs x).2

/-- A first-order complement to `L:variational-global-mean` (not a TeX
statement; it follows from the bounded first derivatives asserted in the
lemma's first sentence): under the same hypotheses, `(s,x) ↦ h_s(x)` is
Lipschitz on `[0,1] × ℝ^d`. -/
theorem variational_global_mean_lipschitz_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (_hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x x',
      |mean alpha0 Γ Ψ s x - mean alpha0 Γ Ψ t x'| ≤ C * dist (s, x) (t, x') := by
  obtain ⟨-, C, -, hC, -, -, -, h4⟩ :=
    global_mean hH.Γ_tempered hH.μ_tempered hH.spectral hΨ hH.alpha0_lt_one
  exact ⟨C, hC, h4⟩

/-- The side condition `integrable_pot` of `WeakSobolev.IsRayleighTrial` is
automatic for the manuscript's potential: under the section's standing
hypotheses, for `Ψ ∈ CPos` and `s ∈ [0,1]`, a Rayleigh trial for `h_s` is
exactly a unit `f ∈ L²` with an `L²` weak gradient `g`. -/
theorem isRayleighTrial_mean_iff_paper {alpha alpha0 : ℝ} {Γ μ : Measure (Rd d)}
    (hH : HomogCovariance d alpha alpha0 Γ μ) (hΓ0 : Γ ≠ 0) {Ψ : ℝ × Rd d → ℝ}
    (hΨ : Ψ ∈ CPos d) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (f : Rd d → ℝ) (g : Rd d → Rd d) :
    WeakSobolev.IsRayleighTrial (mean alpha0 Γ Ψ s) f g ↔
      MemLp f 2 volume ∧ MemLp g 2 volume ∧ WeakSobolev.HasWeakGradient f g ∧
        ∫ x, f x ^ 2 = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hpot⟩ := variational_global_mean_paper hH hΓ0 hΨ
  constructor
  · intro h
    exact ⟨h.memLp_f, h.memLp_g, h.weakGrad, h.unit⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, h4, hpot s hs f h1⟩

end StratonovichHAMSecondMoment.VariationalMean
