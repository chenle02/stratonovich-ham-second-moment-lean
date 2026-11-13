module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:masked-temporal-modulation` (Modulated amplitudes) of
`notes/integrated_covariance_foundation.tex` (statement TeX lines 300-309,
display `E:masked-temporal-modulation` 303-307, proof 311-345), in
double-integral form, and a re-issued wrapper of Lemma `L:masked-trig-products`
(TeX lines 347-374) in which the supplied modulation input of
`MaskedTrigProducts.masked_trig_products_paper` is replaced by the norm
identity of `L:masked-time-completion`.

Statement formalized (`masked_temporal_modulation_paper`).  Standing
assumptions (TeX lines 296-298 and `L:masked-time-completion`): `T > 0`,
`0 < a < 1`, `I = [s, s+h] ⊆ [0, T]`, `0 < h ≤ 1`.  Lemma hypotheses:
`A ∈ C¹(I; ℂ)`, `M = sup_I |A|`, `D = sup_I |A'|`.  Conclusion, for every real
`ω`: the integrand of the complexified temporal form at
`F = 1_I A e^{iω·}` is integrable on `[0,T]²`, and
`|∫_0^T ∫_0^T F(t) conj F(u) |t-u|^{-a} du dt| ≤ C₀(a) h^{2-a} (M+hD)² ⟨hω⟩^{a-1}`,
`C₀(a) = 16/(1-a)`, the manuscript's constant.  The manuscript's left side is
the norm `‖1_I A e^{iωt}‖_a²` of the complexified completion `H_a^ℂ`; by the
complexification clause of `L:masked-time-completion` (TeX lines 153-154) this
norm is the double integral bounded here.  The completion itself is not
constructed; the bound is on the double integral, and nothing about `H_a` is
assumed for it.

Conventions and side conditions made explicit here:
* `A : ℝ → ℂ` (Lean convention); only its values on `I` enter, since every
  function is multiplied by the indicator of `I`.  `C¹(I; ℂ)` is
  `ContDiffOn ℝ 1 A I`; `A'` is `derivWithin A I`; `M`, `D` are `sSup` over
  `I` of `‖A‖` and `‖derivWithin A I‖`.  These suprema are finite (`I` compact,
  `A` and `A'` continuous on `I`; `envelope_of_contDiffOn`), so `sSup` does not
  take Lean's junk value.
* The kernel is `TimeSchur.kern a x = |x| ^ (-a)`; its diagonal value is
  irrelevant (null set).  The form is `TimeSchur.timeForm`, an iterated Bochner
  integral over `[0,T]²`; integrability of the integrand on the product is part
  of the conclusion, so the integral is not Lean's junk `0`.
* `⟨x⟩ = √(1+x²)` is `MaskedTrigProducts.bracket`, `C₀` is
  `MaskedTrigProducts.C₀`, the mode `1_I A e^{iωt}` is
  `MaskedTrigProducts.modeFn I A ω` (shared with `L:masked-trig-products`).
* `T > 0` and `h ≤ 1` are carried in the wrapper but not used: the bound is
  uniform in `T, s, h, A, ω` (TeX line 308).

Proof route (differs from the TeX proof; same statement and same constant).
* The TeX's `c(v) = ∫_s^{s+h-v} A(u+v) conj A(u) du` is represented as the
  autocorrelation `acorr Φ v = ∫_ℝ Φ(u+v) conj Φ(u) du`, `Φ = 1_I A` (equal for
  `0 ≤ v ≤ h`).  The TeX differentiates `c` at the moving endpoint; here no
  derivative of `c` is used.  Instead `|c(v)| ≤ M²(h-v)_+` (`acorr_bound`; it
  contains `c(h) = 0` and `|c| ≤ hM²`) and the Lipschitz bound
  `|c(v) - c(w)| ≤ (M² + hMD)|v - w|` (`acorr_lip`, the integrated form of the
  TeX's `|c'| ≤ M² + hMD`) are proved directly from the definition.
* The shear `u = t - v` and Fubini give `⟨F,F⟩_a = ∫_ℝ |v|^{-a} e^{iωv} c(v) dv`
  (`timeForm_eq_acorr`); `c(-v) = conj c(v)` splits it as `X + conj X`,
  `X = ∫_0^∞ v^{-a} e^{iωv} c(v) dv` (`integral_acorr_split`; the TeX's two
  conjugate triangles, lines 318-324).  Hence `|⟨F,F⟩_a| ≤ 2|X|`.
* Case `⟨hω⟩ ≤ 8` (contains the TeX's case `|ωh| ≤ 1`): `|X| ≤ M² h^{2-a}/(1-a)`
  (`crude_bound`) and `⟨hω⟩^{a-1} ≥ 1/8` (`constant_small`).
* Case `⟨hω⟩ > 8`, so `k = h|ω| > 7`: the TeX integrates by parts on `[1/k, 1]`
  (lines 331-342).  Here the oscillation is used through the half-period shift
  `v ↦ v + δ`, `δ = π/|ω|`, `e^{iωδ} = -1`, so `2X = ∫ (g(v) - g(v+δ)) e^{iωv}`
  with `g = 1_{v>0} v^{-a} c(v)` (`osc_bound`, with the explicit majorant
  `majorant` and `profile_sub_le`).  This gives
  `|X| ≤ K²(hδ^{1-a} + δh^{1-a})/(1-a)`, `K = M + hD`, and the constant check
  `4π · 8/7 ≤ 16` (`constant_large`) replaces the TeX's `8√2 ≤ 16`.

Re-issued `L:masked-trig-products` (`masked_trig_products_bridged_paper`):
the supplied input `hmod` of `masked_trig_products_paper` is discharged by
`masked_temporal_modulation_paper` through the supplied norm identity `hnorm`
(for `f ∈ V ∩ L²(0,T)`, `‖emb f‖² = Re ⟨f,f⟩_a`; TeX lines 153-154, extended to
`L²(0,T)` by lines 148-149 and 177-179).  `hmem` (TeX lines 154-155) stays
supplied.  `MaskedTrigProducts` itself is not modified.

Auxiliary to the Lean proof route (no direct manuscript label): every lemma
whose doc string says "Auxiliary", and `majorant`, `profile`, `phase`.
-/
public import Mathlib
public import StratonovichHAMSecondMoment.TimeSchur
public import StratonovichHAMSecondMoment.MaskedTrigProducts

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped ComplexConjugate

namespace StratonovichHAMSecondMoment.MaskedModulation

open StratonovichHAMSecondMoment.TimeSchur StratonovichHAMSecondMoment.MaskedTrigProducts

/-! ### Elementary integrals of `x^{-a}` (auxiliary to the Lean proof route) -/

/-- Auxiliary: `v ↦ (v + δ)^r` is interval integrable for `r > -1`. -/
theorem ii_rpow_shift {r : ℝ} (hr : -1 < r) (δ p q : ℝ) :
    IntervalIntegrable (fun v : ℝ => (v + δ) ^ r) volume p q := by
  have := (intervalIntegral.intervalIntegrable_rpow' (a := p + δ) (b := q + δ) hr).comp_add_right δ
  simpa using this

/-- Auxiliary: `∫_p^q (v + δ)^r dv = ((q+δ)^{r+1} - (p+δ)^{r+1})/(r+1)` for `r > -1`. -/
theorem integral_rpow_shift {r : ℝ} (hr : -1 < r) (δ p q : ℝ) :
    ∫ v in p..q, (v + δ) ^ r = ((q + δ) ^ (r + 1) - (p + δ) ^ (r + 1)) / (r + 1) := by
  rw [intervalIntegral.integral_comp_add_right (fun v : ℝ => v ^ r), integral_rpow (Or.inl hr)]

/-- Auxiliary: integrability on `Ioc p q` from interval integrability. -/
theorem integrable_indicator_Ioc {f : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hf : IntervalIntegrable f volume p q) : Integrable ((Ioc p q).indicator f) := by
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpq).mp hf).integrable_indicator
    measurableSet_Ioc

/-- Auxiliary: the integral of an indicator of `Ioc p q` is the interval integral. -/
theorem integral_indicator_Ioc (f : ℝ → ℝ) {p q : ℝ} (hpq : p ≤ q) :
    ∫ v, (Ioc p q).indicator f v = ∫ v in p..q, f v := by
  rw [integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le hpq]

/-! ### The oscillatory bound (shift by half a period) -/

/-- Auxiliary: the majorant of `|g(v) - g(v+δ)|` used in the shift argument. -/
def majorant (a h B L δ : ℝ) (v : ℝ) : ℝ :=
  (Ioc (-δ) 0).indicator (fun v => h * B * (v + δ) ^ (-a)) v +
    (Ioc 0 (h - δ)).indicator
      (fun v => h * B * (v ^ (-a) - (v + δ) ^ (-a)) + L * δ * (v + δ) ^ (-a)) v +
    (Ioc (h - δ) h).indicator (fun v => B * δ * v ^ (-a)) v

/-- Auxiliary: the majorant is integrable for `a < 1`, `0 < δ < h`. -/
theorem majorant_integrable {a h B L δ : ℝ} (ha1 : a < 1) (hδ0 : 0 < δ) (hδh : δ < h) :
    Integrable (majorant a h B L δ) := by
  have hr : -1 < -a := by linarith
  unfold majorant
  refine ((integrable_indicator_Ioc (by linarith) ?_).add
    (integrable_indicator_Ioc (by linarith) ?_)).add (integrable_indicator_Ioc (by linarith) ?_)
  · exact (ii_rpow_shift hr δ _ _).const_mul _
  · exact (((intervalIntegral.intervalIntegrable_rpow' hr).sub (ii_rpow_shift hr δ _ _)).const_mul
      _).add ((ii_rpow_shift hr δ _ _).const_mul _)
  · exact (intervalIntegral.intervalIntegrable_rpow' hr).const_mul _

/-- Auxiliary: `∫ majorant ≤ (2hBδ^{1-a} + (L+B)δh^{1-a})/(1-a)`. -/
theorem majorant_integral_le {a h B L δ : ℝ} (ha1 : a < 1) (hδ0 : 0 < δ) (hδh : δ < h)
    (hB : 0 ≤ B) (hL : 0 ≤ L) :
    ∫ v, majorant a h B L δ v ≤
      (2 * h * B * δ ^ (1 - a) + (L + B) * δ * h ^ (1 - a)) / (1 - a) := by
  have hr : -1 < -a := by linarith
  have h1a : 0 < 1 - a := by linarith
  have e : -a + 1 = 1 - a := by ring
  have i1 := integrable_indicator_Ioc (f := fun v => h * B * (v + δ) ^ (-a)) (p := -δ) (q := 0)
    (by linarith) ((ii_rpow_shift hr δ _ _).const_mul _)
  have i2 := integrable_indicator_Ioc
    (f := fun v => h * B * (v ^ (-a) - (v + δ) ^ (-a)) + L * δ * (v + δ) ^ (-a))
    (p := 0) (q := h - δ) (by linarith)
    ((((intervalIntegral.intervalIntegrable_rpow' hr).sub (ii_rpow_shift hr δ _ _)).const_mul
      _).add ((ii_rpow_shift hr δ _ _).const_mul _))
  have i3 := integrable_indicator_Ioc (f := fun v => B * δ * v ^ (-a)) (p := h - δ) (q := h)
    (by linarith) ((intervalIntegral.intervalIntegrable_rpow' hr).const_mul _)
  unfold majorant
  have s1 := integral_add (i1.add i2) i3
  have s2 := integral_add i1 i2
  simp only [Pi.add_apply] at s1 s2
  rw [s1, s2, integral_indicator_Ioc _ (by linarith),
    integral_indicator_Ioc _ (by linarith), integral_indicator_Ioc _ (by linarith)]
  rw [intervalIntegral.integral_const_mul, integral_rpow_shift hr,
    intervalIntegral.integral_add
      (((intervalIntegral.intervalIntegrable_rpow' hr).sub (ii_rpow_shift hr δ _ _)).const_mul _)
      ((ii_rpow_shift hr δ _ _).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_rpow' hr)
      (ii_rpow_shift hr δ _ _),
    integral_rpow (Or.inl hr), integral_rpow_shift hr, intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl hr)]
  simp only [e, neg_add_cancel, zero_add, sub_add_cancel]
  rw [Real.zero_rpow h1a.ne']
  have hP : (h - δ) ^ (1 - a) ≤ h ^ (1 - a) :=
    Real.rpow_le_rpow (by linarith) (by linarith) h1a.le
  have hP0 : 0 ≤ (h - δ) ^ (1 - a) := Real.rpow_nonneg (by linarith) _
  have hE0 : 0 ≤ δ ^ (1 - a) := Real.rpow_nonneg hδ0.le _
  have hh : 0 < h := hδ0.trans hδh
  have k1 : 0 ≤ h * B * (h ^ (1 - a) - (h - δ) ^ (1 - a)) :=
    mul_nonneg (mul_nonneg hh.le hB) (by linarith)
  have k2 : 0 ≤ L * δ * δ ^ (1 - a) := mul_nonneg (mul_nonneg hL hδ0.le) hE0
  have k3 : 0 ≤ B * δ * (h - δ) ^ (1 - a) := mul_nonneg (mul_nonneg hB hδ0.le) hP0
  rw [sub_zero, sub_zero]
  calc _ = (h * B * δ ^ (1 - a) + h * B * ((h - δ) ^ (1 - a) - (h ^ (1 - a) - δ ^ (1 - a))) +
        L * δ * (h ^ (1 - a) - δ ^ (1 - a)) + B * δ * (h ^ (1 - a) - (h - δ) ^ (1 - a))) /
        (1 - a) := by ring
    _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ h1a.le
        nlinarith

/-- Auxiliary: the truncated profile `g(v) = 1_{v > 0} v^{-a} C(v)`. -/
def profile (a : ℝ) (C : ℝ → ℂ) (v : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator (fun v => ((v ^ (-a) : ℝ) : ℂ) * C v) v

/-- Auxiliary: `‖(x^r : ℂ)‖ = x^r` for `x ≥ 0`. -/
theorem norm_ofReal_rpow {x : ℝ} (hx : 0 ≤ x) (r : ℝ) : ‖((x ^ r : ℝ) : ℂ)‖ = x ^ r := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx r)]

/-- Auxiliary: the pointwise shift estimate `‖g(v) - g(v+δ)‖ ≤ majorant(v)`, from
`‖C(v)‖ ≤ B (h - v)_+` for `v ≥ 0` and the Lipschitz bound of `C` on `[0,h]`. -/
theorem profile_sub_le {a h B L δ : ℝ} (ha0 : 0 < a) (hδ0 : 0 < δ) (hδh : δ < h) (hB : 0 ≤ B)
    (hL : 0 ≤ L) (C : ℝ → ℂ) (hCb : ∀ v, 0 ≤ v → ‖C v‖ ≤ B * max (h - v) 0)
    (hCl : ∀ v w, 0 ≤ v → v ≤ w → w ≤ h → ‖C v - C w‖ ≤ L * (w - v)) (v : ℝ) :
    ‖profile a C v - profile a C (v + δ)‖ ≤ majorant a h B L δ v := by
  have hh : 0 < h := hδ0.trans hδh
  have hC0 : ∀ w, h ≤ w → C w = 0 := by
    intro w hw
    have := hCb w (by linarith)
    rw [max_eq_right (by linarith), mul_zero] at this
    exact norm_le_zero_iff.mp this
  -- the three summands are nonnegative
  have t1 : ∀ v, 0 ≤ (Ioc (-δ) 0).indicator (fun v => h * B * (v + δ) ^ (-a)) v := fun v =>
    indicator_nonneg (fun v hv => by
      have : 0 ≤ (v + δ) ^ (-a) := Real.rpow_nonneg (by linarith [hv.1]) _
      positivity) v
  have t2 : ∀ v, 0 ≤ (Ioc 0 (h - δ)).indicator
      (fun v => h * B * (v ^ (-a) - (v + δ) ^ (-a)) + L * δ * (v + δ) ^ (-a)) v := fun v =>
    indicator_nonneg (fun v hv => by
      have h1 : (v + δ) ^ (-a) ≤ v ^ (-a) :=
        Real.rpow_le_rpow_of_nonpos hv.1 (by linarith) (by linarith)
      have h2 : 0 ≤ (v + δ) ^ (-a) := Real.rpow_nonneg (by linarith [hv.1]) _
      have h3 : 0 ≤ h * B * (v ^ (-a) - (v + δ) ^ (-a)) :=
        mul_nonneg (by positivity) (by linarith)
      positivity) v
  have t3 : ∀ v, 0 ≤ (Ioc (h - δ) h).indicator (fun v => B * δ * v ^ (-a)) v := fun v =>
    indicator_nonneg (fun v hv => by
      have : 0 ≤ v ^ (-a) := Real.rpow_nonneg (by linarith [hv.1]) _
      positivity) v
  unfold majorant
  rcases le_or_gt v (-δ) with hv | hv
  · -- both profiles vanish
    have e1 : profile a C v = 0 := indicator_of_notMem (by simp; linarith) _
    have e2 : profile a C (v + δ) = 0 := indicator_of_notMem (by simp; linarith) _
    rw [e1, e2, sub_zero, norm_zero]
    linarith [t1 v, t2 v, t3 v]
  rcases le_or_gt v 0 with hv' | hv'
  · -- `-δ < v ≤ 0`
    have e1 : profile a C v = 0 := indicator_of_notMem (by simp; linarith) _
    have e2 : profile a C (v + δ) = ((v + δ) ^ (-a) : ℝ) * C (v + δ) :=
      indicator_of_mem (show v + δ ∈ Ioi 0 by simp; linarith) _
    have e3 : (Ioc (-δ) 0).indicator (fun v => h * B * (v + δ) ^ (-a)) v =
        h * B * (v + δ) ^ (-a) :=
      indicator_of_mem (show v ∈ Ioc (-δ) 0 from ⟨hv, hv'⟩) _
    rw [e1, e2, e3, zero_sub, norm_neg, norm_mul, norm_ofReal_rpow (by linarith)]
    have hc := hCb (v + δ) (by linarith)
    have hmax : max (h - (v + δ)) 0 ≤ h := max_le (by linarith) hh.le
    have hp : 0 ≤ (v + δ) ^ (-a) := Real.rpow_nonneg (by linarith) _
    have : ‖C (v + δ)‖ ≤ h * B := by nlinarith
    nlinarith [t2 v, t3 v]
  rcases le_or_gt v (h - δ) with hv2 | hv2
  · -- `0 < v ≤ h - δ`
    have e1 : profile a C v = ((v ^ (-a) : ℝ) : ℂ) * C v := indicator_of_mem (show v ∈ Ioi 0 from hv') _
    have e2 : profile a C (v + δ) = ((v + δ) ^ (-a) : ℝ) * C (v + δ) :=
      indicator_of_mem (show v + δ ∈ Ioi 0 by simp; linarith) _
    have e3 : (Ioc 0 (h - δ)).indicator
        (fun v => h * B * (v ^ (-a) - (v + δ) ^ (-a)) + L * δ * (v + δ) ^ (-a)) v =
        h * B * (v ^ (-a) - (v + δ) ^ (-a)) + L * δ * (v + δ) ^ (-a) :=
      indicator_of_mem (show v ∈ Ioc 0 (h - δ) from ⟨hv', hv2⟩) _
    rw [e1, e2, e3]
    have split : ((v ^ (-a) : ℝ) : ℂ) * C v - ((v + δ) ^ (-a) : ℝ) * C (v + δ) =
        ((v ^ (-a) - (v + δ) ^ (-a) : ℝ) : ℂ) * C v + (((v + δ) ^ (-a) : ℝ) : ℂ) * (C v - C (v + δ)) := by
      push_cast; ring
    have hmono : (v + δ) ^ (-a) ≤ v ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos hv' (by linarith) (by linarith)
    have hp : 0 ≤ (v + δ) ^ (-a) := Real.rpow_nonneg (by linarith) _
    rw [split]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      norm_ofReal_rpow (by linarith)]
    have hc := hCb v hv'.le
    have hmax : max (h - v) 0 ≤ h := max_le (by linarith) hh.le
    have hc' : ‖C v‖ ≤ h * B := by nlinarith
    have hl := hCl v (v + δ) hv'.le (by linarith) (by linarith)
    rw [add_sub_cancel_left] at hl
    have k1 : (v ^ (-a) - (v + δ) ^ (-a)) * ‖C v‖ ≤ (v ^ (-a) - (v + δ) ^ (-a)) * (h * B) :=
      mul_le_mul_of_nonneg_left hc' (by linarith)
    have k2 : (v + δ) ^ (-a) * ‖C v - C (v + δ)‖ ≤ (v + δ) ^ (-a) * (L * δ) :=
      mul_le_mul_of_nonneg_left hl hp
    nlinarith [t1 v, t3 v]
  rcases le_or_gt v h with hv3 | hv3
  · -- `h - δ < v ≤ h`
    have hvpos : 0 < v := by linarith
    have e1 : profile a C v = ((v ^ (-a) : ℝ) : ℂ) * C v :=
      indicator_of_mem (show v ∈ Ioi 0 from hvpos) _
    have e2 : profile a C (v + δ) = 0 := by
      unfold profile
      rw [indicator_of_mem (show v + δ ∈ Ioi (0 : ℝ) by simp; linarith),
        hC0 (v + δ) (by linarith), mul_zero]
    have e3 : (Ioc (h - δ) h).indicator (fun v => B * δ * v ^ (-a)) v = B * δ * v ^ (-a) :=
      indicator_of_mem (show v ∈ Ioc (h - δ) h from ⟨hv2, hv3⟩) _
    rw [e1, e2, e3, sub_zero, norm_mul, norm_ofReal_rpow hvpos.le]
    have hc := hCb v hvpos.le
    rw [max_eq_left (by linarith)] at hc
    have hp : 0 ≤ v ^ (-a) := Real.rpow_nonneg hvpos.le _
    have : ‖C v‖ ≤ B * δ := hc.trans (mul_le_mul_of_nonneg_left (by linarith) hB)
    nlinarith [t1 v, t2 v]
  · -- `v > h`
    have e1 : profile a C v = 0 := by
      unfold profile
      rw [indicator_of_mem (show v ∈ Ioi (0 : ℝ) by simp; linarith), hC0 v hv3.le, mul_zero]
    have e2 : profile a C (v + δ) = 0 := by
      unfold profile
      rw [indicator_of_mem (show v + δ ∈ Ioi (0 : ℝ) by simp; linarith),
        hC0 (v + δ) (by linarith), mul_zero]
    rw [e1, e2, sub_zero, norm_zero]
    linarith [t1 v, t2 v, t3 v]

/-- Auxiliary: the phase `t ↦ e^{iωt}`. -/
def phase (ω t : ℝ) : ℂ := Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I)

/-- Auxiliary: `|e^{iωt}| = 1`. -/
theorem norm_phase (ω t : ℝ) : ‖phase ω t‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- Auxiliary: the phase is continuous. -/
theorem continuous_phase (ω : ℝ) : Continuous (phase ω) := by
  unfold phase
  fun_prop

/-- Auxiliary: `e^{iω(t+u)} = e^{iωt} e^{iωu}`. -/
theorem phase_add (ω t u : ℝ) : phase ω (t + u) = phase ω t * phase ω u := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Auxiliary (oscillatory bound by a half-period shift; replaces the TeX's
integration by parts, see the module doc).  Let `0 < a < 1`, `0 < δ < h`,
`B, L ≥ 0`, `C : ℝ → ℂ` a.e.-strongly measurable with `‖C(v)‖ ≤ B (h-v)_+` for
`v ≥ 0` and `‖C(v) - C(w)‖ ≤ L (w - v)` for `0 ≤ v ≤ w ≤ h`, and `ω` with
`e^{iωδ} = -1`.  Then
`‖∫_0^∞ v^{-a} e^{iωv} C(v) dv‖ ≤ (2hBδ^{1-a} + (L+B)δh^{1-a}) / (2(1-a))`. -/
theorem osc_bound {a h B L δ : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hδ0 : 0 < δ) (hδh : δ < h)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (C : ℝ → ℂ) (hCm : AEStronglyMeasurable C volume)
    (hCb : ∀ v, 0 ≤ v → ‖C v‖ ≤ B * max (h - v) 0)
    (hCl : ∀ v w, 0 ≤ v → v ≤ w → w ≤ h → ‖C v - C w‖ ≤ L * (w - v))
    (ω : ℝ) (hω : phase ω δ = -1) :
    ‖∫ v in Ioi 0, ((v ^ (-a) : ℝ) : ℂ) * phase ω v * C v‖ ≤
      (2 * h * B * δ ^ (1 - a) + (L + B) * δ * h ^ (1 - a)) / (2 * (1 - a)) := by
  have hh : 0 < h := hδ0.trans hδh
  have hr : -1 < -a := by linarith
  have h1a : 0 < 1 - a := by linarith
  set g := profile a C
  -- integrability of the profile
  have hgm : AEStronglyMeasurable g volume := by
    refine AEStronglyMeasurable.indicator ?_ measurableSet_Ioi
    exact (Complex.continuous_ofReal.measurable.comp
      (measurable_id.pow_const _)).aestronglyMeasurable.mul hCm
  have hbd : Integrable ((Ioc 0 h).indicator fun v => v ^ (-a) * (B * h)) :=
    integrable_indicator_Ioc hh.le ((intervalIntegral.intervalIntegrable_rpow' hr).mul_const _)
  have hgi : Integrable g := by
    refine hbd.mono' hgm (ae_of_all _ fun v => ?_)
    rcases le_or_gt v 0 with hv | hv
    · have e1 : g v = 0 := indicator_of_notMem (by simp; linarith) _
      rw [e1, norm_zero]
      exact indicator_nonneg (fun v hv => mul_nonneg (Real.rpow_nonneg hv.1.le _)
        (mul_nonneg hB hh.le)) v
    rcases le_or_gt v h with hv' | hv'
    · have e1 : g v = ((v ^ (-a) : ℝ) : ℂ) * C v := indicator_of_mem (show v ∈ Ioi 0 from hv) _
      rw [e1, indicator_of_mem (show v ∈ Ioc 0 h from ⟨hv, hv'⟩), norm_mul,
        norm_ofReal_rpow hv.le]
      have hc := hCb v hv.le
      have hmax : max (h - v) 0 ≤ h := max_le (by linarith) hh.le
      have : ‖C v‖ ≤ B * h := hc.trans (mul_le_mul_of_nonneg_left hmax hB)
      exact mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hv.le _)
    · have hc := hCb v hv.le
      rw [max_eq_right (by linarith), mul_zero] at hc
      have e1 : g v = 0 := by
        change (Ioi (0 : ℝ)).indicator _ v = 0
        rw [indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv), norm_le_zero_iff.mp hc, mul_zero]
      rw [e1, norm_zero]
      exact indicator_nonneg (fun v hv => mul_nonneg (Real.rpow_nonneg hv.1.le _)
        (mul_nonneg hB hh.le)) v
  have hpm : AEStronglyMeasurable (phase ω) volume := (continuous_phase ω).aestronglyMeasurable
  have hpb : ∀ᵐ v ∂volume, ‖phase ω v‖ ≤ 1 := ae_of_all _ fun v => (norm_phase ω v).le
  have hge : Integrable fun v => g v * phase ω v := hgi.mul_bdd hpm hpb
  have hge' : Integrable fun v => g (v + δ) * phase ω v := (hgi.comp_add_right δ).mul_bdd hpm hpb
  -- the integral is that of `g e`
  have hX : ∫ v in Ioi 0, ((v ^ (-a) : ℝ) : ℂ) * phase ω v * C v = ∫ v, g v * phase ω v := by
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    by_cases hv : v ∈ Ioi (0 : ℝ)
    · simp only [g, profile, indicator_of_mem hv]
      ring
    · simp only [g, profile, indicator_of_notMem hv, zero_mul]
  -- the shift
  have hshift : ∫ v, g v * phase ω v = -∫ v, g (v + δ) * phase ω v := by
    rw [← integral_add_right_eq_self (fun v => g v * phase ω v) δ, ← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only [phase_add, hω]
    ring
  have h2 : 2 * ∫ v, g v * phase ω v = ∫ v, (g v - g (v + δ)) * phase ω v := by
    simp_rw [sub_mul]
    rw [integral_sub hge hge']
    nth_rewrite 1 [two_mul]
    nth_rewrite 2 [hshift]
    ring
  have hnorm : ‖∫ v, (g v - g (v + δ)) * phase ω v‖ ≤ ∫ v, majorant a h B L δ v := by
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (ae_of_all _ fun v => norm_nonneg _)
      (majorant_integrable ha1 hδ0 hδh) (ae_of_all _ fun v => ?_)
    simp only [norm_mul, norm_phase, mul_one]
    exact profile_sub_le ha0 hδ0 hδh hB hL C hCb hCl v
  have hm := majorant_integral_le (a := a) (B := B) (L := L) ha1 hδ0 hδh hB hL
  rw [hX]
  have : ‖(2 : ℂ) * ∫ v, g v * phase ω v‖ = 2 * ‖∫ v, g v * phase ω v‖ := by
    rw [norm_mul]; norm_num
  rw [h2] at this
  have k := hnorm.trans hm
  rw [this] at k
  have e : (2 * h * B * δ ^ (1 - a) + (L + B) * δ * h ^ (1 - a)) / (2 * (1 - a)) =
      ((2 * h * B * δ ^ (1 - a) + (L + B) * δ * h ^ (1 - a)) / (1 - a)) / 2 := by
    rw [div_div, mul_comm (1 - a) 2]
  rw [e]
  linarith

/-! ### The autocorrelation `c(v)` -/

/-- The autocorrelation `c(v) = ∫ Φ(u+v) conj Φ(u) du` over `ℝ`.  For
`Φ = 1_I A` with `I = [s, s+h]` and `0 ≤ v ≤ h` it is the TeX's
`c(v) = ∫_s^{s+h-v} A(u+v) conj A(u) du` (TeX line 312). -/
def acorr (Φ : ℝ → ℂ) (v : ℝ) : ℂ := ∫ u, Φ (u + v) * conj (Φ u)

section Acorr

variable {Φ : ℝ → ℂ} {s h M D : ℝ}

/-- Auxiliary: a bound `‖Φ‖ ≤ M` forces `M ≥ 0`. -/
theorem M_nonneg_of_bound (hΦb : ∀ u, ‖Φ u‖ ≤ M) : 0 ≤ M := (norm_nonneg _).trans (hΦb 0)

/-- Auxiliary: for `Φ` measurable, bounded by `M` and vanishing outside
`[s, s+h]`, the integrand of `acorr Φ v` is integrable. -/
theorem acorr_integrable (hΦm : Measurable Φ) (hΦ0 : ∀ u ∉ Icc s (s + h), Φ u = 0)
    (hΦb : ∀ u, ‖Φ u‖ ≤ M) (v : ℝ) : Integrable (fun u => Φ (u + v) * conj (Φ u)) := by
  have hM := M_nonneg_of_bound hΦb
  refine Integrable.mono' (g := (Icc s (s + h)).indicator (fun _ => M * M)) ?_ ?_ ?_
  · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  · exact ((hΦm.comp (measurable_add_const v)).mul
      (Complex.continuous_conj.measurable.comp hΦm)).aestronglyMeasurable
  · refine ae_of_all _ fun u => ?_
    by_cases hu : u ∈ Icc s (s + h)
    · rw [indicator_of_mem hu, norm_mul, Complex.norm_conj]
      exact mul_le_mul (hΦb _) (hΦb _) (norm_nonneg _) hM
    · rw [indicator_of_notMem hu, hΦ0 u hu, map_zero, mul_zero, norm_zero]

/-- Auxiliary: pointwise bound of the integrand of `acorr Φ v` by
`M² 1_{[s, s+h-v]}`. -/
theorem acorr_integrand_le (hΦ0 : ∀ u ∉ Icc s (s + h), Φ u = 0) (hΦb : ∀ u, ‖Φ u‖ ≤ M)
    (v u : ℝ) :
    ‖Φ (u + v) * conj (Φ u)‖ ≤ (Icc s (s + h - v)).indicator (fun _ => M * M) u := by
  have hM := M_nonneg_of_bound hΦb
  by_cases hu : u ∈ Icc s (s + h - v)
  · rw [indicator_of_mem hu, norm_mul, Complex.norm_conj]
    exact mul_le_mul (hΦb _) (hΦb _) (norm_nonneg _) hM
  · rw [indicator_of_notMem hu]
    have : Φ (u + v) = 0 ∨ Φ u = 0 := by
      by_contra hc
      obtain ⟨hc1, hc2⟩ := not_or.mp hc
      have h1 : u + v ∈ Icc s (s + h) := by
        by_contra h'
        exact hc1 (hΦ0 _ h')
      have h2 : u ∈ Icc s (s + h) := by
        by_contra h'
        exact hc2 (hΦ0 _ h')
      exact hu ⟨h2.1, by linarith [h1.2]⟩
    rcases this with h0 | h0 <;> simp [h0]

/-- Auxiliary: `|c(v)| ≤ M² (h - v)_+` for every real `v` (TeX line 318 states
`|c(v)| ≤ hM²` for `0 ≤ v ≤ h`, and `c(h) = 0`). -/
theorem acorr_bound (hΦ0 : ∀ u ∉ Icc s (s + h), Φ u = 0)
    (hΦb : ∀ u, ‖Φ u‖ ≤ M) (v : ℝ) :
    ‖acorr Φ v‖ ≤ M * M * max (h - v) 0 := by
  have hM := M_nonneg_of_bound hΦb
  have hi : Integrable ((Icc s (s + h - v)).indicator (fun _ => M * M)) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  refine (norm_integral_le_of_norm_le hi (ae_of_all _ (acorr_integrand_le hΦ0 hΦb v))).trans ?_
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc, smul_eq_mul]
  have : s + h - v - s = h - v := by ring
  rw [this, mul_comm]

/-- Auxiliary: the Lipschitz bound `|c(v) - c(w)| ≤ (M² + hMD)(w - v)` for
`0 ≤ v ≤ w` (TeX line 318 states `|c'(v)| ≤ M² + hMD`; here no derivative of `c`
is used). -/
theorem acorr_lip (hΦm : Measurable Φ) (hΦ0 : ∀ u ∉ Icc s (s + h), Φ u = 0)
    (hΦb : ∀ u, ‖Φ u‖ ≤ M)
    (hΦl : ∀ x ∈ Icc s (s + h), ∀ y ∈ Icc s (s + h), ‖Φ x - Φ y‖ ≤ D * |x - y|)
    (hh : 0 ≤ h) (hD : 0 ≤ D) {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w) :
    ‖acorr Φ v - acorr Φ w‖ ≤ (M * M + h * M * D) * (w - v) := by
  have hM := M_nonneg_of_bound hΦb
  unfold acorr
  rw [← integral_sub (acorr_integrable hΦm hΦ0 hΦb v) (acorr_integrable hΦm hΦ0 hΦb w)]
  have hi1 : Integrable ((Icc s (s + h)).indicator (fun _ => M * D * (w - v))) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hi2 : Integrable ((Ioc (s + h - w) (s + h - v)).indicator (fun _ => M * M)) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc
  have hpt : ∀ u, ‖Φ (u + v) * conj (Φ u) - Φ (u + w) * conj (Φ u)‖ ≤
      (Icc s (s + h)).indicator (fun _ => M * D * (w - v)) u +
        (Ioc (s + h - w) (s + h - v)).indicator (fun _ => M * M) u := by
    intro u
    have n1 : 0 ≤ (Icc s (s + h)).indicator (fun _ => M * D * (w - v)) u :=
      indicator_nonneg (fun _ _ => mul_nonneg (mul_nonneg hM hD) (by linarith)) u
    have n2 : 0 ≤ (Ioc (s + h - w) (s + h - v)).indicator (fun _ => M * M) u :=
      indicator_nonneg (fun _ _ => mul_nonneg hM hM) u
    by_cases hu : u ∈ Icc s (s + h)
    · by_cases hw : u + w ∈ Icc s (s + h)
      · have hvI : u + v ∈ Icc s (s + h) := ⟨by linarith [hu.1], by linarith [hw.2]⟩
        rw [← sub_mul, norm_mul, Complex.norm_conj, indicator_of_mem hu]
        have hl := hΦl _ hvI _ hw
        have e : |u + v - (u + w)| = w - v := by
          rw [show u + v - (u + w) = -(w - v) by ring, abs_neg, abs_of_nonneg (by linarith)]
        rw [e] at hl
        have : ‖Φ (u + v) - Φ (u + w)‖ * ‖Φ u‖ ≤ D * (w - v) * M :=
          mul_le_mul hl (hΦb u) (norm_nonneg _) ((norm_nonneg _).trans hl)
        nlinarith
      · rw [hΦ0 _ hw, zero_mul, sub_zero]
        by_cases hv' : u + v ∈ Icc s (s + h)
        · have hmem : u ∈ Ioc (s + h - w) (s + h - v) := by
            refine ⟨?_, by linarith [hv'.2]⟩
            by_contra hc
            exact hw ⟨by linarith [hu.1], by linarith⟩
          rw [indicator_of_mem hmem, norm_mul, Complex.norm_conj]
          have := mul_le_mul (hΦb (u + v)) (hΦb u) (norm_nonneg _) hM
          linarith
        · rw [hΦ0 _ hv', zero_mul, norm_zero]
          linarith
    · rw [hΦ0 u hu, map_zero, mul_zero, mul_zero, sub_zero, norm_zero]
      linarith
  refine (norm_integral_le_of_norm_le (hi1.add hi2) (ae_of_all _ hpt)).trans ?_
  rw [integral_add' hi1 hi2, integral_indicator_const _ measurableSet_Icc,
    integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Icc, Real.volume_real_Ioc,
    smul_eq_mul, smul_eq_mul]
  rw [show s + h - s = h by ring, show s + h - v - (s + h - w) = w - v by ring,
    max_eq_left hh, max_eq_left (by linarith)]
  apply le_of_eq
  ring

/-- Auxiliary: `c(-v) = conj c(v)` (no hypothesis on `Φ`: for a non-integrable
integrand both sides are Lean's `0`, consistently). -/
theorem acorr_neg (v : ℝ) : acorr Φ (-v) = conj (acorr Φ v) := by
  unfold acorr
  rw [← integral_conj, ← integral_add_right_eq_self (fun u => Φ (u + -v) * conj (Φ u)) v]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [add_neg_cancel_right, map_mul, Complex.conj_conj]
  ring

/-- Auxiliary: `|c(v)| ≤ M² (h - |v|)_+` for every real `v`. -/
theorem acorr_bound_abs (hΦ0 : ∀ u ∉ Icc s (s + h), Φ u = 0)
    (hΦb : ∀ u, ‖Φ u‖ ≤ M) (v : ℝ) :
    ‖acorr Φ v‖ ≤ M * M * max (h - |v|) 0 := by
  rcases le_total 0 v with hv | hv
  · rw [abs_of_nonneg hv]
    exact acorr_bound hΦ0 hΦb v
  · rw [abs_of_nonpos hv]
    have := acorr_bound hΦ0 hΦb (-v)
    rwa [acorr_neg, Complex.norm_conj] at this

/-- Auxiliary: `c` is strongly measurable for measurable `Φ`. -/
theorem acorr_stronglyMeasurable (hΦm : Measurable Φ) : StronglyMeasurable (acorr Φ) := by
  have hf : StronglyMeasurable fun p : ℝ × ℝ => Φ (p.2 + p.1) * conj (Φ p.2) :=
    ((hΦm.comp (measurable_snd.add measurable_fst)).mul
      (Complex.continuous_conj.measurable.comp (hΦm.comp measurable_snd))).stronglyMeasurable
  exact hf.integral_prod_right'

end Acorr

/-! ### Reduction of the double integral to a one-sided oscillatory integral -/

/-- Auxiliary: `e^{iωt} conj e^{iωt} = 1`. -/
theorem phase_mul_conj (ω t : ℝ) : phase ω t * conj (phase ω t) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phase]
  simp

/-- Auxiliary: `e^{-iωt} = conj e^{iωt}`. -/
theorem phase_neg (ω t : ℝ) : phase ω (-t) = conj (phase ω t) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Auxiliary: the kernel `|v|^{-a}` is integrable on `[-h, h]` for `a < 1`. -/
theorem integrable_kern_indicator {a : ℝ} (ha1 : a < 1) (h : ℝ) (hh : 0 ≤ h) :
    Integrable ((Icc (-h) h).indicator (kern a)) := by
  have hr : -1 < -a := by linarith
  have := (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : -h ≤ h)).mp
    (intervalIntegrable_abs_rpow hr (-h) h)
  exact this.integrable_indicator measurableSet_Icc

section Identity

variable {Φ : ℝ → ℂ} {s h M : ℝ}

/-- Auxiliary: integrability of `(t, v) ↦ F(t) conj F(t-v) |v|^{-a}` on `ℝ²`,
`F = Φ e^{iω·}`. -/
theorem shear_integrable {a : ℝ} (ha1 : a < 1) (hΦm : Measurable Φ)
    (hΦ0 : ∀ u ∉ Icc s (s + h), Φ u = 0) (hΦb : ∀ u, ‖Φ u‖ ≤ M) (hh : 0 ≤ h) (ω : ℝ) :
    Integrable (fun p : ℝ × ℝ => Φ p.1 * phase ω p.1 * conj (Φ (p.1 - p.2) * phase ω (p.1 - p.2)) *
      ((kern a p.2 : ℝ) : ℂ)) (volume.prod volume) := by
  have hM := M_nonneg_of_bound hΦb
  have hF : Measurable fun t => Φ t * phase ω t := hΦm.mul (continuous_phase ω).measurable
  have hb : Integrable (fun p : ℝ × ℝ => (Icc s (s + h)).indicator (fun _ => M * M) p.1 *
      (Icc (-h) h).indicator (kern a) p.2) (volume.prod volume) :=
    ((continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc).mul_prod
      (integrable_kern_indicator ha1 h hh)
  refine hb.mono' ?_ (ae_of_all _ fun p => ?_)
  · exact (((hF.comp measurable_fst).mul (Complex.continuous_conj.measurable.comp
      (hF.comp (measurable_fst.sub measurable_snd)))).mul
      (Complex.continuous_ofReal.measurable.comp
        ((measurable_kern a).comp measurable_snd))).aestronglyMeasurable
  · obtain ⟨t, v⟩ := p
    simp only
    by_cases ht : t ∈ Icc s (s + h)
    · by_cases htv : t - v ∈ Icc s (s + h)
      · have hv : v ∈ Icc (-h) h :=
          ⟨by linarith [ht.1, htv.2], by linarith [ht.2, htv.1]⟩
        rw [indicator_of_mem ht, indicator_of_mem hv, norm_mul, norm_mul, norm_mul,
          Complex.norm_conj, norm_mul, norm_phase, norm_phase, mul_one, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (kern_nonneg a v)]
        exact mul_le_mul_of_nonneg_right (mul_le_mul (hΦb _) (hΦb _) (norm_nonneg _) hM)
          (kern_nonneg a v)
      · rw [hΦ0 _ htv]
        simp only [zero_mul, map_zero, mul_zero, zero_mul, norm_zero]
        exact mul_nonneg (indicator_nonneg (fun _ _ => mul_nonneg hM hM) _)
          (indicator_nonneg (fun v _ => kern_nonneg a v) _)
    · rw [hΦ0 _ ht]
      simp only [zero_mul, norm_zero]
      exact mul_nonneg (indicator_nonneg (fun _ _ => mul_nonneg hM hM) _)
        (indicator_nonneg (fun v _ => kern_nonneg a v) _)

/-- Auxiliary (the convolution form of the double integral): for `Φ` measurable,
bounded by `M`, vanishing outside `I = [s, s+h] ⊆ [0, T]`, and `F = Φ e^{iω·}`,
`∫_0^T ∫_0^T F(t) conj F(u) |t-u|^{-a} du dt = ∫_ℝ |v|^{-a} e^{iωv} c(v) dv`. -/
theorem timeForm_eq_acorr {a T : ℝ} (ha1 : a < 1) (hΦm : Measurable Φ)
    (hΦ0 : ∀ u ∉ Icc s (s + h), Φ u = 0) (hΦb : ∀ u, ‖Φ u‖ ≤ M) (hh : 0 ≤ h)
    (hsupp : Icc s (s + h) ⊆ Icc 0 T) (ω : ℝ) :
    timeForm a T (fun t => Φ t * phase ω t) (fun t => Φ t * phase ω t) =
      ∫ v, ((kern a v : ℝ) : ℂ) * (phase ω v * acorr Φ v) := by
  set F : ℝ → ℂ := fun t => Φ t * phase ω t with hFdef
  set H : ℝ → ℝ → ℂ := fun t u => F t * conj (F u) * ((kern a (t - u) : ℝ) : ℂ) with hHdef
  have hF0 : ∀ t ∉ Icc 0 T, F t = 0 := fun t ht => by
    simp only [F, hΦ0 t (fun h' => ht (hsupp h')), zero_mul]
  have inner : ∀ t, ∫ u in Icc 0 T, H t u = ∫ u, H t u := fun t =>
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => by
      simp only [H, hF0 u hu, map_zero, mul_zero, zero_mul])
  have step1 : timeForm a T F F = ∫ t, ∫ u, H t u := by
    show ∫ t in Icc 0 T, ∫ u in Icc 0 T, H t u = _
    simp_rw [inner]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => by
      simp only [H, hF0 t ht, zero_mul, integral_zero])
  have step2 : ∀ t, ∫ u, H t u = ∫ v, H t (t - v) := fun t =>
    (integral_sub_left_eq_self (fun u => H t u) volume t).symm
  have hint : Integrable (Function.uncurry fun t v => H t (t - v)) (volume.prod volume) := by
    have := shear_integrable ha1 hΦm hΦ0 hΦb hh ω (a := a)
    refine this.congr (ae_of_all _ fun p => ?_)
    obtain ⟨t, v⟩ := p
    simp only [Function.uncurry_apply_pair, H, F, sub_sub_cancel]
  have step4 : ∀ v, ∫ t, H t (t - v) = ((kern a v : ℝ) : ℂ) * (phase ω v * acorr Φ v) := by
    intro v
    simp only [H, sub_sub_cancel]
    rw [integral_mul_const, ← integral_add_right_eq_self
      (fun t => F t * conj (F (t - v))) v]
    simp only [add_sub_cancel_right, F]
    have : ∀ u, Φ (u + v) * phase ω (u + v) * conj (Φ u * phase ω u) =
        phase ω v * (Φ (u + v) * conj (Φ u)) := by
      intro u
      rw [phase_add, map_mul]
      have := phase_mul_conj ω u
      linear_combination (Φ (u + v) * phase ω v * conj (Φ u)) * this
    simp_rw [this]
    rw [integral_const_mul]
    unfold acorr
    ring
  rw [step1]
  simp_rw [step2]
  rw [integral_integral_swap hint]
  exact integral_congr_ae (ae_of_all _ step4)

/-- Auxiliary: the convolution integral is `X + conj X` with `X` its half over
`v > 0`, by the symmetry `c(-v) = conj c(v)` (the TeX's "two conjugate
triangles", lines 318-324). -/
theorem integral_acorr_split {a : ℝ} (ha1 : a < 1) (hΦm : Measurable Φ)
    (hΦ0 : ∀ u ∉ Icc s (s + h), Φ u = 0) (hΦb : ∀ u, ‖Φ u‖ ≤ M) (hh : 0 ≤ h) (ω : ℝ) :
    ∫ v, ((kern a v : ℝ) : ℂ) * (phase ω v * acorr Φ v) =
      (∫ v in Ioi 0, ((kern a v : ℝ) : ℂ) * (phase ω v * acorr Φ v)) +
        conj (∫ v in Ioi 0, ((kern a v : ℝ) : ℂ) * (phase ω v * acorr Φ v)) := by
  have hM := M_nonneg_of_bound hΦb
  set W : ℝ → ℂ := fun v => ((kern a v : ℝ) : ℂ) * (phase ω v * acorr Φ v) with hWdef
  have hWneg : ∀ v, W (-v) = conj (W v) := by
    intro v
    simp only [W, kern_neg, phase_neg, acorr_neg, map_mul, Complex.conj_ofReal]
  have hWm : AEStronglyMeasurable W volume :=
    ((Complex.continuous_ofReal.measurable.comp (measurable_kern a)).aestronglyMeasurable).mul
      ((continuous_phase ω).aestronglyMeasurable.mul
        (acorr_stronglyMeasurable hΦm).aestronglyMeasurable)
  have hb : Integrable ((Icc (-h) h).indicator (kern a) · * (M * M * h)) :=
    (integrable_kern_indicator ha1 h hh).mul_const _
  have hWi : Integrable W := by
    refine hb.mono' hWm (ae_of_all _ fun v => ?_)
    have hc := acorr_bound_abs hΦ0 hΦb v
    simp only [W, norm_mul, norm_phase, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (kern_nonneg a v)]
    by_cases hv : v ∈ Icc (-h) h
    · rw [indicator_of_mem hv]
      have : max (h - |v|) 0 ≤ h := max_le (by linarith [abs_nonneg v]) hh
      exact mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_left this
        (mul_nonneg hM hM))) (kern_nonneg a v)
    · rw [indicator_of_notMem hv, zero_mul]
      have hv' : h < |v| := by
        by_contra hc'
        push Not at hc'
        exact hv (abs_le.mp hc')
      rw [max_eq_right (by linarith), mul_zero] at hc
      rw [norm_le_zero_iff.mp hc, norm_zero, mul_zero]
  rw [← integral_add_compl measurableSet_Ioi hWi, compl_Ioi]
  congr 1
  have := integral_comp_neg_Iic 0 (fun v => W (-v))
  simp only [neg_neg, neg_zero] at this
  rw [this, ← integral_conj]
  exact integral_congr_ae (ae_of_all _ fun v => hWneg v)

end Identity

/-! ### The constants -/

/-- Auxiliary: `⟨x⟩ ≥ 1`. -/
theorem one_le_bracket (x : ℝ) : 1 ≤ bracket x := by
  unfold bracket
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + x ^ 2) := Real.sqrt_le_sqrt (by nlinarith)

/-- Auxiliary (the case `⟨hω⟩ ≤ 8`, constant check): `2B h^{2-a} ≤ 16 h^{2-a} K² ⟨x⟩^{a-1}`
when `B ≤ K²` and `⟨x⟩ ≤ 8`. -/
theorem constant_small {a h B K x : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hh : 0 < h) (hBK : B ≤ K ^ 2)
    (hx : bracket x ≤ 8) :
    2 * B * h ^ (2 - a) ≤ 16 * h ^ (2 - a) * K ^ 2 * bracket x ^ (a - 1) := by
  have hb1 := one_le_bracket x
  have h8 : (8 : ℝ) ^ (a - 1) ≤ bracket x ^ (a - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hx (by linarith)
  have h8' : (8 : ℝ) ^ (-1 : ℝ) ≤ (8 : ℝ) ^ (a - 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  rw [Real.rpow_neg_one] at h8'
  have hp : 0 < h ^ (2 - a) := Real.rpow_pos_of_pos hh _
  have hK : 0 ≤ K ^ 2 := sq_nonneg K
  have : 1 / 8 ≤ bracket x ^ (a - 1) := by linarith [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
  nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hp.le hK)]

/-- Auxiliary (the case `⟨hω⟩ > 8`, constant check, with `k = h|ω| > 7` and
`δ = πh/k`): `2hB δ^{1-a} + (L+B) δ h^{1-a} ≤ 16 h^{2-a} K² ⟨k⟩^{a-1}` when
`B ≤ K²` and `L + B ≤ 2K²`.  This is where the TeX's `8√2 ≤ 16` is replaced by
`4π · 8/7 ≤ 16` (the shift argument has a different numerical constant). -/
theorem constant_large {a h k B L K : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hh : 0 < h) (hk : 7 < k)
    (hBK : B ≤ K ^ 2) (hLB : L + B ≤ 2 * K ^ 2) :
    2 * h * B * (Real.pi * h / k) ^ (1 - a) + (L + B) * (Real.pi * h / k) * h ^ (1 - a) ≤
      16 * h ^ (2 - a) * K ^ 2 * bracket k ^ (a - 1) := by
  have hk0 : 0 < k := by linarith
  have h1a : 0 < 1 - a := by linarith
  have hpi := Real.pi_pos
  have hpi2 := Real.pi_lt_d2
  set q := k ^ (1 - a) with hq
  set H := h ^ (1 - a) with hH
  set P := Real.pi ^ (1 - a) with hP
  have hq0 : 0 < q := Real.rpow_pos_of_pos hk0 _
  have hH0 : 0 < H := Real.rpow_pos_of_pos hh _
  -- `δ^{1-a} = P H / q`
  have e1 : (Real.pi * h / k) ^ (1 - a) = P * H / q := by
    rw [Real.div_rpow (by positivity) hk0.le, Real.mul_rpow hpi.le hh.le]
  -- `h^{2-a} = h H`
  have e2 : h ^ (2 - a) = h * H := by
    rw [hH, show (2 : ℝ) - a = 1 + (1 - a) by ring, Real.rpow_add hh, Real.rpow_one]
  -- `P ≤ π`, `q ≤ k`
  have hPpi : P ≤ Real.pi := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_three])
      (show 1 - a ≤ 1 by linarith)
    rwa [Real.rpow_one] at this
  have hqk : q ≤ k := by
    have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ k by linarith)
      (show 1 - a ≤ 1 by linarith)
    rwa [Real.rpow_one] at this
  have hP0 : 0 ≤ P := Real.rpow_nonneg hpi.le _
  -- `⟨k⟩^{a-1} ≥ 7/(8q)`
  have hbr : bracket k ≤ 8 / 7 * k := by
    unfold bracket
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hbr1 := one_le_bracket k
  have hbrq : bracket k ^ (1 - a) ≤ 8 / 7 * q := by
    calc bracket k ^ (1 - a) ≤ (8 / 7 * k) ^ (1 - a) :=
          Real.rpow_le_rpow (by linarith) hbr h1a.le
      _ = (8 / 7 : ℝ) ^ (1 - a) * q := Real.mul_rpow (by norm_num) hk0.le
      _ ≤ 8 / 7 * q := by
          have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 8 / 7 by norm_num)
            (show 1 - a ≤ 1 by linarith)
          rw [Real.rpow_one] at this
          exact mul_le_mul_of_nonneg_right this hq0.le
  have hinv : bracket k ^ (a - 1) = 1 / bracket k ^ (1 - a) := by
    rw [show a - 1 = -(1 - a) by ring, Real.rpow_neg (by linarith), one_div]
  have hbpos : 0 < bracket k ^ (1 - a) := Real.rpow_pos_of_pos (by linarith) _
  have hlow : 7 / (8 * q) ≤ bracket k ^ (a - 1) := by
    rw [hinv, div_le_div_iff₀ (by positivity) hbpos]
    linarith
  rw [e1, e2]
  -- bound the left side by `4π K² h H / q`
  have hK2 : 0 ≤ K ^ 2 := sq_nonneg K
  have l1 : 2 * h * B * (P * H / q) ≤ 2 * h * K ^ 2 * (Real.pi * H / q) := by
    have : P * H / q ≤ Real.pi * H / q := by gcongr
    have : 0 ≤ P * H / q := by positivity
    have : 2 * h * B ≤ 2 * h * K ^ 2 := by nlinarith
    calc 2 * h * B * (P * H / q) ≤ 2 * h * K ^ 2 * (P * H / q) := by gcongr
      _ ≤ _ := by gcongr
  have l2 : (L + B) * (Real.pi * h / k) * H ≤ 2 * K ^ 2 * (Real.pi * h / q) * H := by
    have : Real.pi * h / k ≤ Real.pi * h / q := by gcongr
    gcongr
  have total : 2 * h * K ^ 2 * (Real.pi * H / q) + 2 * K ^ 2 * (Real.pi * h / q) * H =
      4 * Real.pi * (K ^ 2 * h * H) / q := by ring
  have rhs : 14 * (K ^ 2 * h * H) / q ≤ 16 * (h * H) * K ^ 2 * bracket k ^ (a - 1) := by
    have hX : 0 ≤ K ^ 2 * h * H := by positivity
    calc 14 * (K ^ 2 * h * H) / q = 16 * (K ^ 2 * h * H) * (7 / (8 * q)) := by
          field_simp; ring
      _ ≤ 16 * (K ^ 2 * h * H) * bracket k ^ (a - 1) := by gcongr
      _ = _ := by ring
  have mid : 4 * Real.pi * (K ^ 2 * h * H) / q ≤ 14 * (K ^ 2 * h * H) / q := by
    have hX : 0 ≤ K ^ 2 * h * H := by positivity
    gcongr
    linarith
  linarith

/-- Auxiliary (the crude bound, the TeX's case `|ωh| ≤ 1` argument):
`‖∫_0^∞ v^{-a} e^{iωv} C(v) dv‖ ≤ B h · h^{1-a}/(1-a)` when `‖C(v)‖ ≤ B (h-v)_+`
for `v ≥ 0`. -/
theorem crude_bound {a h B : ℝ} (ha1 : a < 1) (hh : 0 < h) (hB : 0 ≤ B) (C : ℝ → ℂ)
    (hCb : ∀ v, 0 ≤ v → ‖C v‖ ≤ B * max (h - v) 0) (ω : ℝ) :
    ‖∫ v in Ioi 0, ((v ^ (-a) : ℝ) : ℂ) * phase ω v * C v‖ ≤ B * h * (h ^ (1 - a) / (1 - a)) := by
  have hr : -1 < -a := by linarith
  have h1a : 0 < 1 - a := by linarith
  have hbd : Integrable ((Ioc 0 h).indicator fun v => v ^ (-a) * (B * h)) :=
    integrable_indicator_Ioc hh.le ((intervalIntegral.intervalIntegrable_rpow' hr).mul_const _)
  have hnn : ∀ v, 0 ≤ (Ioc 0 h).indicator (fun v => v ^ (-a) * (B * h)) v :=
    fun v => indicator_nonneg (fun v hv => mul_nonneg (Real.rpow_nonneg hv.1.le _)
      (mul_nonneg hB hh.le)) v
  rw [← integral_indicator measurableSet_Ioi]
  refine (norm_integral_le_of_norm_le hbd (ae_of_all _ fun v => ?_)).trans (le_of_eq ?_)
  · rcases le_or_gt v 0 with hv | hv
    · rw [indicator_of_notMem (show v ∉ Ioi (0 : ℝ) by simp; linarith), norm_zero]
      exact hnn v
    rw [indicator_of_mem (show v ∈ Ioi (0 : ℝ) from hv), norm_mul, norm_mul, norm_phase, mul_one,
      norm_ofReal_rpow hv.le]
    rcases le_or_gt v h with hv' | hv'
    · rw [indicator_of_mem (show v ∈ Ioc 0 h from ⟨hv, hv'⟩)]
      have hc := hCb v hv.le
      have hmax : max (h - v) 0 ≤ h := max_le (by linarith) hh.le
      exact mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_left hmax hB))
        (Real.rpow_nonneg hv.le _)
    · have hc := hCb v hv.le
      rw [max_eq_right (by linarith), mul_zero] at hc
      rw [norm_le_zero_iff.mp hc, norm_zero, mul_zero]
      exact hnn v
  · rw [integral_indicator_Ioc _ hh.le, intervalIntegral.integral_mul_const,
      integral_rpow (Or.inl hr), Real.zero_rpow (by linarith), sub_zero,
      show -a + 1 = 1 - a by ring]
    ring

/-! ### Lemma `L:masked-temporal-modulation` -/

/-- Auxiliary: the modulated amplitude in convolution-ready form. -/
theorem modeFn_eq_indicator_mul (I : Set ℝ) (A : ℝ → ℂ) (ω : ℝ) :
    modeFn I A ω = fun t => I.indicator A t * phase ω t := by
  funext t
  by_cases ht : t ∈ I
  · simp [modeFn, phase, indicator_of_mem ht]
  · simp [modeFn, indicator_of_notMem ht]

/-- `L:masked-temporal-modulation` (TeX lines 300-345), general form under the
envelope bounds the proof uses: let `0 < a < 1`, `h > 0`, `0 ≤ s`, `s + h ≤ T`,
`I = [s, s+h]`, `A` continuous on `I` with `‖A‖ ≤ M` on `I` and
`‖A(x) - A(y)‖ ≤ D |x - y|` on `I`.  Then for every real `ω` the integrand of
the complexified form at `F = 1_I A e^{iω·}` is integrable on `[0,T]²` and
`|⟨F, F⟩_a| ≤ C₀(a) h^{2-a} (M+hD)² ⟨hω⟩^{a-1}`, `C₀(a) = 16/(1-a)`.
(`M ≥ 0` and `D ≥ 0` follow from the bounds since `h > 0`.) -/
theorem modulation_bound {a T s h : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hh : 0 < h) (hs : 0 ≤ s)
    (hsT : s + h ≤ T) (A : ℝ → ℂ) (hcont : ContinuousOn A (Icc s (s + h))) (M D : ℝ)
    (hMb : ∀ u ∈ Icc s (s + h), ‖A u‖ ≤ M)
    (hDl : ∀ x ∈ Icc s (s + h), ∀ y ∈ Icc s (s + h), ‖A x - A y‖ ≤ D * |x - y|) (ω : ℝ) :
    Integrable (fun p : ℝ × ℝ => modeFn (Icc s (s + h)) A ω p.1 *
        conj (modeFn (Icc s (s + h)) A ω p.2) * ((kern a (p.1 - p.2) : ℝ) : ℂ))
        ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) ∧
      ‖timeForm a T (modeFn (Icc s (s + h)) A ω) (modeFn (Icc s (s + h)) A ω)‖ ≤
        C₀ a * h ^ (2 - a) * (M + h * D) ^ 2 * bracket (h * ω) ^ (a - 1) := by
  classical
  set I := Icc s (s + h) with hIdef
  have hsI : s ∈ I := ⟨le_rfl, by linarith⟩
  have hshI : s + h ∈ I := ⟨by linarith, le_rfl⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMb s hsI)
  have hD0 : 0 ≤ D := by
    have := (norm_nonneg _).trans (hDl s hsI (s + h) hshI)
    rw [show s - (s + h) = -h by ring, abs_neg, abs_of_pos hh] at this
    exact nonneg_of_mul_nonneg_left this hh
  have h1a : 0 < 1 - a := by linarith
  set Φ := I.indicator A with hΦdef
  have hΦm : Measurable Φ := by
    rw [hΦdef, ← piecewise_eq_indicator]
    exact hcont.measurable_piecewise continuousOn_const measurableSet_Icc
  have hΦ0 : ∀ u ∉ I, Φ u = 0 := fun u hu => indicator_of_notMem hu _
  have hΦb : ∀ u, ‖Φ u‖ ≤ M := by
    intro u
    by_cases hu : u ∈ I
    · rw [hΦdef, indicator_of_mem hu]
      exact hMb u hu
    · rw [hΦ0 u hu, norm_zero]
      exact hM0
  have hΦl : ∀ x ∈ I, ∀ y ∈ I, ‖Φ x - Φ y‖ ≤ D * |x - y| := by
    intro x hx y hy
    rw [hΦdef, indicator_of_mem hx, indicator_of_mem hy]
    exact hDl x hx y hy
  have hsupp : I ⊆ Icc 0 T := fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hmode := modeFn_eq_indicator_mul I A ω
  -- integrability, from the Schur bound
  have hT : 0 < T := by linarith
  have hmemLp : MemLp (modeFn I A ω) 2 (volume.restrict (Icc 0 T)) := by
    rw [hmode]
    refine MemLp.of_bound ((hΦm.mul (continuous_phase ω).measurable).aestronglyMeasurable) M
      (ae_of_all _ fun t => ?_)
    rw [norm_mul, norm_phase, mul_one]
    exact hΦb t
  refine ⟨(time_schur_complex ha0 ha1 hT _ hmemLp).1, ?_⟩
  -- the identity
  rw [hmode, timeForm_eq_acorr ha1 hΦm hΦ0 hΦb hh.le hsupp ω,
    integral_acorr_split ha1 hΦm hΦ0 hΦb hh.le ω]
  set X := ∫ v in Ioi 0, ((kern a v : ℝ) : ℂ) * (phase ω v * acorr Φ v) with hXdef
  have hX : X = ∫ v in Ioi 0, ((v ^ (-a) : ℝ) : ℂ) * phase ω v * acorr Φ v := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun v hv => ?_)
    simp only [kern, abs_of_pos (show (0 : ℝ) < v from hv)]
    ring
  have hsum : ‖X + conj X‖ ≤ 2 * ‖X‖ := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_conj]
    ring
  refine hsum.trans ?_
  set K := M + h * D
  have hMK : M ≤ K := by
    have : 0 ≤ h * D := mul_nonneg hh.le hD0
    linarith
  have hBK : M * M ≤ K ^ 2 := by nlinarith
  have hLB : (M * M + h * M * D) + M * M ≤ 2 * K ^ 2 := by
    have : 0 ≤ h * D := mul_nonneg hh.le hD0
    nlinarith
  have hCb : ∀ v, 0 ≤ v → ‖acorr Φ v‖ ≤ M * M * max (h - v) 0 := fun v _ =>
    acorr_bound hΦ0 hΦb v
  have hCl : ∀ v w, 0 ≤ v → v ≤ w → w ≤ h →
      ‖acorr Φ v - acorr Φ w‖ ≤ (M * M + h * M * D) * (w - v) := fun v w hv hvw _ =>
    acorr_lip hΦm hΦ0 hΦb hΦl hh.le hD0 hv hvw
  have hC0 : C₀ a * h ^ (2 - a) * K ^ 2 * bracket (h * ω) ^ (a - 1) =
      (16 * h ^ (2 - a) * K ^ 2 * bracket (h * ω) ^ (a - 1)) / (1 - a) := by
    unfold C₀
    ring
  rw [hC0, hX]
  rcases le_or_gt (bracket (h * ω)) 8 with hbr | hbr
  · -- `⟨hω⟩ ≤ 8`: the crude bound
    have hc := crude_bound ha1 hh (mul_nonneg hM0 hM0) (acorr Φ) hCb ω
    have e2 : h ^ (2 - a) = h * h ^ (1 - a) := by
      rw [show (2 : ℝ) - a = 1 + (1 - a) by ring, Real.rpow_add hh, Real.rpow_one]
    have hsm := constant_small ha0 ha1 hh hBK hbr
    rw [e2] at hsm ⊢
    rw [le_div_iff₀ h1a]
    have : 2 * ‖∫ v in Ioi 0, ((v ^ (-a) : ℝ) : ℂ) * phase ω v * acorr Φ v‖ * (1 - a) ≤
        2 * (M * M * h * (h ^ (1 - a) / (1 - a))) * (1 - a) := by gcongr
    rw [show 2 * (M * M * h * (h ^ (1 - a) / (1 - a))) * (1 - a) =
      2 * (M * M) * (h * h ^ (1 - a)) by field_simp] at this
    linarith
  · -- `⟨hω⟩ > 8`: the shift argument
    have hk : 7 < h * |ω| := by
      have h64 : 64 < 1 + (h * ω) ^ 2 := by
        have := hbr
        unfold bracket at this
        rw [Real.lt_sqrt (by norm_num)] at this
        linarith
      have hsq : (h * |ω|) ^ 2 = (h * ω) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
      nlinarith [abs_nonneg ω, mul_nonneg hh.le (abs_nonneg ω)]
    have hω0 : 0 < |ω| := by
      by_contra hc
      have : |ω| = 0 := le_antisymm (not_lt.mp hc) (abs_nonneg ω)
      rw [this, mul_zero] at hk
      linarith
    set δ := Real.pi / |ω| with hδdef
    have hδ0 : 0 < δ := div_pos Real.pi_pos hω0
    have hδh : δ < h := by
      rw [hδdef, div_lt_iff₀ hω0]
      linarith [Real.pi_lt_d2]
    have hphase : phase ω δ = -1 := by
      unfold phase
      rcases lt_or_gt_of_ne (abs_pos.mp hω0) with hneg | hpos
      · have hne : ω ≠ 0 := hneg.ne
        rw [hδdef, abs_of_neg hneg, show ω * (Real.pi / -ω) = -Real.pi by field_simp]
        push_cast
        rw [neg_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
        norm_num
      · rw [hδdef, abs_of_pos hpos, show ω * (Real.pi / ω) = Real.pi by field_simp]
        exact Complex.exp_pi_mul_I
    have ho := osc_bound ha0 ha1 hδ0 hδh (mul_nonneg hM0 hM0)
      (by positivity : (0 : ℝ) ≤ M * M + h * M * D) (acorr Φ)
      (acorr_stronglyMeasurable hΦm).aestronglyMeasurable hCb hCl ω hphase
    have hδ' : δ = Real.pi * h / (h * |ω|) := by
      rw [hδdef]
      field_simp
    have hlg := constant_large ha0 ha1 hh hk hBK hLB
    rw [← hδ'] at hlg
    have hbreq : bracket (h * ω) = bracket (h * |ω|) := by
      unfold bracket
      rw [mul_pow, mul_pow, sq_abs]
    rw [hbreq]
    rw [le_div_iff₀ h1a]
    have : 2 * ‖∫ v in Ioi 0, ((v ^ (-a) : ℝ) : ℂ) * phase ω v * acorr Φ v‖ * (1 - a) ≤
        2 * ((2 * h * (M * M) * δ ^ (1 - a) + (M * M + h * M * D + M * M) * δ * h ^ (1 - a)) /
          (2 * (1 - a))) * (1 - a) := by gcongr
    rw [show 2 * ((2 * h * (M * M) * δ ^ (1 - a) + (M * M + h * M * D + M * M) * δ * h ^ (1 - a)) /
          (2 * (1 - a))) * (1 - a) =
        2 * h * (M * M) * δ ^ (1 - a) + (M * M + h * M * D + M * M) * δ * h ^ (1 - a) by
      field_simp] at this
    linarith

/-- Auxiliary: the envelope facts used by the proof, from the manuscript's
hypotheses `A ∈ C¹(I; ℂ)`, `M = sup_I |A|`, `D = sup_I |A'|` with `I = [s, s+h]`,
`h > 0`: `A` is continuous on `I`, `‖A‖ ≤ M` on `I`, and `A` is `D`-Lipschitz on
`I` (mean value inequality).  The suprema are finite because `I` is compact and
`A`, `A'` are continuous on it, so `sSup` is not Lean's junk value here. -/
theorem envelope_of_contDiffOn {s h : ℝ} (hh : 0 < h) (A : ℝ → ℂ)
    (hA : ContDiffOn ℝ 1 A (Icc s (s + h))) (M D : ℝ)
    (hM : M = sSup ((fun t => ‖A t‖) '' Icc s (s + h)))
    (hD : D = sSup ((fun t => ‖derivWithin A (Icc s (s + h)) t‖) '' Icc s (s + h))) :
    ContinuousOn A (Icc s (s + h)) ∧ (∀ u ∈ Icc s (s + h), ‖A u‖ ≤ M) ∧
      ∀ x ∈ Icc s (s + h), ∀ y ∈ Icc s (s + h), ‖A x - A y‖ ≤ D * |x - y| := by
  have hcont : ContinuousOn A (Icc s (s + h)) := hA.continuousOn
  have bddM : BddAbove ((fun t => ‖A t‖) '' Icc s (s + h)) :=
    isCompact_Icc.bddAbove_image (continuous_norm.comp_continuousOn hcont)
  have hdc : ContinuousOn (derivWithin A (Icc s (s + h))) (Icc s (s + h)) :=
    hA.continuousOn_derivWithin (uniqueDiffOn_Icc (by linarith)) le_rfl
  have bddD : BddAbove ((fun t => ‖derivWithin A (Icc s (s + h)) t‖) '' Icc s (s + h)) :=
    isCompact_Icc.bddAbove_image (continuous_norm.comp_continuousOn hdc)
  refine ⟨hcont, fun u hu => hM ▸ le_csSup bddM (mem_image_of_mem _ hu), ?_⟩
  intro x hx y hy
  have hdb : ∀ z ∈ Icc s (s + h), ‖derivWithin A (Icc s (s + h)) z‖ ≤ D :=
    fun z hz => hD ▸ le_csSup bddD (mem_image_of_mem _ hz)
  have := Convex.norm_image_sub_le_of_norm_derivWithin_le (hA.differentiableOn one_ne_zero)
    hdb (convex_Icc _ _) hy hx
  rwa [Real.norm_eq_abs] at this

/-- Auxiliary: a modulated amplitude `1_I A e^{iω·}` with `A` continuous and
bounded by `M` on `I = [s, s+h]` lies in `L²(0,T)`. -/
theorem memLp_modeFn {s h T : ℝ} (A : ℝ → ℂ) (hcont : ContinuousOn A (Icc s (s + h))) (M : ℝ)
    (hMb : ∀ u ∈ Icc s (s + h), ‖A u‖ ≤ M) (ω : ℝ) :
    MemLp (modeFn (Icc s (s + h)) A ω) 2 (volume.restrict (Icc 0 T)) := by
  classical
  have hΦm : Measurable ((Icc s (s + h)).indicator A) := by
    rw [← piecewise_eq_indicator]
    exact hcont.measurable_piecewise continuousOn_const measurableSet_Icc
  rw [modeFn_eq_indicator_mul]
  refine MemLp.of_bound ((hΦm.mul (continuous_phase ω).measurable).aestronglyMeasurable)
    (max M 0) (ae_of_all _ fun t => ?_)
  rw [norm_mul, norm_phase, mul_one]
  by_cases ht : t ∈ Icc s (s + h)
  · rw [indicator_of_mem ht]
    exact (hMb t ht).trans (le_max_left _ _)
  · rw [indicator_of_notMem ht, norm_zero]
    exact le_max_right _ _

/-- `L:masked-temporal-modulation` (TeX lines 300-345, display 303-307), exact
hypotheses, in double-integral form.  Standing assumptions of the subsection
(TeX lines 296-298): `I = [s, s+h] ⊆ [0, T]`, `0 < h ≤ 1`, with `T > 0` and
`0 < a < 1` from `L:masked-time-completion`; lemma hypotheses: `A ∈ C¹(I; ℂ)`,
`M = sup_I |A|`, `D = sup_I |A'|` (with `A'` the derivative within `I`).  For
every real `ω`, the integrand `F(t) conj F(u) |t-u|^{-a}`, `F = 1_I A e^{iω·}`,
is integrable on `[0,T]²` and its double integral (the complexified form of
`L:masked-time-completion`) satisfies
`|⟨F, F⟩_a| ≤ C₀(a) h^{2-a} (M+hD)² ⟨hω⟩^{a-1}` with `C₀(a) = 16/(1-a)`.

The left side of the manuscript's display is the completion norm
`‖1_I A e^{iωt}‖_a²`; by the complexification clause of
`L:masked-time-completion` (TeX lines 153-154) it equals this double integral,
which is what is bounded here (the completion is not constructed).  The
hypotheses `T > 0` and `h ≤ 1` are not used by the proof (the bound is uniform
in `T`, `s`, `h`, `A` and `ω`, as the TeX states). -/
theorem masked_temporal_modulation_paper (a T s h : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (_hT : 0 < T)
    (hh0 : 0 < h) (_hh1 : h ≤ 1) (hs : 0 ≤ s) (hsT : s + h ≤ T)
    (A : ℝ → ℂ) (hA : ContDiffOn ℝ 1 A (Icc s (s + h)))
    (M D : ℝ)
    (hM : M = sSup ((fun t => ‖A t‖) '' Icc s (s + h)))
    (hD : D = sSup ((fun t => ‖derivWithin A (Icc s (s + h)) t‖) '' Icc s (s + h)))
    (ω : ℝ) :
    Integrable (fun p : ℝ × ℝ => modeFn (Icc s (s + h)) A ω p.1 *
        conj (modeFn (Icc s (s + h)) A ω p.2) * ((kern a (p.1 - p.2) : ℝ) : ℂ))
        ((volume.restrict (Icc 0 T)).prod (volume.restrict (Icc 0 T))) ∧
      ‖timeForm a T (modeFn (Icc s (s + h)) A ω) (modeFn (Icc s (s + h)) A ω)‖ ≤
        C₀ a * h ^ (2 - a) * (M + h * D) ^ 2 * bracket (h * ω) ^ (a - 1) := by
  obtain ⟨hcont, hMb, hDl⟩ := envelope_of_contDiffOn hh0 A hA M D hM hD
  exact modulation_bound ha0 ha1 hh0 hs hsT A hcont M D hMb hDl ω

/-! ### `L:masked-trig-products` with the norm identity in place of the modulation input -/

/-- `L:masked-trig-products` (TeX lines 347-374), re-issued with one supplied
input fewer than `MaskedTrigProducts.masked_trig_products_paper`: the
modulation bound `hmod` (`L:masked-temporal-modulation`) is no longer assumed
but proved (`masked_temporal_modulation_paper`), through the norm identity

`hnorm`: for `f ∈ V` with `f ∈ L²(0,T)`, `‖emb f‖² = Re ∬_{[0,T]²} f(t) conj f(u) |t-u|^{-a}`,

which is the complexification clause of `L:masked-time-completion` (TeX lines
153-154; with lines 148-149 and 177-178 it holds for all of `L²(0,T)`).
Remaining supplied inputs: `hmem` (TeX lines 154-155, the modes belong to the
accepted class `V`, whose inclusion `emb` into `E = H_a^ℂ` is linear) and
`hnorm`.  The other hypotheses are the manuscript's, as in
`masked_trig_products_paper`; `T > 0` and `h ≤ 1` are carried but not used. -/
theorem masked_trig_products_bridged_paper {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    (a T s h : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (hT : 0 < T)
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hs : 0 ≤ s) (hsT : s + h ≤ T)
    (A : ℝ → ℂ) (hA : ContDiffOn ℝ 1 A (Icc s (s + h)))
    (M D : ℝ)
    (hM : M = sSup ((fun t => ‖A t‖) '' Icc s (s + h)))
    (hD : D = sSup ((fun t => ‖derivWithin A (Icc s (s + h)) t‖) '' Icc s (s + h)))
    (r ρ : ℝ) (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (P Q : Trig)
    (V : Submodule ℂ (ℝ → ℂ)) (emb : V →ₗ[ℂ] E)
    (hmem : ∀ ω : ℝ, modeFn (Icc s (s + h)) A ω ∈ V)
    (hnorm : ∀ f : V, MemLp (f : ℝ → ℂ) 2 (volume.restrict (Icc 0 T)) →
      ‖emb f‖ ^ 2 = (timeForm a T f f).re) :
    prodFn (Icc s (s + h)) A P Q r ρ ∈ V ∧
      ∀ hp : prodFn (Icc s (s + h)) A P Q r ρ ∈ V,
        ‖emb ⟨prodFn (Icc s (s + h)) A P Q r ρ, hp⟩‖ ^ 2 ≤
          C₀ a * h ^ (2 - a) * (M + h * D) ^ 2 * frequencyPair a h r ρ := by
  obtain ⟨hcont, hMb, -⟩ := envelope_of_contDiffOn hh0 A hA M D hM hD
  refine masked_trig_products_paper a T s h ha0 ha1 hT hh0 hh1 hs hsT A hA M D hM hD r ρ hr hρ
    P Q V emb hmem (fun ω => ?_)
  rw [hnorm ⟨_, hmem ω⟩ (memLp_modeFn A hcont M hMb ω)]
  exact (Complex.re_le_norm _).trans
    (masked_temporal_modulation_paper a T s h ha0 ha1 hT hh0 hh1 hs hsT A hA M D hM hD ω).2

end StratonovichHAMSecondMoment.MaskedModulation
