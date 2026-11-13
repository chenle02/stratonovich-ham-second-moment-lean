module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Section `S:temporal-equilibrium` (The temporal equilibrium density) of
`notes/integrated_temporal_equilibrium.tex`: Lemma `L:equilibrium-gamma-beta`
(Gamma and Beta identities) and Lemma `L:temporal-equilibrium` (Exact potential
and mass).

Conventions and side conditions made explicit here:
* The manuscript's `Γ_E` is Euler's Gamma function; we use Mathlib's
  `Real.Gamma`, and `gammaE_integral` records that for `x > 0` it is the
  manuscript's integral `∫_0^∞ u^{x-1} e^{-u} du` (integrable, positive).
* The manuscript's `Beta(x,y) = ∫_0^1 t^{x-1}(1-t)^{y-1} dt` is defined
  verbatim as `Beta x y` (a Bochner integral over `Ioo 0 1`);
  `Beta_integrableOn` and `Beta_pos` record that it is a finite positive
  integral for `x, y > 0`, and `Beta_eq_betaIntegral` identifies it with
  Mathlib's `Complex.betaIntegral`.
* `f_a` is `density a`, a total function `ℝ → ℝ` whose values are only used on
  `(0,1)` (the manuscript defines it only for `0 < t < 1`).
  `L^p(0,1)` is `MemLp · p (volume.restrict (Ioo 0 1))`.
* Every integral conclusion carries its integrability (the Bochner integral of
  a non-integrable function is `0` in Lean).
* The potential kernel `|s-t|^{-a}` is `|s - t| ^ (-a)` with Lean's `rpow`; its
  value at `t = s` (a null set) is irrelevant.

Proof route (differs from the TeX proof, same statement): the TeX proof of the
potential identity expands hypergeometric series.  Here the left part is
computed by a Tonelli swap from the Euler-type identity
`∫_0^t (t-u)^{-2r} u^{r-1}(1-u)^{r-1} du = Beta(r,1-2r) [t(1-t)]^{-r}`
(Möbius substitution `u = t v / (1 - t + t v)`), which gives
`Beta(r,1-2r) L(s) = Beta(1-2r,2r) B_s(r,r)`, the same incomplete-Beta
formula as the TeX display after line 71.  The right part and the endpoints
follow by reflection `t ↦ 1-t` and splitting at `s` (no limiting argument).
-/
public import Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real
open scoped ENNReal

namespace StratonovichHAMSecondMoment.TemporalEquilibrium

/-! ### Euler's Beta function as the manuscript's integral -/

/-- The Beta integrand `t^{x-1}(1-t)^{y-1}`. -/
def betaKernel (x y : ℝ) (t : ℝ) : ℝ := t ^ (x - 1) * (1 - t) ^ (y - 1)

/-- The manuscript's `Beta(x,y) = ∫_0^1 t^{x-1}(1-t)^{y-1} dt` (TeX line 10). -/
def Beta (x y : ℝ) : ℝ := ∫ t in Ioo (0:ℝ) 1, betaKernel x y t

lemma cplx_kernel_eq (x y t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    (t : ℂ) ^ ((x : ℂ) - 1) * (1 - (t : ℂ)) ^ ((y : ℂ) - 1) = (betaKernel x y t : ℂ) := by
  unfold betaKernel
  rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1, Complex.ofReal_cpow (by linarith [ht.2])]
  push_cast; ring_nf

theorem betaKernel_integrableOn {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (betaKernel x y) (Ioo 0 1) := by
  have h := Complex.betaIntegral_convergent (u := (x : ℂ)) (v := (y : ℂ)) (by simpa) (by simpa)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
  have h2 := h.re
  refine (h2.congr_fun ?_ measurableSet_Ioc).mono_set Ioo_subset_Ioc_self
  intro t ht
  simp only
  rw [cplx_kernel_eq x y t ⟨ht.1.le, ht.2⟩]; simp

theorem Beta_eq_Gamma {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Beta x y = Gamma x * Gamma y / Gamma (x + y) := by
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (x : ℂ)) (t := (y : ℂ))
    (by simpa) (by simpa)
  have hB : Complex.betaIntegral x y = (Beta x y : ℂ) := by
    unfold Complex.betaIntegral Beta
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    exact cplx_kernel_eq x y t ht
  rw [hB, ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal] at hG
  have hpos : 0 < Gamma (x + y) := Gamma_pos_of_pos (by linarith)
  have hG' : Gamma x * Gamma y = Gamma (x + y) * Beta x y := by exact_mod_cast hG
  field_simp
  linarith



lemma betaKernel_nonneg (x y : ℝ) {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) : 0 ≤ betaKernel x y t :=
  mul_nonneg (rpow_nonneg ht.1.le _) (rpow_nonneg (by linarith [ht.2]) _)

theorem lintegral_betaKernel {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ∫⁻ t in Ioo (0:ℝ) 1, ENNReal.ofReal (betaKernel x y t) = ENNReal.ofReal (Beta x y) := by
  unfold Beta
  rw [ofReal_integral_eq_lintegral_ofReal (betaKernel_integrableOn hx hy)]
  exact ae_restrict_of_forall_mem measurableSet_Ioo fun t ht => betaKernel_nonneg x y ht

theorem Beta_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < Beta x y := by
  rw [Beta_eq_Gamma hx hy]
  exact div_pos (mul_pos (Gamma_pos_of_pos hx) (Gamma_pos_of_pos hy))
    (Gamma_pos_of_pos (by linarith))

/-- Affine Beta integral on `(u, s)`. -/
theorem lintegral_affine_beta {u s p q : ℝ} (hus : u < s) (hp : 0 < p) (hq : 0 < q) :
    ∫⁻ t in Ioo u s, ENNReal.ofReal ((s - t) ^ (p - 1) * (t - u) ^ (q - 1))
      = ENNReal.ofReal ((s - u) ^ (p + q - 1) * Beta q p) := by
  have hd : 0 < s - u := sub_pos.mpr hus
  have himg : (fun v : ℝ => u + (s - u) * v) '' Ioo 0 1 = Ioo u s := by
    ext x; constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨by nlinarith [hv.1], by nlinarith [hv.2]⟩
    · intro hx
      refine ⟨(x - u) / (s - u), ⟨div_pos (by linarith [hx.1]) hd, ?_⟩, ?_⟩
      · rw [div_lt_one hd]; linarith [hx.2]
      · field_simp; ring
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (f' := fun _ => s - u)]
  rotate_left
  · intro v _
    have := ((hasDerivAt_id v).const_mul (s - u)).const_add u
    simpa using this.hasDerivWithinAt
  · intro v₁ _ v₂ _ h
    simpa [hd.ne'] using h
  rw [ENNReal.ofReal_mul (by positivity), ← lintegral_betaKernel hq hp,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  rw [abs_of_pos hd, ← ENNReal.ofReal_mul hd.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h1 : s - (u + (s - u) * v) = (s - u) * (1 - v) := by ring
  have h2 : u + (s - u) * v - u = (s - u) * v := by ring
  have hv1 : 0 < 1 - v := by linarith [hv.2]
  rw [h1, h2, mul_rpow hd.le hv1.le, mul_rpow hd.le hv.1.le]
  unfold betaKernel
  have : (s - u) ^ (p + q - 1) = (s - u) * (s - u) ^ (p - 1) * (s - u) ^ (q - 1) := by
    rw [mul_assoc, ← rpow_add hd]
    nth_rewrite 2 [← rpow_one (s - u)]
    rw [← rpow_add hd]
    congr 1; ring
  rw [this]; ring

/-- Reflection `x ↦ 1 - x`. -/
theorem lintegral_reflect (F : ℝ → ℝ≥0∞) (p q : ℝ) :
    ∫⁻ x in Ioo p q, F x = ∫⁻ x in Ioo (1 - q) (1 - p), F (1 - x) := by
  have himg : (fun x : ℝ => 1 - x) '' Ioo (1 - q) (1 - p) = Ioo p q := by
    ext x; constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨by linarith [hv.2], by linarith [hv.1]⟩
    · intro hx; exact ⟨1 - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, by ring⟩
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo (f' := fun _ => -1)]
  · simp
  · intro v _
    simpa using ((hasDerivAt_id v).const_sub 1).hasDerivWithinAt
  · intro v₁ _ v₂ _ h; simpa using h

/-- Splitting `(0,1)` at `s ∈ [0,1]` (the point `s` is null). -/
theorem lintegral_split (F : ℝ → ℝ≥0∞) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    ∫⁻ x in Ioo (0:ℝ) 1, F x = (∫⁻ x in Ioo 0 s, F x) + ∫⁻ x in Ioo s 1, F x := by
  have hdisj : Disjoint (Ioo (0:ℝ) s) (Ioo s 1) :=
    Set.disjoint_left.mpr fun x h1 h2 => by linarith [h1.2, h2.1]
  refine (setLIntegral_congr (ae_eq_set.mpr ⟨?_, ?_⟩)).trans
    (lintegral_union measurableSet_Ioo hdisj)
  · refine measure_mono_null (t := {s}) ?_ (measure_singleton s)
    intro x hx
    simp only [mem_sdiff, mem_union, mem_Ioo, not_or, not_and, not_lt] at hx
    simp only [mem_singleton_iff]
    rcases hx with ⟨⟨h0, h1⟩, ha, hb⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact absurd (ha h0) (not_le.mpr h)
    · exact absurd (hb h) (not_le.mpr h1)
  · have : (Ioo 0 s ∪ Ioo s 1) \ Ioo (0:ℝ) 1 = ∅ := by
      ext x; simp only [mem_sdiff, mem_union, mem_empty_iff_false, iff_false]
      rintro ⟨h | h, h'⟩
      · exact h' ⟨h.1, by linarith [hs.2, h.2]⟩
      · exact h' ⟨by linarith [hs.1, h.1], h.2⟩
    rw [this, measure_empty]


lemma mobius_pointwise {r t v : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (hv : v ∈ Ioo (0:ℝ) 1) :
    t * (1 - t) / (1 - t + t * v) ^ 2 *
      ((t - t * v / (1 - t + t * v)) ^ (-(2 * r)) * betaKernel r r (t * v / (1 - t + t * v)))
      = (t * (1 - t)) ^ (-r) * betaKernel r (1 - 2 * r) v := by
  obtain ⟨t0, t1⟩ := ht
  obtain ⟨v0, v1⟩ := hv
  have hT : 0 < 1 - t := by linarith
  have hV : 0 < 1 - v := by linarith
  have hD : 0 < 1 - t + t * v := by nlinarith
  set D := 1 - t + t * v with hDdef
  have e1 : t - t * v / D = t * (1 - t) * (1 - v) / D := by
    field_simp; rw [hDdef]; ring
  have e2 : 1 - t * v / D = (1 - t) / D := by
    field_simp; rw [hDdef]; ring
  unfold betaKernel
  rw [e1, e2]
  have p1 : 0 < t * (1 - t) * (1 - v) / D := by positivity
  have p2 : 0 < t * v / D := by positivity
  have p3 : 0 < (1 - t) / D := by positivity
  have p4 : 0 < t * (1 - t) := by positivity
  have p5 : 0 < t * (1 - t) / D ^ 2 := by positivity
  rw [rpow_def_of_pos p1, rpow_def_of_pos p2, rpow_def_of_pos p3, rpow_def_of_pos p4,
    rpow_def_of_pos v0, rpow_def_of_pos hV, ← exp_log p5]
  have l1 : log (t * (1 - t) * (1 - v) / D) = log t + log (1 - t) + log (1 - v) - log D := by
    rw [log_div (by positivity) hD.ne', log_mul (by positivity) hV.ne',
      log_mul t0.ne' hT.ne']
  have l2 : log (t * v / D) = log t + log v - log D := by
    rw [log_div (by positivity) hD.ne', log_mul t0.ne' v0.ne']
  have l3 : log ((1 - t) / D) = log (1 - t) - log D := log_div hT.ne' hD.ne'
  have l4 : log (t * (1 - t)) = log t + log (1 - t) := log_mul t0.ne' hT.ne'
  have l5 : log (t * (1 - t) / D ^ 2) = log t + log (1 - t) - 2 * log D := by
    rw [log_div p4.ne' (by positivity), l4, log_pow]; push_cast; ring
  rw [l1, l2, l3, l4, l5, ← exp_add, ← exp_add, ← exp_add, ← exp_add, ← exp_add]
  congr 1; ring

theorem mobius_image {t : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    (fun v : ℝ => t * v / (1 - t + t * v)) '' Ioo 0 1 = Ioo 0 t := by
  obtain ⟨t0, t1⟩ := ht
  ext x; constructor
  · rintro ⟨v, ⟨v0, v1⟩, rfl⟩
    have hD : 0 < 1 - t + t * v := by nlinarith
    refine ⟨by positivity, ?_⟩
    rw [div_lt_iff₀ hD]; nlinarith [mul_pos (mul_pos t0 (sub_pos.2 t1)) (sub_pos.2 v1)]
  · rintro ⟨x0, x1⟩
    have h1 : 0 < t * (1 - x) := by nlinarith
    refine ⟨x * (1 - t) / (t * (1 - x)), ⟨by
      have : 0 < x * (1 - t) := by nlinarith
      positivity, ?_⟩, ?_⟩
    · rw [div_lt_one h1]; nlinarith
    · have hx : (1:ℝ) - x ≠ 0 := by linarith
      have htt : (1:ℝ) - t ≠ 0 := by linarith
      have hD : 1 - t + t * (x * (1 - t) / (t * (1 - x))) = (1 - t) / (1 - x) := by
        field_simp; ring
      simp only
      rw [hD]
      field_simp

/-- The key Euler-type identity: for `0 < r < 1/2` and `0 < t < 1`,
`∫_0^t (t-u)^{-2r} u^{r-1}(1-u)^{r-1} du = Beta(r,1-2r) [t(1-t)]^{-r}`. -/
theorem lintegral_mobius {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1 / 2) (ht : t ∈ Ioo (0:ℝ) 1) :
    ∫⁻ u in Ioo 0 t, ENNReal.ofReal ((t - u) ^ (-(2 * r)) * betaKernel r r u)
      = ENNReal.ofReal (Beta r (1 - 2 * r) * (t * (1 - t)) ^ (-r)) := by
  obtain ⟨t0, t1⟩ := ht
  rw [← mobius_image ⟨t0, t1⟩, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (f' := fun v => t * (1 - t) / (1 - t + t * v) ^ 2)]
  rotate_left
  · intro v hv
    have hD : 0 < 1 - t + t * v := by nlinarith [hv.1, hv.2]
    have h : HasDerivAt (fun y : ℝ => t * y / (1 - t + t * y))
        ((t * 1 * (1 - t + t * v) - t * v * (t * 1)) / (1 - t + t * v) ^ 2) v :=
      ((hasDerivAt_id' v).const_mul t).div
        (((hasDerivAt_id' v).const_mul t).const_add (1 - t)) hD.ne'
    convert h.hasDerivWithinAt using 1
    ring
  · intro v₁ hv₁ v₂ hv₂ h
    have hD1 : 0 < 1 - t + t * v₁ := by nlinarith [hv₁.1, hv₁.2]
    have hD2 : 0 < 1 - t + t * v₂ := by nlinarith [hv₂.1, hv₂.2]
    simp only at h
    rw [div_eq_div_iff hD1.ne' hD2.ne'] at h
    have : t * (1 - t) * (v₁ - v₂) = 0 := by linarith
    have hT : 0 < 1 - t := by linarith
    have hne : t * (1 - t) ≠ 0 := by positivity
    have := (mul_eq_zero.mp this).resolve_left hne
    linarith
  rw [ENNReal.ofReal_mul (Beta_pos hr0 (by linarith)).le, ← lintegral_betaKernel hr0
    (by linarith : (0:ℝ) < 1 - 2 * r), ← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioo fun v hv => ?_
  have hD : 0 < 1 - t + t * v := by nlinarith [hv.1, hv.2]
  have hT : 0 < 1 - t := by linarith
  rw [abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (betaKernel_nonneg _ _ hv)]
  congr 1
  rw [mobius_pointwise ⟨t0, t1⟩ hv]; ring


/-- Left part of the potential (manuscript lines 61--75, via a Tonelli swap). -/
theorem lintegral_left {r s : ℝ} (hr0 : 0 < r) (hr1 : r < 1 / 2) (hs : s ∈ Icc (0:ℝ) 1) :
    ENNReal.ofReal (Beta r (1 - 2 * r)) *
        ∫⁻ t in Ioo 0 s, ENNReal.ofReal ((s - t) ^ (2 * r - 1) * (t * (1 - t)) ^ (-r))
      = ENNReal.ofReal (Beta (1 - 2 * r) (2 * r)) *
        ∫⁻ u in Ioo 0 s, ENNReal.ofReal (betaKernel r r u) := by
  set F : ℝ → ℝ → ℝ≥0∞ := fun t u => if u < t then
    ENNReal.ofReal (betaKernel r r u) *
      ENNReal.ofReal ((s - t) ^ (2 * r - 1) * (t - u) ^ (-(2 * r)))
    else 0 with hF
  have hmeas : Measurable (Function.uncurry F) := by
    refine Measurable.ite (measurableSet_lt measurable_snd measurable_fst) ?_ measurable_const
    unfold betaKernel
    fun_prop
  -- Step 1: insert the Möbius identity.
  have step1 : ENNReal.ofReal (Beta r (1 - 2 * r)) *
        ∫⁻ t in Ioo 0 s, ENNReal.ofReal ((s - t) ^ (2 * r - 1) * (t * (1 - t)) ^ (-r))
      = ∫⁻ t in Ioo 0 s, ∫⁻ u in Ioo 0 s, F t u := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    have ht1 : t ∈ Ioo (0:ℝ) 1 := ⟨ht.1, lt_of_lt_of_le ht.2 hs.2⟩
    have hst : 0 ≤ (s - t) ^ (2 * r - 1) := rpow_nonneg (by linarith [ht.2]) _
    have hF' : ∀ u ∈ Ioo 0 s, F t u = (Iio t).indicator (fun u =>
        ENNReal.ofReal ((s - t) ^ (2 * r - 1)) *
        ENNReal.ofReal ((t - u) ^ (-(2 * r)) * betaKernel r r u)) u := by
      intro u hu
      simp only [hF, Set.indicator, mem_Iio]
      split_ifs with h
      · have hu' : 0 ≤ (t - u) ^ (-(2 * r)) := rpow_nonneg (by linarith) _
        have hk := betaKernel_nonneg r r (t := u) ⟨hu.1, by linarith [hu.2, hs.2]⟩
        rw [← ENNReal.ofReal_mul hk, ← ENNReal.ofReal_mul hst]
        congr 1; ring
      · rfl
    rw [setLIntegral_congr_fun measurableSet_Ioo hF', setLIntegral_indicator measurableSet_Iio]
    have hset : Iio t ∩ Ioo 0 s = Ioo 0 t := by
      ext u; simp only [mem_inter_iff, mem_Iio, mem_Ioo]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith [ht.2]⟩
    rw [hset, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_mobius hr0 hr1 ht1,
      ← ENNReal.ofReal_mul hst, ← ENNReal.ofReal_mul (Beta_pos hr0 (by linarith)).le]
    congr 1; ring
  rw [step1, lintegral_lintegral_swap hmeas.aemeasurable,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  have hF'' : ∀ t, F t u = (Ioi u).indicator (fun t => ENNReal.ofReal (betaKernel r r u) *
      ENNReal.ofReal ((s - t) ^ (2 * r - 1) * (t - u) ^ (-(2 * r)))) t := by
    intro t
    simp only [hF, Set.indicator, mem_Ioi]
  simp_rw [hF'']
  rw [setLIntegral_indicator measurableSet_Ioi]
  have hset : Ioi u ∩ Ioo 0 s = Ioo u s := by
    ext t; simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith [hu.1], h2⟩
  rw [hset, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_comm]
  congr 1
  have := lintegral_affine_beta (u := u) (s := s) (p := 2 * r) (q := 1 - 2 * r) hu.2
    (by linarith) (by linarith)
  have e : (2 * r + (1 - 2 * r) - 1) = 0 := by ring
  rw [e, rpow_zero, one_mul] at this
  rw [← this]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  ring_nf


theorem betaKernel_symm (r x : ℝ) : betaKernel r r (1 - x) = betaKernel r r x := by
  unfold betaKernel; rw [sub_sub_cancel]; ring

/-- The unnormalized potential identity in `ℝ≥0∞`, for every `s ∈ [0,1]`. -/
theorem lintegral_potential {r s : ℝ} (hr0 : 0 < r) (hr1 : r < 1 / 2) (hs : s ∈ Icc (0:ℝ) 1) :
    ∫⁻ t in Ioo (0:ℝ) 1, ENNReal.ofReal (|s - t| ^ (2 * r - 1) * (t * (1 - t)) ^ (-r))
      = ENNReal.ofReal (Beta (1 - 2 * r) (2 * r) * Beta r r / Beta r (1 - 2 * r)) := by
  have hB1 := Beta_pos hr0 (by linarith : (0:ℝ) < 1 - 2 * r)
  have hs' : 1 - s ∈ Icc (0:ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rw [lintegral_split _ hs]
  have hL : ∫⁻ t in Ioo 0 s, ENNReal.ofReal (|s - t| ^ (2 * r - 1) * (t * (1 - t)) ^ (-r))
      = ∫⁻ t in Ioo 0 s, ENNReal.ofReal ((s - t) ^ (2 * r - 1) * (t * (1 - t)) ^ (-r)) := by
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [abs_of_pos (by linarith [ht.2])]
  have hR : ∫⁻ t in Ioo s 1, ENNReal.ofReal (|s - t| ^ (2 * r - 1) * (t * (1 - t)) ^ (-r))
      = ∫⁻ t in Ioo 0 (1 - s),
          ENNReal.ofReal (((1 - s) - t) ^ (2 * r - 1) * (t * (1 - t)) ^ (-r)) := by
    rw [lintegral_reflect, sub_self]
    refine setLIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [abs_of_neg (by linarith [ht.2])]
    congr 2
    · congr 1; ring
    · congr 1; ring
  have hH : ∫⁻ u in Ioo s 1, ENNReal.ofReal (betaKernel r r u)
      = ∫⁻ u in Ioo 0 (1 - s), ENNReal.ofReal (betaKernel r r u) := by
    rw [lintegral_reflect, sub_self]
    simp_rw [betaKernel_symm]
  have key : ENNReal.ofReal (Beta r (1 - 2 * r)) *
      ((∫⁻ t in Ioo 0 s, ENNReal.ofReal (|s - t| ^ (2 * r - 1) * (t * (1 - t)) ^ (-r))) +
        ∫⁻ t in Ioo s 1, ENNReal.ofReal (|s - t| ^ (2 * r - 1) * (t * (1 - t)) ^ (-r)))
      = ENNReal.ofReal (Beta r (1 - 2 * r)) *
        ENNReal.ofReal (Beta (1 - 2 * r) (2 * r) * Beta r r / Beta r (1 - 2 * r)) := by
    rw [mul_add, hL, hR, lintegral_left hr0 hr1 hs, lintegral_left hr0 hr1 hs', ← hH, ← mul_add,
      ← lintegral_split _ hs, lintegral_betaKernel hr0 hr0, ← ENNReal.ofReal_mul hB1.le,
      ← ENNReal.ofReal_mul (Beta_pos (by linarith) (by linarith)).le]
    congr 1
    field_simp
  exact (ENNReal.mul_right_inj (by simpa using hB1) ENNReal.ofReal_ne_top).mp key

theorem Beta_combo {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1 / 2) :
    Beta (1 - 2 * r) (2 * r) * Beta r r / Beta r (1 - 2 * r) = Gamma r * Gamma (1 - r) := by
  rw [Beta_eq_Gamma (by linarith) (by linarith), Beta_eq_Gamma hr0 hr0,
    Beta_eq_Gamma hr0 (by linarith)]
  have h1 : 1 - 2 * r + 2 * r = 1 := by ring
  have h2 : r + (1 - 2 * r) = 1 - r := by ring
  rw [h1, h2, Gamma_one, ← two_mul]
  have := Gamma_pos_of_pos hr0
  have := Gamma_pos_of_pos (by linarith : (0:ℝ) < 1 - 2 * r)
  have := Gamma_pos_of_pos (by linarith : (0:ℝ) < 1 - r)
  have := Gamma_pos_of_pos (by linarith : (0:ℝ) < 2 * r)
  field_simp


/-! ### TeX lines 9--11: the two integrals are positive and finite -/

/-- TeX line 9: for `x > 0`, Mathlib's `Real.Gamma x` is the manuscript's
`Γ_E(x) = ∫_0^∞ u^{x-1} e^{-u} du`, the integral converges, and it is positive. -/
theorem gammaE_integral {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun u : ℝ => u ^ (x - 1) * exp (-u)) (Ioi 0) ∧
      Gamma x = ∫ u in Ioi (0:ℝ), u ^ (x - 1) * exp (-u) ∧ 0 < Gamma x := by
  refine ⟨?_, ?_, Gamma_pos_of_pos hx⟩
  · simpa only [mul_comm] using GammaIntegral_convergent hx
  · rw [Gamma_eq_integral hx]; simp_rw [mul_comm]

/-- TeX line 10: the Beta integral converges for `x, y > 0`. -/
theorem Beta_integrableOn {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => t ^ (x - 1) * (1 - t) ^ (y - 1)) (Ioo 0 1) :=
  betaKernel_integrableOn hx hy

/-- The manuscript's Beta agrees with Mathlib's `Complex.betaIntegral`. -/
theorem Beta_eq_betaIntegral (x y : ℝ) : Complex.betaIntegral x y = (Beta x y : ℂ) := by
  unfold Complex.betaIntegral Beta
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  exact cplx_kernel_eq x y t ht

/-! ### Lemma `L:equilibrium-gamma-beta` (TeX lines 13--22) -/

/-- TeX line 16: `Γ_E(x+1) = x Γ_E(x)` for `x > 0`. -/
theorem gamma_beta_recurrence {x : ℝ} (hx : 0 < x) : Gamma (x + 1) = x * Gamma x :=
  Gamma_add_one hx.ne'

/-- TeX lines 17--18: `Beta(x,y) = Γ_E(x)Γ_E(y)/Γ_E(x+y)` for `x, y > 0`. -/
theorem gamma_beta_beta_gamma {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Beta x y = Gamma x * Gamma y / Gamma (x + y) :=
  Beta_eq_Gamma hx hy

/-- Duplication for every real `x` (Mathlib's Legendre formula; no sign
hypothesis needed). -/
theorem gamma_beta_duplication_general (x : ℝ) :
    Gamma (2 * x) = 2 ^ (2 * x - 1) * Gamma x * Gamma (x + 1 / 2) / √π := by
  have h := Gamma_mul_Gamma_add_half x
  have hpi : 0 < √π := sqrt_pos.mpr pi_pos
  have h2 : (2:ℝ) ^ (2 * x - 1) * (2:ℝ) ^ (1 - 2 * x) = 1 := by
    rw [← rpow_add two_pos]; simp
  rw [eq_div_iff hpi.ne']
  linear_combination (-(Gamma (2 * x) * √π)) * h2 - (2:ℝ) ^ (2 * x - 1) * h

/-- TeX lines 19--20 (duplication): `Γ_E(2x) = 2^{2x-1} Γ_E(x) Γ_E(x+1/2)/√π`
for `x > 0` (the manuscript's hypothesis; the general version above shows it
is not needed). -/
theorem gamma_beta_duplication {x : ℝ} (_hx : 0 < x) :
    Gamma (2 * x) = 2 ^ (2 * x - 1) * Gamma x * Gamma (x + 1 / 2) / √π :=
  gamma_beta_duplication_general x

/-- Proof step (TeX lines 28--29): `Beta(x,x) = 2^{1-2x} Beta(1/2,x)`, and
`Γ_E(1/2) = √π`. -/
theorem gamma_beta_proof_steps {x : ℝ} (hx : 0 < x) :
    Beta x x = 2 ^ (1 - 2 * x) * Beta (1 / 2) x ∧ Gamma (1 / 2) = √π := by
  refine ⟨?_, Gamma_one_half_eq⟩
  rw [Beta_eq_Gamma hx hx, Beta_eq_Gamma (by norm_num) hx, Gamma_one_half_eq, ← two_mul,
    add_comm (1 / 2) x, gamma_beta_duplication hx]
  have hpi : 0 < √π := sqrt_pos.mpr pi_pos
  have := Gamma_pos_of_pos hx
  have := Gamma_pos_of_pos (by linarith : (0:ℝ) < x + 1 / 2)
  have hB : (2:ℝ) ^ (1 - 2 * x) = ((2:ℝ) ^ (2 * x - 1))⁻¹ := by
    rw [← rpow_neg two_pos.le]; ring_nf
  have h3 : (0:ℝ) < 2 ^ (2 * x - 1) := rpow_pos_of_pos two_pos _
  rw [hB]
  field_simp

/-- Lemma `L:equilibrium-gamma-beta`, all three identities, under exactly the
manuscript hypothesis "for positive arguments" (`x > 0`, `y > 0`). -/
theorem gamma_beta_paper {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Gamma (x + 1) = x * Gamma x ∧
      Beta x y = Gamma x * Gamma y / Gamma (x + y) ∧
      Gamma (2 * x) = 2 ^ (2 * x - 1) * Gamma x * Gamma (x + 1 / 2) / √π :=
  ⟨gamma_beta_recurrence hx, gamma_beta_beta_gamma hx hy, gamma_beta_duplication hx⟩

/-! ### Lemma `L:temporal-equilibrium` (TeX lines 37--51) -/

/-- The density `f_a(t) = [t(1-t)]^{-r}/(Γ_E(r)Γ_E(1-r))`, `r = (1-a)/2`
(TeX line 40, `E:temporal-equilibrium-density`). -/
def density (a t : ℝ) : ℝ :=
  (t * (1 - t)) ^ (-((1 - a) / 2)) / (Gamma ((1 - a) / 2) * Gamma (1 - (1 - a) / 2))

/-- The mass `M_a = ∫_0^1 f_a(t) dt` (TeX line 46). -/
def mass (a : ℝ) : ℝ := ∫ t in Ioo (0:ℝ) 1, density a t

lemma normalizer_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < Gamma ((1 - a) / 2) * Gamma (1 - (1 - a) / 2) :=
  mul_pos (Gamma_pos_of_pos (by linarith)) (Gamma_pos_of_pos (by linarith))

lemma measurable_density (a : ℝ) : Measurable (density a) := by
  unfold density; fun_prop

/-- Positivity (TeX line 42): `f_a(t) > 0` for `0 < t < 1`. -/
theorem density_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ t ∈ Ioo (0:ℝ) 1, 0 < density a t := by
  intro t ht
  have : 0 < t * (1 - t) := mul_pos ht.1 (by linarith [ht.2])
  exact div_pos (rpow_pos_of_pos this _) (normalizer_pos ha0 ha1)

lemma rpow_prod_eq_betaKernel {t p : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) :
    (t * (1 - t)) ^ (-p) = betaKernel (1 - p) (1 - p) t := by
  unfold betaKernel
  rw [mul_rpow ht.1.le (by linarith [ht.2])]
  congr 2 <;> ring

/-- `f_a ∈ L^1(0,1)` (TeX line 42), as integrability on `(0,1)`. -/
theorem density_integrableOn {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    IntegrableOn (density a) (Ioo 0 1) := by
  have h : IntegrableOn (fun t => betaKernel (1 - (1 - a) / 2) (1 - (1 - a) / 2) t /
      (Gamma ((1 - a) / 2) * Gamma (1 - (1 - a) / 2))) (Ioo 0 1) :=
    (betaKernel_integrableOn (x := 1 - (1 - a) / 2) (y := 1 - (1 - a) / 2)
      (by linarith) (by linarith)).div_const _
  refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioo
  simp only [density]
  rw [rpow_prod_eq_betaKernel ht]

/-- `f_a ∈ L^1(0,1)` as `MemLp _ 1`. -/
theorem density_memLp_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    MemLp (density a) 1 (volume.restrict (Ioo 0 1)) :=
  memLp_one_iff_integrable.mpr (density_integrableOn ha0 ha1)

/-- `f_a ∈ L^2(0,1)` (TeX line 42): `f_a²` is integrable on `(0,1)`.  Only
`a > 0` is used (`-2r = a - 1 > -1`, TeX line 85); `a < 1` is the lemma's
standing hypothesis and is kept for fidelity. -/
theorem density_sq_integrableOn {a : ℝ} (ha0 : 0 < a) (_ha1 : a < 1) :
    IntegrableOn (fun t => density a t ^ 2) (Ioo 0 1) := by
  have h : IntegrableOn (fun t => betaKernel a a t /
      (Gamma ((1 - a) / 2) * Gamma (1 - (1 - a) / 2)) ^ 2) (Ioo 0 1) :=
    (betaKernel_integrableOn (x := a) (y := a) ha0 ha0).div_const _
  refine IntegrableOn.congr_fun h (fun t ht => ?_) measurableSet_Ioo
  have hp : 0 < t * (1 - t) := mul_pos ht.1 (by linarith [ht.2])
  have hsq : ((t * (1 - t)) ^ (-((1 - a) / 2))) ^ 2 = betaKernel a a t := by
    rw [← rpow_natCast, ← rpow_mul hp.le]
    have e : -((1 - a) / 2) * ((2 : ℕ) : ℝ) = -(1 - a) := by push_cast; ring
    rw [e, rpow_prod_eq_betaKernel ht, sub_sub_cancel]
  simp only [density]
  rw [div_pow, hsq]

/-- `f_a ∈ L^2(0,1)` as `MemLp _ 2`. -/
theorem density_memLp_two {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    MemLp (density a) 2 (volume.restrict (Ioo 0 1)) :=
  (memLp_two_iff_integrable_sq (measurable_density a).aestronglyMeasurable).mpr
    (density_sq_integrableOn ha0 ha1)

/-- From a finite `ℝ≥0∞` value of a nonnegative integrand to integrability and
the Bochner value. -/
lemma integrableOn_and_integral_of_lintegral {f : ℝ → ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hf : Measurable f) (hnn : ∀ t ∈ S, 0 ≤ f t) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ t in S, ENNReal.ofReal (f t) = ENNReal.ofReal c) :
    IntegrableOn f S ∧ ∫ t in S, f t = c := by
  have hae : 0 ≤ᵐ[volume.restrict S] f := ae_restrict_of_forall_mem hS hnn
  refine ⟨⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hae).mpr ?_⟩, ?_⟩
  · rw [h]; exact ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae hae hf.aestronglyMeasurable, h,
      ENNReal.toReal_ofReal hc]

/-- The potential identity (TeX lines 44--45,
`E:temporal-equilibrium-potential`): for `0 < a < 1` and every `s ∈ [0,1]`
(endpoints included), the integrand is integrable on `(0,1)` and
`∫_0^1 |s-t|^{-a} f_a(t) dt = 1`. -/
theorem potential_eq_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ s ∈ Icc (0:ℝ) 1,
      IntegrableOn (fun t => |s - t| ^ (-a) * density a t) (Ioo 0 1) ∧
        ∫ t in Ioo (0:ℝ) 1, |s - t| ^ (-a) * density a t = 1 := by
  intro s hs
  set r := (1 - a) / 2 with hr
  have hr0 : 0 < r := by linarith
  have hr1 : r < 1 / 2 := by linarith
  have hC := normalizer_pos ha0 ha1
  have e1 : 1 - 2 * r = a := by rw [hr]; ring
  have e2 : 2 * r - 1 = -a := by rw [hr]; ring
  refine integrableOn_and_integral_of_lintegral measurableSet_Ioo
    (by unfold density; fun_prop) (fun t ht => mul_nonneg (rpow_nonneg (abs_nonneg _) _)
      (density_pos ha0 ha1 t ht).le) zero_le_one ?_
  have hP := lintegral_potential hr0 hr1 hs
  rw [Beta_combo hr0 hr1, e2] at hP
  have : ∀ t ∈ Ioo (0:ℝ) 1, ENNReal.ofReal (|s - t| ^ (-a) * density a t)
      = ENNReal.ofReal (|s - t| ^ (-a) * (t * (1 - t)) ^ (-r)) *
        ENNReal.ofReal (Gamma r * Gamma (1 - r))⁻¹ := by
    intro t ht
    have hp : 0 ≤ t * (1 - t) := mul_nonneg ht.1.le (by linarith [ht.2])
    rw [← ENNReal.ofReal_mul (mul_nonneg (rpow_nonneg (abs_nonneg _) _) (rpow_nonneg hp _))]
    congr 1
    simp only [density, ← hr]
    rw [div_eq_mul_inv]; ring
  rw [setLIntegral_congr_fun measurableSet_Ioo this,
    lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hP, ← ENNReal.ofReal_mul (by
      rw [hr]; exact hC.le), mul_inv_cancel₀ (by rw [hr]; exact hC.ne')]

/-- The mass (TeX lines 46--48, `E:temporal-equilibrium-mass`): `f_a` is
integrable on `(0,1)` and
`M_a = Γ_E((1+a)/2) / (Γ_E(1+a) Γ_E((1-a)/2))`. -/
theorem mass_eq {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    IntegrableOn (density a) (Ioo 0 1) ∧
      mass a = Gamma ((1 + a) / 2) / (Gamma (1 + a) * Gamma ((1 - a) / 2)) := by
  refine ⟨density_integrableOn ha0 ha1, ?_⟩
  have e : 1 - (1 - a) / 2 = (1 + a) / 2 := by ring
  have hcongr : ∀ t ∈ Ioo (0:ℝ) 1, density a t = betaKernel ((1 + a) / 2) ((1 + a) / 2) t /
      (Gamma ((1 - a) / 2) * Gamma ((1 + a) / 2)) := by
    intro t ht
    simp only [density]
    rw [rpow_prod_eq_betaKernel ht, e]
  unfold mass
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr, integral_div]
  change Beta _ _ / _ = _
  rw [Beta_eq_Gamma (by linarith) (by linarith)]
  have e2 : (1 + a) / 2 + (1 + a) / 2 = 1 + a := by ring
  rw [e2]
  have := Gamma_pos_of_pos (by linarith : (0:ℝ) < (1 + a) / 2)
  have := Gamma_pos_of_pos (by linarith : (0:ℝ) < (1 - a) / 2)
  have := Gamma_pos_of_pos (by linarith : (0:ℝ) < 1 + a)
  field_simp

/-- `M_a > 0` (TeX line 48). -/
theorem mass_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < mass a := by
  rw [(mass_eq ha0 ha1).2]
  have := Gamma_pos_of_pos (by linarith : (0:ℝ) < (1 + a) / 2)
  have := Gamma_pos_of_pos (by linarith : (0:ℝ) < (1 - a) / 2)
  have := Gamma_pos_of_pos (by linarith : (0:ℝ) < 1 + a)
  positivity

/-- Remark (not in the TeX): by Euler reflection the normalizer is
`Γ_E(r) Γ_E(1-r) = π / sin(π r)`. -/
theorem normalizer_eq_pi_div_sin (a : ℝ) :
    Gamma ((1 - a) / 2) * Gamma (1 - (1 - a) / 2) = π / sin (π * ((1 - a) / 2)) :=
  Gamma_mul_Gamma_one_sub _

/-- Lemma `L:temporal-equilibrium`, under exactly its hypothesis `0 < a < 1`
(with `r = (1-a)/2` built into `density`): `f_a` is positive on `(0,1)`,
belongs to `L^1(0,1) ∩ L^2(0,1)`, has potential identically `1` on `[0,1]`
(with integrability), and its mass is
`Γ_E((1+a)/2)/(Γ_E(1+a)Γ_E((1-a)/2)) > 0`. -/
theorem temporal_equilibrium_paper {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (∀ t ∈ Ioo (0:ℝ) 1, 0 < density a t) ∧
      MemLp (density a) 1 (volume.restrict (Ioo 0 1)) ∧
      MemLp (density a) 2 (volume.restrict (Ioo 0 1)) ∧
      (∀ s ∈ Icc (0:ℝ) 1,
        IntegrableOn (fun t => |s - t| ^ (-a) * density a t) (Ioo 0 1) ∧
          ∫ t in Ioo (0:ℝ) 1, |s - t| ^ (-a) * density a t = 1) ∧
      (IntegrableOn (density a) (Ioo 0 1) ∧
        ∫ t in Ioo (0:ℝ) 1, density a t
          = Gamma ((1 + a) / 2) / (Gamma (1 + a) * Gamma ((1 - a) / 2))) ∧
      0 < ∫ t in Ioo (0:ℝ) 1, density a t :=
  ⟨density_pos ha0 ha1, density_memLp_one ha0 ha1, density_memLp_two ha0 ha1,
    potential_eq_one ha0 ha1, mass_eq ha0 ha1, mass_pos ha0 ha1⟩

end StratonovichHAMSecondMoment.TemporalEquilibrium
