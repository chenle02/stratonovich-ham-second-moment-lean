module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Lemma `L:tube-rayleigh-tail` (Exact Rayleigh tail bound) of
`notes/integrated_gaussian_tubes.tex`.

Manuscript hypotheses made explicit here:
* `G` is defined on all of `ℝ` (Lean convention); the growth bound is assumed
  only on the manuscript domain `r ≥ 0` (the preceding proposition has
  `G : [0, ∞) → ℝ`).  The tail proof uses it only for `r ≥ M`.
* "Borel" is `Measurable G`.
* `δ > 0` (the section fixes `0 < δ < 1`; only `δ > 0` is used).
* Integrability on `(M, ∞)` is part of the conclusion, since the Bochner
  integral of a non-integrable function is `0` in Lean.
-/
public import Mathlib

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Set Topology

namespace StratonovichHAMSecondMoment.RayleighTail

/-- The finite scalar cutoff inequality: for `r ≥ M`,
`C r^ν - r²/2 ≤ -M²/8 - r²/8`. -/
theorem cutoff_split (M r C ν : ℝ)
    (hM : 0 < M) (hr : M ≤ r) (hC : 0 ≤ C)
    (_hν1 : 1 < ν) (hν2 : ν < 2) (hcut : 4 * C ≤ M ^ (2 - ν)) :
    C * r ^ ν - r ^ 2 / 2 ≤ -M ^ 2 / 8 - r ^ 2 / 8 := by
  have hrpos : 0 < r := lt_of_lt_of_le hM hr
  have hmono : M ^ (2 - ν) ≤ r ^ (2 - ν) :=
    Real.rpow_le_rpow hM.le hr (by linarith)
  have hs := mul_le_mul_of_nonneg_right (hcut.trans hmono)
    (Real.rpow_nonneg hrpos.le ν)
  have hpow : r ^ (2 - ν) * r ^ ν = r ^ 2 := by
    calc
      _ = r ^ ((2 - ν) + ν) := (Real.rpow_add hrpos _ _).symm
      _ = r ^ (2 : ℝ) := by congr 1; ring
      _ = r ^ (2 : ℕ) := Real.rpow_natCast r 2
  rw [hpow] at hs
  have hprod : 0 ≤ (r - M) * (r + M) :=
    mul_nonneg (sub_nonneg.mpr hr) (by linarith)
  have hCr : 0 ≤ C * r ^ ν := mul_nonneg hC (Real.rpow_nonneg hrpos.le ν)
  nlinarith [hs, hprod, hCr]

/-- Exact Gaussian-weight tail: `∫_M^∞ (r/δ) e^{-r²/(8δ)} dr = 4 e^{-M²/(8δ)}`,
with integrability. -/
theorem gaussian_weight_tail (δ M : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M) :
    IntegrableOn (fun r : ℝ => r / δ * Real.exp (-(r ^ 2) / (8 * δ))) (Ioi M) ∧
      ∫ r in Ioi M, r / δ * Real.exp (-(r ^ 2) / (8 * δ)) =
        4 * Real.exp (-(M ^ 2) / (8 * δ)) := by
  set F : ℝ → ℝ := fun r => -4 * Real.exp (-(r ^ 2) / (8 * δ)) with hF
  have hderiv : ∀ x ∈ Ici M,
      HasDerivAt F (x / δ * Real.exp (-(x ^ 2) / (8 * δ))) x := by
    intro x _
    have h1 : HasDerivAt (fun r : ℝ => -(r ^ 2) / (8 * δ)) (-(2 * x) / (8 * δ)) x := by
      have := ((hasDerivAt_pow 2 x).neg).div_const (8 * δ)
      simpa using this
    have h2 := (h1.exp).const_mul (-4)
    convert h2 using 1
    field_simp
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hq : Tendsto (fun r : ℝ => -(r ^ 2) / (8 * δ)) atTop atBot := by
      have : Tendsto (fun r : ℝ => r ^ 2 / (8 * δ)) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).atTop_div_const (by positivity)
      have := tendsto_neg_atTop_atBot.comp this
      refine this.congr (fun r => ?_)
      simp [neg_div]
    have := (Real.tendsto_exp_atBot.comp hq).const_mul (-4)
    simpa [hF] using this
  have hpos : ∀ x ∈ Ioi M, 0 ≤ x / δ * Real.exp (-(x ^ 2) / (8 * δ)) := by
    intro x hx
    have hx0 : 0 ≤ x := hM.trans (le_of_lt hx)
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp [hF]

/-- Lemma `L:tube-rayleigh-tail`, display `E:tube-rayleigh-tail`:
if `G` is Borel, `G r ≤ A₀ + C r^ν` for `r ≥ 0`, `C ≥ 0`, `1 < ν < 2`,
`M > 0` and `4C ≤ M^(2-ν)`, then the integrand is integrable on `(M, ∞)` and
`∫_M^∞ (r/δ) e^{(G(r)-r²/2)/δ} dr ≤ 4 e^{(A₀-M²/4)/δ}`. -/
theorem rayleigh_tail (G : ℝ → ℝ) (hG : Measurable G) (A₀ C ν M δ : ℝ)
    (hgrowth : ∀ r, 0 ≤ r → G r ≤ A₀ + C * r ^ ν)
    (hC : 0 ≤ C) (hν1 : 1 < ν) (hν2 : ν < 2) (hδ : 0 < δ)
    (hM : 0 < M) (hcut : 4 * C ≤ M ^ (2 - ν)) :
    IntegrableOn (fun r : ℝ => r / δ * Real.exp ((G r - r ^ 2 / 2) / δ)) (Ioi M) ∧
      ∫ r in Ioi M, r / δ * Real.exp ((G r - r ^ 2 / 2) / δ) ≤
        4 * Real.exp ((A₀ - M ^ 2 / 4) / δ) := by
  obtain ⟨hgint, hgval⟩ := gaussian_weight_tail δ M hδ hM.le
  set K : ℝ := Real.exp ((A₀ - M ^ 2 / 8) / δ) with hK
  set g : ℝ → ℝ := fun r => r / δ * Real.exp (-(r ^ 2) / (8 * δ)) with hg
  set f : ℝ → ℝ := fun r => r / δ * Real.exp ((G r - r ^ 2 / 2) / δ) with hf
  have hfmeas : Measurable f := by
    apply Measurable.mul
    · exact measurable_id.div_const δ
    · exact Real.measurable_exp.comp
        ((hG.sub ((measurable_id.pow_const 2).div_const 2)).div_const δ)
  have hpt : ∀ r ∈ Ioi M, 0 ≤ f r ∧ f r ≤ K * g r := by
    intro r hr
    have hr' : M ≤ r := le_of_lt hr
    have hr0 : 0 < r := hM.trans hr
    have hsplit := cutoff_split M r C ν hM hr' hC hν1 hν2 hcut
    have hGr := hgrowth r hr0.le
    have hexp : (G r - r ^ 2 / 2) / δ ≤ (A₀ - M ^ 2 / 8) / δ + -(r ^ 2) / (8 * δ) := by
      have : G r - r ^ 2 / 2 ≤ (A₀ - M ^ 2 / 8) + -(r ^ 2) / 8 := by linarith
      calc (G r - r ^ 2 / 2) / δ ≤ ((A₀ - M ^ 2 / 8) + -(r ^ 2) / 8) / δ :=
            div_le_div_of_nonneg_right this hδ.le
        _ = _ := by field_simp
    have hrd : 0 ≤ r / δ := div_nonneg hr0.le hδ.le
    refine ⟨mul_nonneg hrd (Real.exp_nonneg _), ?_⟩
    have := Real.exp_le_exp.mpr hexp
    rw [Real.exp_add] at this
    calc f r = r / δ * Real.exp ((G r - r ^ 2 / 2) / δ) := rfl
      _ ≤ r / δ * (K * Real.exp (-(r ^ 2) / (8 * δ))) :=
          mul_le_mul_of_nonneg_left this hrd
      _ = K * g r := by simp only [hg]; ring
  have hKg : IntegrableOn (fun r => K * g r) (Ioi M) := hgint.const_mul K
  have hfint : IntegrableOn f (Ioi M) := by
    refine Integrable.mono' hKg hfmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hpt r hr).1]
    exact (hpt r hr).2
  refine ⟨hfint, ?_⟩
  calc ∫ r in Ioi M, f r ≤ ∫ r in Ioi M, K * g r :=
        setIntegral_mono_on hfint hKg measurableSet_Ioi (fun r hr => (hpt r hr).2)
    _ = K * (4 * Real.exp (-(M ^ 2) / (8 * δ))) := by
        rw [integral_const_mul, hgval]
    _ = 4 * Real.exp ((A₀ - M ^ 2 / 4) / δ) := by
        rw [hK, mul_left_comm, ← Real.exp_add]
        congr 2
        field_simp
        ring

/-- The proof's remark "on `[0, M]` the integral is finite as well": under the
growth bound on `r ≥ 0` (here with `C ≥ 0`, `ν > 0` used for monotonicity of
`r ↦ r^ν`), the integrand is integrable on `[0, M]`. -/
theorem rayleigh_head_integrable (G : ℝ → ℝ) (hG : Measurable G) (A₀ C ν M δ : ℝ)
    (hgrowth : ∀ r, 0 ≤ r → G r ≤ A₀ + C * r ^ ν)
    (hC : 0 ≤ C) (hν1 : 1 < ν) (hδ : 0 < δ) (hM : 0 < M) :
    IntegrableOn (fun r : ℝ => r / δ * Real.exp ((G r - r ^ 2 / 2) / δ)) (Icc 0 M) := by
  set f : ℝ → ℝ := fun r => r / δ * Real.exp ((G r - r ^ 2 / 2) / δ) with hf
  have hfmeas : Measurable f := by
    apply Measurable.mul
    · exact measurable_id.div_const δ
    · exact Real.measurable_exp.comp
        ((hG.sub ((measurable_id.pow_const 2).div_const 2)).div_const δ)
  set B : ℝ := M / δ * Real.exp ((A₀ + C * M ^ ν) / δ)
  refine Measure.integrableOn_of_bounded (M := B) (by simp)
    hfmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun r hr => ?_)
  obtain ⟨hr0, hrM⟩ := hr
  have hGr := hgrowth r hr0
  have hpow : r ^ ν ≤ M ^ ν := Real.rpow_le_rpow hr0 hrM (by linarith)
  have hsq : 0 ≤ r ^ 2 / 2 := by positivity
  have hexp : (G r - r ^ 2 / 2) / δ ≤ (A₀ + C * M ^ ν) / δ := by
    apply div_le_div_of_nonneg_right _ hδ.le
    nlinarith [mul_le_mul_of_nonneg_left hpow hC]
  have hrd : 0 ≤ r / δ := div_nonneg hr0 hδ.le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hrd (Real.exp_nonneg _))]
  exact mul_le_mul (div_le_div_of_nonneg_right hrM hδ.le) (Real.exp_le_exp.mpr hexp)
    (Real.exp_nonneg _) (div_nonneg hM.le hδ.le)

/-- `L:tube-rayleigh-tail` with the manuscript's own hypotheses, including the
section's standing range `0 < δ < 1`: for Borel `G` with
`G r ≤ A₀ + C r^ν` (`r ≥ 0`), `C ≥ 0`, `1 < ν < 2`, `M > 0` and
`4C ≤ M^(2-ν)`, the tail integrand is integrable on `(M, ∞)` with the bound
`E:tube-rayleigh-tail`, and it is integrable on `[0, M]`. The lemma's
"In particular" application to another proposition is not formalized. -/
theorem rayleigh_tail_paper (G : ℝ → ℝ) (hG : Measurable G) (A₀ C ν M δ : ℝ)
    (hgrowth : ∀ r, 0 ≤ r → G r ≤ A₀ + C * r ^ ν)
    (hC : 0 ≤ C) (hν1 : 1 < ν) (hν2 : ν < 2) (hδ : 0 < δ) (_hδ1 : δ < 1)
    (hM : 0 < M) (hcut : 4 * C ≤ M ^ (2 - ν)) :
    IntegrableOn (fun r : ℝ => r / δ * Real.exp ((G r - r ^ 2 / 2) / δ)) (Ioi M) ∧
      (∫ r in Ioi M, r / δ * Real.exp ((G r - r ^ 2 / 2) / δ) ≤
        4 * Real.exp ((A₀ - M ^ 2 / 4) / δ)) ∧
      IntegrableOn (fun r : ℝ => r / δ * Real.exp ((G r - r ^ 2 / 2) / δ)) (Icc 0 M) :=
  ⟨(rayleigh_tail G hG A₀ C ν M δ hgrowth hC hν1 hν2 hδ hM hcut).1,
    (rayleigh_tail G hG A₀ C ν M δ hgrowth hC hν1 hν2 hδ hM hcut).2,
    rayleigh_head_integrable G hG A₀ C ν M δ hgrowth hC hν1 hδ hM⟩

end StratonovichHAMSecondMoment.RayleighTail
