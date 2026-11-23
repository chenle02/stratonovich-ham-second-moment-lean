module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

In-domain control for the Gaussian Fourier pairing step of
`L:phase-contractions` (main TeX file `notes/notes_stratonovich_ham_second_moment.tex`
at revision edf7085f: the lemma at lines 2509-2523, the pairing display at lines
2534-2542, the standing assumptions of `S:static-phase` at lines 2490-2493).

The pairing step is the inequality `∫ e^{-s|q+ξ|²} μ(dξ) ≤ ∫ e^{-s|ξ|²} μ(dξ)`
(package theorem `PhaseContractions.gauss_shift_le`).  The wrong variant
"shift invariance" replaces `≤` by `=` for every `q`.  This module shows that
the variant fails for every nonzero spectral measure that is `α`-homogeneous
with `α < d` and tempered (`not_gauss_shift_invariant`); in particular for every
covariance of the class `PhaseContractions.PhaseCovariance` with `μ ≠ 0`
(`not_gauss_shift_invariant_phase`), which is the manuscript domain of
`S:static-phase` (`d = 3`, `0 < α < 2`).

Proof route (auxiliary to the Lean development; the TeX has no such
statement).  If `F(q) = ∫ e^{-s|q+ξ|²} μ(dξ)` were constant, equal to
`F(0) > 0`, then averaging against `e^{-t|q|²} dq` over `ℝ^d` gives
`F(0) (π/t)^{d/2}` (growth `t^{-d/2}` of the volume as `t → 0`), whereas the
pointwise bound `e^{-t|q|²-s|q+ξ|²} ≤ e^{-(t/2)|ξ|²} e^{-(s/2)|q+ξ|²}`
(`2t ≤ s`) and Tonelli bound the same average by
`(2π/s)^{d/2} ∫ e^{-(t/2)|ξ|²} μ(dξ) = (2π/s)^{d/2} (t/2)^{-α/2} ∫ e^{-|ξ|²} μ(dξ)`
(growth `t^{-α/2}` of the `μ`-mass by homogeneity).  Since `α < d`, letting
`t → 0` forces `F(0) = 0`.  This is the scaling argument "volume `R^d` against
`μ(B_{2R}) ∝ R^α`" with a Gaussian window in place of a ball, so no tail
estimate is needed.  No Fourier inversion and no explicit Riesz pair is used.

Hypotheses of `not_gauss_shift_invariant`: `μ` locally finite (for Tonelli),
tempered (integrability of Gaussians), `SpectralHomogeneous μ α`, `α < d`,
`μ ≠ 0`, `s > 0`.  `μ ≠ 0` is necessary: for `μ = 0` both sides vanish
(`phaseCovariance_zero` shows the zero pair lies in the class).
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.SpectralHomog
public import StratonovichHAMSecondMoment.MaskedSpectralGrowth
public import StratonovichHAMSecondMoment.PhaseContractions

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter Topology
open scoped ENNReal

namespace StratonovichHAMSecondMoment.PhaseShiftControl

open HomogHypothesis SpectralHomog MaskedSpectralGrowth PhaseContractions

variable {d : ℕ}

/-- Auxiliary to the Lean proof route.  The pointwise weight comparison
`t|q|² + s|q+ξ|² ≥ (t/2)|ξ|² + (s/2)|q+ξ|²` for `0 ≤ t`, `2t ≤ s`. -/
theorem weight_le (q ξ : Rd d) {s t : ℝ} (ht : 0 ≤ t) (hts : 2 * t ≤ s) :
    t / 2 * ‖ξ‖ ^ 2 + s / 2 * ‖q + ξ‖ ^ 2 ≤ t * ‖q‖ ^ 2 + s * ‖q + ξ‖ ^ 2 := by
  have h1 : ‖ξ‖ ≤ ‖q + ξ‖ + ‖q‖ := by
    calc ‖ξ‖ = ‖(q + ξ) - q‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖q + ξ‖ + ‖q‖ := norm_sub_le _ _
  have h2 : ‖ξ‖ ^ 2 ≤ 2 * ‖q + ξ‖ ^ 2 + 2 * ‖q‖ ^ 2 := by
    nlinarith [norm_nonneg ξ, norm_nonneg q, norm_nonneg (q + ξ), sq_nonneg (‖q + ξ‖ - ‖q‖)]
  nlinarith [sq_nonneg ‖q + ξ‖]

/-- Auxiliary to the Lean proof route.  The Gaussian average of the shifted
spectral integrals is bounded by Tonelli and `weight_le`:
`∫ e^{-t|q|²} ∫ e^{-s|q+ξ|²} μ(dξ) dq ≤ ∫ e^{-(t/2)|ξ|²} μ(dξ) · ∫ e^{-(s/2)|v|²} dv`
(as lower integrals, `0 ≤ t`, `2t ≤ s`). -/
theorem lintegral_average_le (μ : Measure (Rd d)) [SFinite μ] {s t : ℝ} (ht : 0 ≤ t)
    (hts : 2 * t ≤ s) :
    ∫⁻ q, ENNReal.ofReal (Real.exp (-(t * ‖q‖ ^ 2))) *
        ∫⁻ ξ, ENNReal.ofReal (Real.exp (-(s * ‖q + ξ‖ ^ 2))) ∂μ ≤
      (∫⁻ ξ, ENNReal.ofReal (Real.exp (-(t / 2 * ‖ξ‖ ^ 2))) ∂μ) *
        ∫⁻ v : Rd d, ENNReal.ofReal (Real.exp (-(s / 2 * ‖v‖ ^ 2))) := by
  have hpt : ∀ q ξ : Rd d,
      ENNReal.ofReal (Real.exp (-(t * ‖q‖ ^ 2))) *
          ENNReal.ofReal (Real.exp (-(s * ‖q + ξ‖ ^ 2))) ≤
        ENNReal.ofReal (Real.exp (-(t / 2 * ‖ξ‖ ^ 2))) *
          ENNReal.ofReal (Real.exp (-(s / 2 * ‖q + ξ‖ ^ 2))) := by
    intro q ξ
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [weight_le q ξ ht hts]))
  calc ∫⁻ q, ENNReal.ofReal (Real.exp (-(t * ‖q‖ ^ 2))) *
          ∫⁻ ξ, ENNReal.ofReal (Real.exp (-(s * ‖q + ξ‖ ^ 2))) ∂μ
      = ∫⁻ q, ∫⁻ ξ, ENNReal.ofReal (Real.exp (-(t * ‖q‖ ^ 2))) *
          ENNReal.ofReal (Real.exp (-(s * ‖q + ξ‖ ^ 2))) ∂μ := by
        refine lintegral_congr fun q => ?_
        rw [lintegral_const_mul _ (by fun_prop)]
    _ ≤ ∫⁻ q, ∫⁻ ξ, ENNReal.ofReal (Real.exp (-(t / 2 * ‖ξ‖ ^ 2))) *
          ENNReal.ofReal (Real.exp (-(s / 2 * ‖q + ξ‖ ^ 2))) ∂μ :=
        lintegral_mono fun q => lintegral_mono fun ξ => hpt q ξ
    _ = ∫⁻ ξ, (∫⁻ q, ENNReal.ofReal (Real.exp (-(t / 2 * ‖ξ‖ ^ 2))) *
          ENNReal.ofReal (Real.exp (-(s / 2 * ‖q + ξ‖ ^ 2)))) ∂μ := by
        refine lintegral_lintegral_swap (Measurable.aemeasurable ?_)
        exact (by fun_prop : Measurable fun p : Rd d × Rd d =>
          ENNReal.ofReal (Real.exp (-(t / 2 * ‖p.2‖ ^ 2))) *
            ENNReal.ofReal (Real.exp (-(s / 2 * ‖p.1 + p.2‖ ^ 2))))
    _ = ∫⁻ ξ, ENNReal.ofReal (Real.exp (-(t / 2 * ‖ξ‖ ^ 2))) *
          (∫⁻ v : Rd d, ENNReal.ofReal (Real.exp (-(s / 2 * ‖v‖ ^ 2)))) ∂μ := by
        refine lintegral_congr fun ξ => ?_
        rw [lintegral_const_mul _ (by fun_prop),
          lintegral_add_right_eq_self (fun v : Rd d => ENNReal.ofReal
            (Real.exp (-(s / 2 * ‖v‖ ^ 2)))) ξ]
    _ = _ := lintegral_mul_const _ (by fun_prop)

/-- Auxiliary to the Lean proof route.  The Gaussian integral over `ℝ^d`:
`∫ e^{-b|v|²} dv = (π/b)^{d/2}` (`b > 0`), from Mathlib's
`integral_rexp_neg_mul_sq_norm`. -/
theorem integral_gauss_volume {b : ℝ} (hb : 0 < b) :
    ∫ v : Rd d, Real.exp (-(b * ‖v‖ ^ 2)) = (π / b) ^ ((d : ℝ) / 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Rd d) hb
  simpa [neg_mul, finrank_euclideanSpace] using h

/-- Auxiliary to the Lean proof route.  The Gaussian `e^{-b|v|²}` (`b > 0`) is
Lebesgue integrable on `ℝ^d`. -/
theorem integrable_gauss_volume {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : Rd d => Real.exp (-(b * ‖v‖ ^ 2))) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_gauss_volume hb]
  exact (Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _).ne'

/-- Auxiliary to the Lean proof route.  The lower-integral form of
`integral_gauss_volume`. -/
theorem lintegral_gauss_volume {b : ℝ} (hb : 0 < b) :
    ∫⁻ v : Rd d, ENNReal.ofReal (Real.exp (-(b * ‖v‖ ^ 2))) =
      ENNReal.ofReal ((π / b) ^ ((d : ℝ) / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gauss_volume hb)
    (ae_of_all _ fun _ => (Real.exp_pos _).le), integral_gauss_volume hb]

/-- Auxiliary to the Lean proof route.  Homogeneity of Gaussian `μ`-masses:
for `SpectralHomogeneous μ α` and `u > 0`,
`∫ e^{-u|ξ|²} μ(dξ) = u^{-α/2} ∫ e^{-|ξ|²} μ(dξ)` (the `t^{-α/2}` growth of the
`μ`-mass, the analogue of `μ(B_R) = R^α μ(B_1)`). -/
theorem integral_gauss_homog {μ : Measure (Rd d)} {alpha : ℝ}
    (hI : SpectralHomogeneous μ alpha) (u : ℝ) (hu : 0 < u) :
    ∫ ξ, Real.exp (-(u * ‖ξ‖ ^ 2)) ∂μ = u ^ (-(alpha / 2)) * ∫ ξ, Real.exp (-‖ξ‖ ^ 2) ∂μ := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have h := integral_comp_smul hI (Real.sqrt u) hs (fun ξ => Real.exp (-‖ξ‖ ^ 2))
    (by fun_prop)
  have hpt : ∀ ξ : Rd d, Real.exp (-‖Real.sqrt u • ξ‖ ^ 2) = Real.exp (-(u * ‖ξ‖ ^ 2)) := by
    intro ξ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow, Real.sq_sqrt hu.le]
  simp only [hpt] at h
  rw [h, Real.sqrt_eq_rpow, ← Real.rpow_mul hu.le]
  congr 2
  ring

/-- **In-domain failure of shift invariance** (control for the pairing step of
`L:phase-contractions`, main TeX lines 2534-2542 at edf7085f).  Let `μ` be a
nonzero, locally finite, tempered measure on `ℝ^d` with `μ(cA) = c^α μ(A)` and
`α < d`, and let `s > 0`.  Then `q ↦ ∫ e^{-s|q+ξ|²} μ(dξ)` is not constant:
the comparison `≤` of `gauss_shift_le` cannot be an equality for every `q`.
Proof: `lintegral_average_le` against the volume and the `μ`-mass growth
(`integral_gauss_volume`, `integral_gauss_homog`), then `t → 0`. -/
theorem not_gauss_shift_invariant {μ : Measure (Rd d)} [IsLocallyFiniteMeasure μ]
    {alpha : ℝ} (hμt : IsTempered μ) (hI : SpectralHomogeneous μ alpha)
    (hαd : alpha < d) (hμ : μ ≠ 0) {s : ℝ} (hs : 0 < s) :
    ¬ ∀ q : Rd d, ∫ ξ, Real.exp (-(s * ‖q + ξ‖ ^ 2)) ∂μ =
      ∫ ξ, Real.exp (-(s * ‖ξ‖ ^ 2)) ∂μ := by
  intro H
  set K := ∫ ξ, Real.exp (-(s * ‖ξ‖ ^ 2)) ∂μ with hK
  set K1 := ∫ ξ, Real.exp (-‖ξ‖ ^ 2) ∂μ with hK1
  have : NeZero μ := ⟨hμ⟩
  have hKpos : 0 < K := integral_exp_pos (integrable_gauss_zero hμt hs)
  have hK1nn : 0 ≤ K1 := integral_nonneg fun _ => (Real.exp_pos _).le
  set P := (π / (s / 2)) ^ ((d : ℝ) / 2) with hP
  have hPnn : 0 ≤ P := (Real.rpow_pos_of_pos (div_pos Real.pi_pos (half_pos hs)) _).le
  have key : ∀ t : ℝ, 0 < t → 2 * t ≤ s →
      (π / t) ^ ((d : ℝ) / 2) * K ≤ (t / 2) ^ (-(alpha / 2)) * K1 * P := by
    intro t ht hts
    have hshift : ∀ q : Rd d,
        ∫⁻ ξ, ENNReal.ofReal (Real.exp (-(s * ‖q + ξ‖ ^ 2))) ∂μ = ENNReal.ofReal K := by
      intro q
      have hint : Integrable (fun ξ : Rd d => Real.exp (-(s * ‖q + ξ‖ ^ 2))) μ := by
        refine (integrable_gauss_of_tempered hμt hs (-q)).congr (ae_of_all _ fun ξ => ?_)
        simp only [sub_neg_eq_add, add_comm ξ q]
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (ae_of_all _ fun _ => (Real.exp_pos _).le), H q]
    have h := lintegral_average_le μ ht.le hts
    simp only [hshift] at h
    rw [lintegral_mul_const _ (by fun_prop), lintegral_gauss_volume ht,
      ← ofReal_integral_eq_lintegral_ofReal (integrable_gauss_zero hμt (half_pos ht))
        (ae_of_all _ fun _ => (Real.exp_pos _).le), lintegral_gauss_volume (half_pos hs),
      ← ENNReal.ofReal_mul (Real.rpow_pos_of_pos (div_pos Real.pi_pos ht) _).le,
      ← ENNReal.ofReal_mul (integral_nonneg fun _ => (Real.exp_pos _).le)] at h
    have h2 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
      (integral_nonneg fun _ => (Real.exp_pos _).le) hPnn)).1 h
    rw [integral_gauss_homog hI (t / 2) (half_pos ht)] at h2
    simpa only [hP] using h2
  set p := ((d : ℝ) - alpha) / 2 with hp_def
  have hp : 0 < p := by rw [hp_def]; linarith
  set C := K1 * P / (2 : ℝ) ^ (-(alpha / 2)) with hC
  have bound : ∀ t : ℝ, 0 < t → 2 * t ≤ s → π ^ ((d : ℝ) / 2) * K ≤ C * t ^ p := by
    intro t ht hts
    have h := key t ht hts
    have htd : 0 < t ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos ht _
    rw [Real.div_rpow Real.pi_pos.le ht.le, Real.div_rpow ht.le (by norm_num)] at h
    have e1 : t ^ p = t ^ ((d : ℝ) / 2) * t ^ (-(alpha / 2)) := by
      rw [← Real.rpow_add ht, hp_def]
      congr 1
      ring
    calc π ^ ((d : ℝ) / 2) * K
        = t ^ ((d : ℝ) / 2) * (π ^ ((d : ℝ) / 2) / t ^ ((d : ℝ) / 2) * K) := by
          field_simp
      _ ≤ t ^ ((d : ℝ) / 2) * (t ^ (-(alpha / 2)) / 2 ^ (-(alpha / 2)) * K1 * P) :=
          mul_le_mul_of_nonneg_left h htd.le
      _ = C * t ^ p := by
          rw [e1, hC]
          ring
  have hlim : Tendsto (fun t : ℝ => C * t ^ p) (𝓝[>] 0) (𝓝 0) := by
    have h0 := ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [Real.zero_rpow hp.ne'] at h0
    simpa using h0.const_mul C
  have hpos : 0 < π ^ ((d : ℝ) / 2) * K :=
    mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) hKpos
  obtain ⟨t, h1, h2⟩ :=
    ((hlim.eventually (gt_mem_nhds hpos)).and (Ioo_mem_nhdsGT (half_pos hs))).exists
  have h3 := bound t h2.1 (by linarith [h2.2])
  linarith

/-- The in-domain specialization: for every covariance of the class of
`S:static-phase` (`PhaseCovariance`, main TeX lines 2490-2493 at edf7085f:
`d = 3`, `0 < α < 2`, `Γ(rA) = r^{3-α} Γ(A)`, `μ` the tempered spectral measure)
with `μ ≠ 0`, and every `s > 0`, the map `q ↦ ∫ e^{-s|q+ξ|²} μ(dξ)` is not
constant.  The homogeneity of `μ` is `spectralHomogeneous_of_scaling`.  Fields
of `PhaseCovariance` used: `alpha_lt_two`, `μ_radon`, `μ_tempered`, `spectral`,
`scaling`; carried but unused (checked through every lemma called):
`alpha_pos`, `Γ_radon`, `Γ_even`, `Γ_tempered`, `Γ_posdef`, `μ_even`.  The
hypothesis `μ ≠ 0` is added (it is necessary, see `phaseCovariance_zero`). -/
theorem not_gauss_shift_invariant_phase {alpha : ℝ} {Γ μ : Measure (Rd 3)}
    (h : PhaseCovariance alpha Γ μ) (hμ : μ ≠ 0) {s : ℝ} (hs : 0 < s) :
    ¬ ∀ q : Rd 3, ∫ ξ, Real.exp (-(s * ‖q + ξ‖ ^ 2)) ∂μ =
      ∫ ξ, Real.exp (-(s * ‖ξ‖ ^ 2)) ∂μ := by
  have := h.μ_radon
  have h2 := h.alpha_lt_two
  exact not_gauss_shift_invariant h.μ_tempered
    (spectralHomogeneous_of_scaling h.μ_tempered h.spectral h.scaling')
    (by push_cast; linarith) hμ hs

/-- In the class of `S:static-phase` with `μ ≠ 0`, the pairing inequality of
`gauss_shift_le` is strict at some nonzero shift, for every `s > 0`. -/
theorem exists_gauss_shift_lt_phase {alpha : ℝ} {Γ μ : Measure (Rd 3)}
    (h : PhaseCovariance alpha Γ μ) (hμ : μ ≠ 0) {s : ℝ} (hs : 0 < s) :
    ∃ q : Rd 3, q ≠ 0 ∧ ∫ ξ, Real.exp (-(s * ‖q + ξ‖ ^ 2)) ∂μ <
      ∫ ξ, Real.exp (-(s * ‖ξ‖ ^ 2)) ∂μ := by
  have hn := not_gauss_shift_invariant_phase h hμ hs
  push Not at hn
  obtain ⟨q, hq⟩ := hn
  refine ⟨q, ?_, lt_of_le_of_ne (gauss_shift_le h.spectral s hs q) hq⟩
  rintro rfl
  simp at hq

/-- The zero pair `Γ = 0`, `μ = 0` belongs to the class of `S:static-phase` for
every `0 < α < 2`; for it the shifted Gaussian masses are all `0`, so the
hypothesis `μ ≠ 0` of `not_gauss_shift_invariant_phase` cannot be dropped. -/
theorem phaseCovariance_zero {alpha : ℝ} (ha0 : 0 < alpha) (ha2 : alpha < 2) :
    PhaseCovariance alpha (0 : Measure (Rd 3)) 0 where
  alpha_pos := ha0
  alpha_lt_two := ha2
  Γ_radon := inferInstance
  Γ_even := by simp [IsEven]
  Γ_tempered := ⟨0, by simp⟩
  Γ_posdef := fun φ => by simp
  μ_radon := inferInstance
  μ_even := by simp [IsEven]
  μ_tempered := ⟨0, by simp⟩
  spectral := fun φ => by simp
  scaling := fun A _ c _ => by simp

end StratonovichHAMSecondMoment.PhaseShiftControl
