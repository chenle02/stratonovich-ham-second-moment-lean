module

/-
Copyright 2026 Le Chen. SPDX-License-Identifier: Apache-2.0

Spectral homogeneity under `H:homog`, from the main TeX file
`notes/notes_stratonovich_ham_second_moment.tex` (revision a284420): the
first paragraph of the proof of `L:damped-homogeneous-norms` (lines 851-860)
and the facts about `h_Γ` and `R_Γ` stated before
`P:clock-copy-obstruction` (lines 7715-7724); the same derivation appears in the proof of
`L:low-alpha-convolution` (lines 4718-4722).

Supplied input (the only one of this slice):
* `SpectralHomogeneous μ α`: `μ(cA) = c^α μ(A)` for Borel `A` and `c > 0`.
  The manuscript derives it in the proof of `L:damped-homogeneous-norms`
  (lines 851-852: "Scaling the Fourier representation of `Γ` and using Fourier
  uniqueness gives `μ(cA) = c^α μ(A)`").  It is exactly that sentence's
  conclusion, so it is no stronger than the manuscript.  (The package's
  `HomogHypothesis.HomogCovariance` records the scaling of `Γ`; the Fourier
  uniqueness step from it to `μ` is not formalized.)

Proved here from that input, local finiteness of `μ` and `0 < α < 2`:
* `μ{0} = 0` and `μ(B_r) = r^α μ(B_1)` (lines 852-854);
* `∫ (1+|ξ|²)⁻¹ μ(dξ) < ∞` (the finiteness at lines 856-858), by the layer-cake
  formula instead of the manuscript's polar formula (proof-route
  difference, same conclusion);
* the scaling `∫ f(cξ) μ(dξ) = c^{-α} ∫ f dμ`, and from it
  `R_Γ(q) = q^{α-2} R_Γ(1)` and `h_Γ(w) = w^{-α/2} h_Γ(1)` (lines 7723-7724);
* finiteness of `R_Γ(q)` and `h_Γ(w)` for `q, w > 0`, and their positivity
  when `μ ≠ 0` (line 7722), and `R_Γ(q) > R_Γ(q')` for `0 < q < q'`.

Proved without the input: `Γ ≠ 0 ⇒ μ ≠ 0` for a locally finite `Γ` with
spectral measure `μ` in the sense of `HomogHypothesis.IsSpectralMeasure`
(`spectral_ne_zero`), by testing against smooth compactly supported bumps.

The general radial formula `∫ f(|ξ|) μ(dξ) = αV ∫ f(r) r^{α-1} dr` is not
needed for `P:clock-copy-obstruction` and is not formalized.
-/

public import Mathlib
public import StratonovichHAMSecondMoment.HomogHypothesis
public import StratonovichHAMSecondMoment.TimeFractional

@[expose] public section

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Real Filter Metric
open scoped ENNReal Pointwise

namespace StratonovichHAMSecondMoment.SpectralHomog

open HomogHypothesis

/-- The supplied input `μ(cA) = c^α μ(A)` (proof of
`L:damped-homogeneous-norms`, lines 851-852). -/
def SpectralHomogeneous {d : ℕ} (μ : Measure (Rd d)) (alpha : ℝ) : Prop :=
  ∀ A : Set (Rd d), MeasurableSet A → ∀ c : ℝ, 0 < c →
    μ (c • A) = ENNReal.ofReal (c ^ alpha) * μ A

variable {d : ℕ} {μ : Measure (Rd d)} {alpha : ℝ}

/-- Pushforward form of the homogeneity: `μ ∘ (c·)⁻¹ = c^{-α} μ`. -/
theorem map_smul_eq (hI : SpectralHomogeneous μ alpha) (c : ℝ) (hc : 0 < c) :
    μ.map (fun ξ => c • ξ) = ENNReal.ofReal (c ^ (-alpha)) • μ := by
  ext A hA
  rw [Measure.map_apply (measurable_const_smul c) hA, Set.preimage_smul₀ hc.ne',
    hI A hA c⁻¹ (inv_pos.2 hc), Measure.smul_apply, smul_eq_mul, Real.inv_rpow hc.le,
    Real.rpow_neg hc.le]

/-- Scaling of integrals: `∫ f(cξ) μ(dξ) = c^{-α} ∫ f dμ` (`c > 0`). -/
theorem integral_comp_smul (hI : SpectralHomogeneous μ alpha) (c : ℝ) (hc : 0 < c)
    (f : Rd d → ℝ) (hf : Measurable f) :
    ∫ ξ, f (c • ξ) ∂μ = c ^ (-alpha) * ∫ ξ, f ξ ∂μ := by
  rw [← integral_map (measurable_const_smul c).aemeasurable hf.aestronglyMeasurable,
    map_smul_eq hI c hc, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul]

/-- `μ(B_r) = r^α μ(B_1)` for `r > 0` (line 853). -/
theorem measure_ball (hI : SpectralHomogeneous μ alpha) (r : ℝ) (hr : 0 < r) :
    μ (ball 0 r) = ENNReal.ofReal (r ^ alpha) * μ (ball 0 1) := by
  have h := smul_unitBall (E := Rd d) (c := r) hr.ne'
  rw [Real.norm_eq_abs, abs_of_pos hr] at h
  rw [← h, hI _ measurableSet_ball r hr]

/-- `μ{0} = 0` (lines 852-853: Radon finiteness and `α > 0`). -/
theorem measure_zero (hI : SpectralHomogeneous μ alpha) [IsLocallyFiniteMeasure μ]
    (ha : 0 < alpha) : μ {0} = 0 := by
  have h := hI {0} (measurableSet_singleton 0) 2 two_pos
  rw [Set.smul_set_singleton, smul_zero] at h
  have hfin : μ {0} ≠ ⊤ := isCompact_singleton.measure_lt_top.ne
  have h2 : 1 < (2 : ℝ) ^ alpha := Real.one_lt_rpow (by norm_num) ha
  have ht := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at ht
  have h0 : (μ {0}).toReal = 0 := by nlinarith [ENNReal.toReal_nonneg (a := μ {0})]
  rcases (ENNReal.toReal_eq_zero_iff _).1 h0 with h0 | h0
  · exact h0
  · exact absurd h0 hfin

/-- Auxiliary to the Lean proof route. Integrability from the bound `K (1+|ξ|²)⁻¹` once
`(1+|ξ|²)⁻¹` is
integrable. -/
theorem integrable_of_le_inv (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    {g : Rd d → ℝ} (hg : AEStronglyMeasurable g μ) (K : ℝ)
    (hb : ∀ ξ, ‖g ξ‖ ≤ K * (1 / (1 + ‖ξ‖ ^ 2))) : Integrable g μ :=
  Integrable.mono' (hR.const_mul K) hg (Eventually.of_forall hb)

/-- Finiteness of `∫ (1+|ξ|²)⁻¹ dμ` from the homogeneity, local finiteness and
`α < 2`, by the layer-cake formula. -/
theorem integrable_inv_one_add_sq (hI : SpectralHomogeneous μ alpha)
    [IsLocallyFiniteMeasure μ] (ha2 : alpha < 2) :
    Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ := by
  set f : Rd d → ℝ := fun ξ => 1 / (1 + ‖ξ‖ ^ 2) with hf_def
  have hfm : Measurable f := by rw [hf_def]; fun_prop
  have hf0 : ∀ ξ, 0 ≤ f ξ := fun ξ => by rw [hf_def]; positivity
  refine ⟨hfm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall hf0)).2 ?_⟩
  rw [lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall hf0) hfm.aemeasurable]
  set V := μ (ball (0 : Rd d) 1)
  have hV : V < ⊤ := measure_ball_lt_top
  -- the level sets
  have hbound : ∀ t ∈ Ioi (0 : ℝ), μ {ξ | t < f ξ} ≤
      (Iio (1 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ (-(alpha / 2))) * V) t := by
    intro t ht
    have ht0 : 0 < t := ht
    by_cases ht1 : t < 1
    · rw [indicator_of_mem (show t ∈ Iio (1 : ℝ) from ht1)]
      have hsub : {ξ | t < f ξ} ⊆ ball (0 : Rd d) (t ^ (-(1 / 2 : ℝ))) := by
        intro ξ hξ
        simp only [mem_ofPred_eq, hf_def] at hξ
        rw [mem_ball_zero_iff]
        have hpos : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
        have h1 : t * (1 + ‖ξ‖ ^ 2) < 1 := by
          rwa [lt_div_iff₀ hpos] at hξ
        have h2 : ‖ξ‖ ^ 2 < t⁻¹ := by
          rw [← one_div, lt_div_iff₀ ht0]
          nlinarith [sq_nonneg ‖ξ‖]
        have h3 : t ^ (-(1 / 2 : ℝ)) = Real.sqrt t⁻¹ := by
          rw [Real.sqrt_eq_rpow, Real.inv_rpow ht0.le, Real.rpow_neg ht0.le]
        rw [h3]
        exact Real.lt_sqrt (norm_nonneg _) |>.2 h2
      calc μ {ξ | t < f ξ} ≤ μ (ball (0 : Rd d) (t ^ (-(1 / 2 : ℝ)))) := measure_mono hsub
        _ = ENNReal.ofReal ((t ^ (-(1 / 2 : ℝ))) ^ alpha) * V :=
          measure_ball hI _ (Real.rpow_pos_of_pos ht0 _)
        _ = ENNReal.ofReal (t ^ (-(alpha / 2))) * V := by
          rw [← Real.rpow_mul ht0.le]
          congr 3
          ring
    · rw [indicator_of_notMem (show t ∉ Iio (1 : ℝ) from ht1)]
      have hempty : {ξ | t < f ξ} = ∅ := by
        ext ξ
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt, hf_def]
        rw [div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg ‖ξ‖]
      rw [hempty, measure_empty]
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi hbound) ?_
  rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have hset : Iio (1 : ℝ) ∩ Ioi 0 = Ioo 0 1 := by
    ext t; simp [and_comm]
  rw [hset]
  simp_rw [mul_comm _ V]
  rw [lintegral_const_mul _ (by fun_prop)]
  refine ENNReal.mul_lt_top hV ?_
  have hint : IntegrableOn (fun t : ℝ => t ^ (-(alpha / 2))) (Ioo 0 1) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  exact hint.lintegral_lt_top

/-! ### The resolvent `R_Γ` and the heat mass `h_Γ` -/

/-- `R_Γ(q) = ∫ μ(dξ)/(q²+|ξ|²)` (line 7720). -/
def resolvent (μ : Measure (Rd d)) (q : ℝ) : ℝ := ∫ ξ, 1 / (q ^ 2 + ‖ξ‖ ^ 2) ∂μ

/-- `h_Γ(w) = ∫ e^{-w|ξ|²/2} μ(dξ)` (line 7718). -/
def heat (μ : Measure (Rd d)) (w : ℝ) : ℝ := ∫ ξ, Real.exp (-(w * ‖ξ‖ ^ 2 / 2)) ∂μ

/-- Auxiliary to the Lean proof route. -/
theorem resolvent_integrable (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    (q : ℝ) (hq : q ≠ 0) : Integrable (fun ξ : Rd d => 1 / (q ^ 2 + ‖ξ‖ ^ 2)) μ := by
  have hq2 : 0 < q ^ 2 := by positivity
  refine integrable_of_le_inv hR
    (by fun_prop : Measurable fun ξ : Rd d => 1 / (q ^ 2 + ‖ξ‖ ^ 2)).aestronglyMeasurable
    (max 1 (1 / q ^ 2)) fun ξ => ?_
  have hp : 0 < q ^ 2 + ‖ξ‖ ^ 2 := by positivity
  have hp1 : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have h1 := le_max_left 1 (1 / q ^ 2)
  have h2 : 1 ≤ max 1 (1 / q ^ 2) * q ^ 2 := by
    have := mul_le_mul_of_nonneg_right (le_max_right 1 (1 / q ^ 2)) hq2.le
    rwa [one_div_mul_cancel hq2.ne'] at this
  rw [Real.norm_of_nonneg (by positivity), mul_one_div, div_le_div_iff₀ hp hp1, one_mul]
  nlinarith [sq_nonneg ‖ξ‖]

/-- Auxiliary to the Lean proof route. -/
theorem heat_integrable (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    (w : ℝ) (hw : 0 < w) :
    Integrable (fun ξ : Rd d => Real.exp (-(w * ‖ξ‖ ^ 2 / 2))) μ := by
  refine integrable_of_le_inv hR
    (by fun_prop : Measurable fun ξ : Rd d =>
      Real.exp (-(w * ‖ξ‖ ^ 2 / 2))).aestronglyMeasurable
    (max 1 (2 / w)) fun ξ => ?_
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have hx : 0 ≤ w * ‖ξ‖ ^ 2 / 2 := by positivity
  have he : Real.exp (-(w * ‖ξ‖ ^ 2 / 2)) * (1 + w * ‖ξ‖ ^ 2 / 2) ≤ 1 := by
    have h1 := Real.add_one_le_exp (w * ‖ξ‖ ^ 2 / 2)
    have h2 : Real.exp (-(w * ‖ξ‖ ^ 2 / 2)) * Real.exp (w * ‖ξ‖ ^ 2 / 2) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-(w * ‖ξ‖ ^ 2 / 2))]
  have hK : 1 + ‖ξ‖ ^ 2 ≤ max 1 (2 / w) * (1 + w * ‖ξ‖ ^ 2 / 2) := by
    have h1 := le_max_left 1 (2 / w)
    have h2 := le_max_right 1 (2 / w)
    have h3 : 2 / w * (w / 2) = 1 := by field_simp
    nlinarith [sq_nonneg ‖ξ‖,
      mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ w / 2 * ‖ξ‖ ^ 2)]
  have hp1 : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  rw [mul_one_div, le_div_iff₀ hp1]
  calc Real.exp (-(w * ‖ξ‖ ^ 2 / 2)) * (1 + ‖ξ‖ ^ 2)
      ≤ Real.exp (-(w * ‖ξ‖ ^ 2 / 2)) * (max 1 (2 / w) * (1 + w * ‖ξ‖ ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hK (Real.exp_pos _).le
    _ = max 1 (2 / w) * (Real.exp (-(w * ‖ξ‖ ^ 2 / 2)) * (1 + w * ‖ξ‖ ^ 2 / 2)) := by ring
    _ ≤ max 1 (2 / w) * 1 := mul_le_mul_of_nonneg_left he (by positivity)
    _ = max 1 (2 / w) := mul_one _

/-- `R_Γ(q) = q^{α-2} R_Γ(1)` for `q > 0` (line 7724). -/
theorem resolvent_homog (hI : SpectralHomogeneous μ alpha) (q : ℝ) (hq : 0 < q) :
    resolvent μ q = q ^ (alpha - 2) * resolvent μ 1 := by
  have h := integral_comp_smul hI q⁻¹ (inv_pos.2 hq) (fun ξ => 1 / (1 + ‖ξ‖ ^ 2))
    (by fun_prop)
  have hpt : ∀ ξ : Rd d,
      1 / (1 + ‖q⁻¹ • ξ‖ ^ 2) = q ^ 2 * (1 / (q ^ 2 + ‖ξ‖ ^ 2)) := by
    intro ξ
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hq]
    have : 0 < q ^ 2 + ‖ξ‖ ^ 2 := by positivity
    field_simp
  simp only [hpt] at h
  rw [integral_const_mul, Real.inv_rpow hq.le, Real.rpow_neg (by positivity), inv_inv] at h
  unfold resolvent
  simp only [one_pow]
  rw [Real.rpow_sub hq, Real.rpow_two]
  field_simp
  linarith

/-- `h_Γ(w) = w^{-α/2} h_Γ(1)` for `w > 0` (line 7723). -/
theorem heat_homog (hI : SpectralHomogeneous μ alpha) (w : ℝ) (hw : 0 < w) :
    heat μ w = w ^ (-(alpha / 2)) * heat μ 1 := by
  have hs : 0 < Real.sqrt w := Real.sqrt_pos.2 hw
  have h := integral_comp_smul hI (Real.sqrt w) hs (fun ξ => Real.exp (-(1 * ‖ξ‖ ^ 2 / 2)))
    (by fun_prop)
  have hpt : ∀ ξ : Rd d, Real.exp (-(1 * ‖Real.sqrt w • ξ‖ ^ 2 / 2)) =
      Real.exp (-(w * ‖ξ‖ ^ 2 / 2)) := by
    intro ξ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow, Real.sq_sqrt hw.le, one_mul]
  simp only [hpt] at h
  unfold heat
  rw [h, Real.sqrt_eq_rpow, ← Real.rpow_mul hw.le]
  congr 2
  ring

/-- `R_Γ(q) - R_Γ(q') > 0` for `0 < q < q'` when `μ ≠ 0`. -/
theorem resolvent_sub_pos (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    (hμ : μ ≠ 0) (q q' : ℝ) (hq : 0 < q) (hqq : q < q') :
    0 < resolvent μ q - resolvent μ q' := by
  unfold resolvent
  have h1 := resolvent_integrable hR q hq.ne'
  have h2 := resolvent_integrable hR q' (by linarith)
  rw [← integral_sub h1 h2]
  refine TimeFractional.integral_pos_of_ae_pos (h1.sub h2) hμ (Eventually.of_forall fun ξ => ?_)
  have ha : 0 < q ^ 2 + ‖ξ‖ ^ 2 := by positivity
  have hb : q ^ 2 + ‖ξ‖ ^ 2 < q' ^ 2 + ‖ξ‖ ^ 2 := by nlinarith
  simp only [sub_pos]
  exact one_div_lt_one_div_of_lt ha hb

/-- Auxiliary to the Lean proof route. -/
theorem resolvent_pos (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    (hμ : μ ≠ 0) (q : ℝ) (hq : q ≠ 0) : 0 < resolvent μ q :=
  TimeFractional.integral_pos_of_ae_pos (resolvent_integrable hR q hq) hμ
    (Eventually.of_forall fun ξ => one_div_pos.2
      (add_pos_of_pos_of_nonneg (by positivity) (by positivity)))

/-- Auxiliary to the Lean proof route. -/
theorem heat_pos (hR : Integrable (fun ξ : Rd d => 1 / (1 + ‖ξ‖ ^ 2)) μ)
    (hμ : μ ≠ 0) (w : ℝ) (hw : 0 < w) : 0 < heat μ w :=
  TimeFractional.integral_pos_of_ae_pos (heat_integrable hR w hw) hμ
    (Eventually.of_forall fun _ => Real.exp_pos _)

/-! ### `Γ ≠ 0` gives `μ ≠ 0` -/

/-- A nonzero locally finite covariance has a nonzero spectral measure. -/
theorem spectral_ne_zero (Γ μ : Measure (Rd d)) [IsLocallyFiniteMeasure Γ]
    (hsp : IsSpectralMeasure Γ μ) (hΓ : Γ ≠ 0) : μ ≠ 0 := by
  intro hμ
  apply hΓ
  have hball : ∀ n : ℕ, Γ (closedBall (0 : Rd d) ((n : ℝ) + 1)) = 0 := by
    intro n
    let b : ContDiffBump (0 : Rd d) :=
      ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
    have hsupp : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
      b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) Complex.ofReal_zero
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((b x : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp b.contDiff
    have h := hsp (hsupp.toSchwartzMap hsmooth)
    simp only [HasCompactSupport.toSchwartzMap_toFun, hμ, integral_zero_measure,
      integral_complex_ofReal, Complex.ofReal_eq_zero] at h
    have hint : Integrable (fun x => b x) Γ :=
      b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => b.nonneg) hint).1 h
    refine measure_mono_null (fun x hx => ?_) (measure_eq_zero_iff_ae_notMem.2
      (hae.mono fun x hx => ?_ : ∀ᵐ x ∂Γ, x ∉ {x | b x ≠ 0}))
    · exact (show b x ≠ 0 by rw [b.one_of_mem_closedBall hx]; exact one_ne_zero)
    · simpa using hx
  have huniv : (univ : Set (Rd d)) = ⋃ n : ℕ, closedBall (0 : Rd d) ((n : ℝ) + 1) := by
    refine (eq_univ_of_forall fun x => ?_).symm
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact mem_iUnion.2 ⟨n, mem_closedBall_zero_iff.2 (by linarith)⟩
  rw [← Measure.measure_univ_eq_zero, huniv]
  exact measure_iUnion_null hball

end StratonovichHAMSecondMoment.SpectralHomog
